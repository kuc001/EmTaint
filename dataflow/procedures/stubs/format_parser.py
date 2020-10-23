from string import digits as ascii_digits
import logging
import math
import claripy

from angr import sim_type
from angr.storage.file import SimPackets
from ...sim_procedure import SimProcedure
from ...parse_ast import BVV, get_mem_permission, get_value, get_scope, is_str_pointer_v2
from dataflow.data_collector import weaks_command_exec


l = logging.getLogger(name=__name__)
ascii_digits = ascii_digits.encode()

class FormatString(object):
    """
    Describes a format string.
    """

    SCANF_DELIMITERS = [b"\x09", b"\x0a", b"\x0b", b"\x0d", b"\x20"]

    def __init__(self, parser, components):
        """
        Takes a list of components which are either just strings or a FormatSpecifier.
        """
        self.components = components
        self.parser = parser
        self.string = None

    @property
    def state(self):
        return self.parser.state

    @staticmethod
    def _add_to_string(string, c):
        if c is None:
            return string
        if string is None:
            return c
        return string.concat(c)

    def _get_str_at(self, str_addr):

        strlen = self.parser._sim_strlen(str_addr)

        #TODO: we probably could do something more fine-grained here.

        # throw away strings which are just the NULL terminator
        if self.parser.state.solver.max_int(strlen) == 0:
            return None
        return self.parser.state.memory.load(str_addr, strlen)

    def replace(self, startpos, args):
        """
        Implement printf - based on the stored format specifier information, format the values from the arg getter function `args` into a string.

        :param startpos:        The index of the first argument to be used by the first element of the format string
        :param args:            A function which, given an argument index, returns the integer argument to the current function at that index
        :return:                The result formatted string
        """

        argpos = startpos
        string = None

        for component in self.components:
            # if this is just concrete data
            if isinstance(component, bytes):
                string = self._add_to_string(string, self.parser.state.solver.BVV(component))
            elif isinstance(component, str):
                raise Exception("this branch should be impossible?")
            elif isinstance(component, claripy.ast.BV):
                string = self._add_to_string(string, component)
            else:
                # okay now for the interesting stuff
                # what type of format specifier is it?
                fmt_spec = component
                if fmt_spec.spec_type == b's':
                    str_ptr = args(argpos)
                    string = self._add_to_string(string, self._get_str_at(str_ptr))
                # integers, for most of these we'll end up concretizing values..
                else:
                    i_val = args(argpos)
                    c_val = int(self.parser.state.solver.eval(i_val))
                    c_val &= (1 << (fmt_spec.size * 8)) - 1
                    if fmt_spec.signed and (c_val & (1 << ((fmt_spec.size * 8) - 1))):
                        c_val -= (1 << fmt_spec.size * 8)

                    if fmt_spec.spec_type in (b'd', b'i'):
                        s_val = str(c_val)
                    elif fmt_spec.spec_type == b'u':
                        s_val = str(c_val)
                    elif fmt_spec.spec_type == b'c':
                        s_val = chr(c_val & 0xff)
                    elif fmt_spec.spec_type == b'x':
                        s_val = hex(c_val)[2:]
                    elif fmt_spec.spec_type == b'o':
                        s_val = oct(c_val)[2:]
                    elif fmt_spec.spec_type == b'p':
                        s_val = hex(c_val)
                    else:
                        raise SimProcedureError("Unimplemented format specifier '%s'" % fmt_spec.spec_type)

                    string = self._add_to_string(string, self.parser.state.solver.BVV(s_val.encode()))

                argpos += 1

        return string

    def interpret(self, startpos, args, addr=None, simfd=None):
        """
        implement scanf - extract formatted data from memory or a file according to the stored format
        specifiers and store them into the pointers extracted from `args`.

        :param startpos:    The index of the first argument corresponding to the first format element
        :param args:        A function which, given the index of an argument to the function, returns that argument
        :param addr:        The address in the memory to extract data from, or...
        :param simfd:       A file descriptor to use for reading data from
        :return:            The number of arguments parsed
        """
        if simfd is not None and isinstance(simfd.read_storage, SimPackets):
            argnum = startpos
            for component in self.components:
                if type(component) is bytes:
                    sdata, _ = simfd.read_data(len(component), short_reads=False)
                    self.state.solver.add(sdata == component)
                elif isinstance(component, claripy.Bits):
                    sdata, _ = simfd.read_data(len(component) // 8, short_reads=False)
                    self.state.solver.add(sdata == component)
                elif component.spec_type == b's':
                    if component.length_spec is None:
                        sdata, slen = simfd.read_data(self.state.libc.buf_symbolic_bytes)
                    else:
                        sdata, slen = simfd.read_data(component.length_spec)
                    for byte in sdata.chop(8):
                        self.state.solver.add(claripy.And(*[byte != char for char in self.SCANF_DELIMITERS]))
                    self.state.memory.store(args(argnum), sdata, size=slen)
                    self.state.memory.store(args(argnum) + slen, claripy.BVV(0, 8))
                    argnum += 1
                elif component.spec_type == b'c':
                    sdata, _ = simfd.read_data(1, short_reads=False)
                    self.state.memory.store(args(argnum), sdata)
                    argnum += 1
                else:
                    bits = component.size * 8
                    if component.spec_type == b'x':
                        base = 16
                    elif component.spec_type == b'o':
                        base = 8
                    else:
                        base = 10

                    # here's the variable representing the result of the parsing
                    target_variable = self.state.solver.BVS('scanf_' + component.string.decode(), bits,
                            key=('api', 'scanf', argnum - startpos, component.string))
                    negative = claripy.SLT(target_variable, 0)

                    # how many digits does it take to represent this variable fully?
                    max_digits = int(math.ceil(math.log(2**bits, base)))

                    # how many digits does the format specify?
                    spec_digits = component.length_spec

                    # how many bits can we specify as input?
                    available_bits = float('inf') if spec_digits is None else spec_digits * math.log(base, 2)
                    not_enough_bits = available_bits < bits

                    # how many digits will we model this input as?
                    digits = max_digits if spec_digits is None else spec_digits

                    # constrain target variable range explicitly if it can't take on all possible values
                    if not_enough_bits:
                        self.state.solver.add(self.state.solver.And(
                            self.state.solver.SLE(target_variable, (base**digits) - 1),
                            self.state.solver.SGE(target_variable, -(base**(digits - 1) - 1))))

                    # perform the parsing in reverse - constrain the input digits to be the string version of the input
                    # this only works because we're reading from a packet stream and therefore nobody has the ability
                    # to add other constraints to this data!
                    # this makes z3's job EXTREMELY easy
                    sdata, _ = simfd.read_data(digits, short_reads=False)
                    for i, digit in enumerate(reversed(sdata.chop(8))):
                        digit_value = (target_variable // (base**i)) % base
                        digit_ascii = digit_value + ord('0')
                        if base > 10:
                            digit_ascii = claripy.If(digit_value >= 10, digit_value + (-10 + ord('a')), digit_ascii)

                        # if there aren't enough bits, we can increase the range by accounting for the possibility that
                        # the first digit is a minus sign
                        if not_enough_bits:
                            if i == digits - 1:
                                neg_digit_ascii = ord('-')
                            else:
                                neg_digit_value = (-target_variable // (base**i)) % base
                                neg_digit_ascii = neg_digit_value + ord('0')
                                if base > 10:
                                    neg_digit_ascii = claripy.If(neg_digit_value >= 10, neg_digit_value + (-10 + ord('a')), neg_digit_ascii)

                            digit_ascii = claripy.If(negative, neg_digit_ascii, digit_ascii)

                        self.state.solver.add(digit == digit_ascii[7:0])

                    self.state.memory.store(args(argnum), target_variable, endness=self.state.arch.memory_endness)
                    argnum += 1

            return argnum - startpos

        # TODO: we only support one format specifier in interpretation for now

        format_specifier_count = sum(1 for x in self.components if isinstance(x, FormatSpecifier))
        if format_specifier_count > 1:
            l.warning("We don't support more than one format specifiers in format strings.")

        if simfd is not None:
            region = simfd.read_storage
            addr = simfd._pos if hasattr(simfd, '_pos') else simfd._read_pos # XXX THIS IS BAD
        else:
            region = self.parser.state.memory

        bits = self.parser.state.arch.bits
        failed = self.parser.state.solver.BVV(0, bits)
        argpos = startpos
        position = addr
        for component in self.components:
            if isinstance(component, bytes):
                # TODO we skip non-format-specifiers in format string interpretation for now
                # if the region doesn't match the concrete component, we need to return immediately
                pass
            else:
                fmt_spec = component
                try:
                    dest = args(argpos)
                except SimProcedureArgumentError:
                    dest = None
                if fmt_spec.spec_type == b's':
                    # set some limits for the find
                    max_str_len = self.parser.state.libc.max_str_len
                    max_sym_bytes = self.parser.state.libc.buf_symbolic_bytes

                    # has the length of the format been limited by the string itself?
                    if fmt_spec.length_spec is not None:
                        max_str_len = fmt_spec.length_spec
                        max_sym_bytes = fmt_spec.length_spec

                    # TODO: look for limits on other characters which scanf is sensitive to, '\x00', '\x20'
                    ohr, ohc, ohi = region.find(position, self.parser.state.solver.BVV(b'\n'), max_str_len, max_symbolic_bytes=max_sym_bytes)

                    # if no newline is found, mm is position + max_strlen
                    # If-branch will really only happen for format specifiers with a length
                    mm = self.parser.state.solver.If(ohr == 0, position + max_str_len, ohr)
                    # we're just going to concretize the length, load will do this anyways
                    length = self.parser.state.solver.max_int(mm - position)
                    src_str = region.load(position, length)

                    # TODO all of these should be delimiters we search for above
                    # add that the contents of the string cannot be any scanf %s string delimiters
                    for delimiter in set(FormatString.SCANF_DELIMITERS):
                        delim_bvv = self.parser.state.solver.BVV(delimiter)
                        for i in range(length):
                            self.parser.state.add_constraints(region.load(position + i, 1) != delim_bvv)

                    # write it out to the pointer
                    self.parser.state.memory.store(dest, src_str)
                    # store the terminating null byte
                    self.parser.state.memory.store(dest + length, self.parser.state.solver.BVV(0, 8))

                    position += length

                else:

                    # XXX: atoi only supports strings of one byte
                    if fmt_spec.spec_type in [b'd', b'i', b'u', b'x']:
                        base = 16 if fmt_spec.spec_type == b'x' else 10
                        status, i, num_bytes = self.parser._sim_atoi_inner(position, region, base=base, read_length=fmt_spec.length_spec)
                        # increase failed count if we were unable to parse it
                        failed = self.parser.state.solver.If(status, failed, failed + 1)
                        position += num_bytes
                    elif fmt_spec.spec_type == b'c':
                        i = region.load(position, 1)
                        i = i.zero_extend(bits - 8)
                        position += 1
                    else:
                        raise SimProcedureError("unsupported format spec '%s' in interpret" % fmt_spec.spec_type)

                    i = self.parser.state.solver.Extract(fmt_spec.size*8-1, 0, i)
                    self.parser.state.memory.store(dest, i, size=fmt_spec.size, endness=self.parser.state.arch.memory_endness)

                argpos += 1

        if simfd is not None:
            simfd.read_data(position - addr)

        return (argpos - startpos) - failed

    def __repr__(self):
        outstr = ""
        for comp in self.components:
            outstr += (str(comp))

        return outstr

class FormatSpecifier(object):
    """
    Describes a format specifier within a format string.
    """

    def __init__(self, string, length_spec, size, signed):
        self.string = string
        self.size = size
        self.signed = signed
        self.length_spec = length_spec

    @property
    def spec_type(self):
        return self.string[-1:].lower()

    def __str__(self):
        return "%%%s" % self.string.decode()

    def __len__(self):
        return len(self.string)

class FormatParser(SimProcedure):
    """
    For SimProcedures relying on format strings.
    """

    ARGS_MISMATCH = True

    # Basic conversion specifiers for format strings, mapped to sim_types
    # TODO: support for C and S that are deprecated.
    # TODO: We only consider POSIX locales here.
    basic_spec = {
        b'd': 'int',
        b'i': 'int',
        b'o': 'unsigned int',
        b'u': 'unsigned int',
        b'x': 'unsigned int',
        b'X': 'unsigned int',
        b'e': 'double',
        b'E': 'double',
        b'f': 'double',
        b'F': 'double',
        b'g': 'double',
        b'G': 'double',
        b'a': 'double',
        b'A': 'double',
        b'c': 'char',
        b's': 'char*',
        b'p': 'uintptr_t',
        b'n': 'uintptr_t', # pointer to num bytes written so far
        #b'm': None, # Those don't expect any argument
        #b'%': None, # Those don't expect any argument
    }

    # Signedness of integers
    int_sign = {
        'signed': [b'd', b'i'],
        'unsigned' : [b'o', b'u', b'x', b'X']
    }

    # Length modifiers and how they apply to integer conversion (signed / unsigned).
    int_len_mod = {
        b'hh': ('char', 'uint8_t'),
        b'h' : ('int16_t', 'uint16_t'),
        b'l' : ('long', 'unsigned long'),
        # FIXME: long long is 64bit according to stdint.h on Linux,  but that might not always be the case
        b'll' : ('int64_t', 'uint64_t'),

        # FIXME: intmax_t seems to be always 64 bit, but not too sure
        b'j' : ('int64_t', 'uint64_t'),
        b'z' : ('ssize', 'size_t'),
        b't' : ('ptrdiff_t', 'ptrdiff_t'),
    }

    # Types that are not known by sim_types
    # Maps to (size, signedness)
    other_types = {
        ('string',): lambda _:(0, True) # special value for strings, we need to count
    }

    # Those flags affect the formatting the output string
    flags = ['#', '0', r'\-', r' ', r'\+', r'\'', 'I']

    @property
    def _mod_spec(self):
        """
        Modified length specifiers: mapping between length modifiers and conversion specifiers. This generates all the
        possibilities, i.e. hhd, etc.
        """
        mod_spec={}

        for mod, sizes in self.int_len_mod.items():

            for conv in self.int_sign['signed']:
                mod_spec[mod + conv] = sizes[0]

            for conv in self.int_sign['unsigned']:
                mod_spec[mod + conv] = sizes[1]

        return mod_spec

    @property
    def _all_spec(self):
        """
        All specifiers and their lengths.
        """

        base = self._mod_spec

        for spec in self.basic_spec:
            base[spec] = self.basic_spec[spec]

        return base

    # Tricky stuff
    # Note that $ is not C99 compliant (but posix specific).

    def _match_spec(self, nugget):
        """
        match the string `nugget` to a format specifier.
        """
        # TODO: handle positional modifiers and other similar format string tricks.
        all_spec = self._all_spec

        # iterate through nugget throwing away anything which is an int
        # TODO store this in a size variable

        original_nugget = nugget
        length_str = [ ]
        length_spec = None

        for j, c in enumerate(nugget):
            # print("match-spec: %s %s" % (j, c))
            if c in ascii_digits:
                length_str.append(c)
            else:
                nugget = nugget[j:]
                length_spec = None if len(length_str) == 0 else int(bytes(length_str))
                break

        # we need the length of the format's length specifier to extract the format and nothing else
        length_spec_str_len = 0 if length_spec is None else len(length_str)
        # is it an actual format?
        for spec in all_spec:
            if nugget.startswith(spec):
                # this is gross coz sim_type is gross..
                nugget = nugget[:len(spec)]
                original_nugget = original_nugget[:(length_spec_str_len + len(spec))]
                nugtype = all_spec[nugget]
                try:
                    typeobj = sim_type.parse_type(nugtype).with_arch(self.state.arch)
                except:
                    raise SimProcedureError("format specifier uses unknown type '%s'" % repr(nugtype))
                return FormatSpecifier(original_nugget, length_spec, typeobj.size // 8, typeobj.signed)

        return None

    def _match_spec_v2(self, index, fmt, fmt_len):
        """
        match the string `fmt` to a format specifier.
        """
        length_str = b''
        length_spec = None
        i = index

        while i < fmt_len:
            c = fmt[i]
            if c in ascii_digits:
                length_str += c
            else:
                length_spec = None if len(length_str) == 0 else int(bytes(length_str))
                # print(length_spec)
                break
            i += 1

        if i >= len(fmt):
            return None, None
        spec = fmt[i]
        # print("spec: %s" % (spec))
        if spec == b's':
            param = 's'
        elif spec in [b'[', b'{']:
            # sscanf's formats
            param = 's'
        elif spec == b'*':
            param = ''
        else:
            param = 'i'

        return param, length_spec

    def _find_fmt_parameters(self, fmt):
        """
        Extract the actual formats from the format string `fmt`.
        """
        args = []
        fmt_len = len(fmt)
        for i, c in enumerate(fmt):
            if type(c) is bytes and c == b"%":
                spec_type, length_spec = self._match_spec_v2(i+1, fmt, fmt_len)
                if spec_type:
                    args.append(spec_type)

        if len(args):
            self.block.format_args = args
            # print("%s has format-parm: %s" % (self.block, args))

    def _get_fmt_args(self, fmt):
        """
        Extract the actual formats from the format string `fmt`.

        :param list fmt: A list of format chars.
        :returns: a FormatString object
        """

        # iterate over the format string looking for format specifiers
        # components = [ ]
        args = []
        i = 0
        while i < len(fmt):
            if type(fmt[i]) is bytes and fmt[i] == b"%":
                # Note that we only support concrete format specifiers
                # grab the specifier
                # go to the space
                specifier = b""
                for c in fmt[i+1:]:
                    if type(c) is bytes:
                        specifier += c
                        # print("add-c: %s" % (c))
                    else:
                        break

                # print("specifier: %s" % (specifier))
                specifier = self._match_spec(specifier)
                # print(specifier)
                if specifier is not None:
                    i += len(specifier)
                    if specifier.spec_type == b's':
                        args.append('s')
                    else:
                        args.append('i')

                else:
                    # if we get here we didn't match any specs, the first char will be thrown away
                    # and we'll add the percent
                    if fmt[i+1] != b'*':
                        args.append('s')
                    i += 1
            i += 1

        if len(args):
            self.block.format_args = args

    def _get_fmt(self, fmt):
        """
        Extract the actual formats from the format string `fmt`.

        :param list fmt: A list of format chars.
        :returns: a FormatString object
        """

        # iterate over the format string looking for format specifiers
        components = [ ]
        i = 0
        while i < len(fmt):
            if type(fmt[i]) is bytes and fmt[i] == b"%":
                # Note that we only support concrete format specifiers
                # grab the specifier
                # go to the space
                specifier = b""
                for c in fmt[i+1:]:
                    if type(c) is bytes:
                        specifier += c
                    else:
                        break

                specifier = self._match_spec(specifier)
                if specifier is not None:
                    i += len(specifier)
                    components.append(specifier)
                else:
                    # if we get here we didn't match any specs, the first char will be thrown away
                    # and we'll add the percent
                    i += 1
                    components.append(b'%')
            else:
                # claripy ASTs, which are usually symbolic variables
                # They will be kept as they are - even if those chars can be evaluated to "%"
                components.append(fmt[i])
            i += 1

        return FormatString(self, components)

    def _sim_atoi_inner(self, str_addr, region, base=10, read_length=None):
        """
        Return the result of invoking the atoi simprocedure on `str_addr`.
        """

        from .. import SIM_PROCEDURES
        strtol = SIM_PROCEDURES['libc']['strtol']

        return strtol.strtol_inner(str_addr, self.state, region, base, True, read_length=read_length)


    def _sim_strlen(self, str_addr):
        """
        Return the result of invoking the strlen simprocedure on `str_addr`.
        """

        from .. import SIM_PROCEDURES
        strlen = SIM_PROCEDURES['libc']['strlen']

        return self.inline_call(strlen, str_addr).ret_expr

    def _get_format_arguments(self, args):
        """
        Get format argument's reg name and stack addr.
        """
        if args is None:
            return []
        arguments = []
        i = self.num_args
        for index, arg in enumerate(args):
            if arg != 's':
                continue

            index += i
            v = self.arg(index)
            if 'r' in v:
                arguments.append(v)
            elif 's' in v:
                stack_addr = self.get_stack_arg_ptr(v)
                if stack_addr:
                    # print("stack: %x" % (stack_addr))
                    arguments.append(stack_addr)

        return arguments

    def _find_taint_propagate_in_format_v1(self, s, args, constraint=None):
        """
        In sprintf (snprintf, etc.), find tiant propagate with arguments.
        """
        arguments = self._get_format_arguments(args)
        # if len(arguments) == 0:
        #     return 1

        ret_name = 'r%d' % (self.arch.ret_offset)

        def find_arg_taint(ast, trace_sims, arguments):
            if (ast.op == 'BVS' or is_str_pointer_v2(ast) or
                    (ast.op == 'Store' and ast.args[0].op == 'BVV')):
                for arg in arguments:
                    if arg in trace_sims:
                        return True
            return False

        new_exprs = []
        ret_killed_exprs = []
        ptr_killed_exprs = []

        for trace_expr in self.block.forward_exprs:
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if find_arg_taint(trace_ast, trace_sims, arguments):
                self.block.is_tainted = 2
                new_expr = trace_expr.replace(trace_ast, s, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.ptr_id = self.block.addr
                new_expr.expr.taint_live = self.block.addr
                new_exprs.append(new_expr)

            if trace_ast.op == 'BVS' and s in trace_sims:
                ptr_killed_exprs.append(trace_expr)
                dst_value = get_value(self.block, s)
                # print("Killed-%x %s with %s" % (self.block.addr, trace_expr, dst_value))
                if type(dst_value) is int and get_scope(dst_value) == 'global':
                    self.block.global_defs.add(dst_value)

            if ret_name in trace_sims:
                ret_killed_exprs.append(trace_expr)

        for kill_expr in ret_killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        if len(ptr_killed_exprs):
            self.kill_forward_exprs(ptr_killed_exprs)

        cons_values = []
        cons_expr = None
        if constraint:
            # print("Has-cons: %s" % (constraint))
            cons_values, cons_expr = self.get_constraint(constraint, 3)
            # print("Con- %s %s" % (cons_values, cons_expr))

        for pre_block in self.block.predecessors:
            for new_expr in new_exprs:
                if len(cons_values):
                    # new_expr.constraints.extend(cons_values)
                    for cons_v in cons_values:
                        if cons_v not in new_expr.constraints:
                            new_expr.constraints.append(cons_v)
                elif cons_expr is not None:
                    if 'S' not in new_expr.constraints:
                        new_expr.constraints.append('S')
                # print("format-taint: %x %s %s %x" % (self.block.addr, new_expr, new_expr.constraints, new_expr.expr.flag))
                new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                new_expr.expr.taint_loc = self.block.addr
                new_expr.expr.flag &= 0xeeff
                new_expr.taint_propagaton_level += 1
                pre_block.backward_exprs.append(new_expr)

    def _find_taint_propagate_in_format_v2(self, s, args, constrain=None):
        """
        In sscanf, find tiant propagate from taint parameter to other arguments.
        """
        arguments = self._get_format_arguments(args)
        if len(arguments) == 0:
            return 1

        # print("Format-taint with: %s" % (arguments))
        ret_name = 'r%d' % (self.arch.ret_offset)

        def get_taint_expr(ast, arg, trace_expr):
            if type(arg) is int:
                arg = claripy.Load(BVV(arg), ast.size())
                rep_info = {arg: 'ptr'}
                sim_action = trace_expr.create_sim_action(arg, var_type='ptr')
                re_sim_actions = {0: sim_action}
                new_expr = trace_expr.replace(ast, arg, rep_type='ptr', re_sim_actions=re_sim_actions, rep_info=rep_info)
            else:
                new_expr = trace_expr.replace(ast, arg, rep_type='ptr')
            new_expr.expr.trace_dir = 'B'
            return new_expr

        def check_ptr_redefine(ast, sims, arguments):
            for arg in arguments:
                if ast.op == 'BVS' and type(arg) is str and arg in sims:
                    return True

                elif (type(arg) is int and ast.op in ['Load', 'Store'] and
                        ast.args[0].op == 'BVV' and ast.args[0].args[0] == arg):
                    return True
            return False

        if self.flow_dir == 'F':
            new_exprs = []
            ret_killed_exprs = []
            ptr_killed_exprs = []

            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast

                if s in trace_sims and trace_ast.op == 'BVS':
                    for i, arg in enumerate(arguments):
                        self.block.is_tainted = 2
                        new_expr = get_taint_expr(trace_ast, arg, trace_expr)
                        new_expr.expr.ptr_id = self.block.addr + i
                        new_expr.expr.taint_live = self.block.addr
                        new_exprs.append(new_expr)

                kill_flag = check_ptr_redefine(trace_ast, trace_sims, arguments)
                if kill_flag:
                    ptr_killed_exprs.append(trace_expr)

                if ret_name in trace_sims:
                    ret_killed_exprs.append(trace_expr)

            for kill_expr in ret_killed_exprs:
                self.block.forward_exprs.remove(kill_expr)

            if len(ptr_killed_exprs):
                self.kill_forward_exprs(ptr_killed_exprs)

            for pre_block in self.block.predecessors:
                for new_expr in new_exprs:
                    # print("format-taint: %s" % (new_expr))
                    new_expr.expr.taint_loc = self.block.addr
                    new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                    new_expr.expr.flag &= 0xfeff
                    new_expr.taint_propagaton_level += 1
                    pre_block.backward_exprs.append(new_expr)

    def _find_taint_propagate_in_format_v3(self, args):
        """
        In _system, find tiant propagate to command.
        """
        arguments = self._get_format_arguments(args)
        if len(arguments) == 0:
            return 0

        ret_name = 'r%d' % (self.arch.ret_offset)

        def find_arg_taint(ast, trace_sims, arguments):
            if ast.op == 'BVS' or (ast.op == 'Store' and ast.args[0].op == 'BVV'):
                for arg in arguments:
                    if arg in trace_sims:
                        return True
            return False

        if self.flow_dir == 'F':
            new_exprs = []
            killed_exprs = []
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast
                flag = trace_expr.expr.flag

                if flag & 0x100 and find_arg_taint(trace_ast, trace_sims, arguments):
                    self.block.is_tainted = 2
                    # if trace_expr not in weaks_command_exec[self.block.addr]:
                    weaks_command_exec[self.block.addr].append(trace_expr)

    def _find_taint_propagate_in_format_v4(self, s, arg_list, args, constraint=None):
        """
        In vsprintf (vsnprintf, etc.), find tiant propagate with arguments.
        """
        ret_name = 'r%d' % (self.arch.ret_offset)

        def find_arg_taint(ast, trace_sims, arg_list, arguments):
            if ast.op != 'Store' or arg_list not in ast.variables:
                return False
            offset = None
            format_arg_ptr = ast.args[0]
            if format_arg_ptr.op == 'BVS':
                offset = 0
            elif format_arg_ptr.op == '__add__' and len(format_arg_ptr.args) == 2:
                base_ptr, offset_ast = format_arg_ptr.args[0], format_arg_ptr.args[1]
                if base_ptr.op == 'BVS' and offset_ast.op == 'BVV':
                    offset = offset_ast.args[0]

            if offset is None:
                return False

            i = offset % self.arch.bytes
            if i < len(arguments) and arguments[i] == 's':
                return True
            return False

        new_exprs = []
        ret_killed_exprs = []
        ptr_killed_exprs = []

        # arg_list_addr = self.get_value(arg_list)
        # if arg_list_addr:
        #     print("format-arg-list-ptr: %x" % (arg_list_addr))

        for trace_expr in self.block.forward_exprs:
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            # if arg_list_addr and trace_ast.op == 'Store' and trace_ast.args[0].op == 'BVV':
            #     s_addr = trace_ast.args[0].args[0]
            #     offset = s_addr - arg_list_addr

            if args and find_arg_taint(trace_ast, trace_sims, arg_list, args):
                self.block.is_tainted = 2
                new_expr = trace_expr.replace(trace_ast, s, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.ptr_id = self.block.addr
                new_expr.expr.taint_live = self.block.addr
                new_exprs.append(new_expr)

            if trace_ast.op == 'BVS' and s in trace_sims:
                ptr_killed_exprs.append(trace_expr)
                dst_value = get_value(self.block, s)
                # print("Killed-%x %s with %s" % (self.block.addr, trace_expr, dst_value))
                if type(dst_value) is int and get_scope(dst_value) == 'global':
                    self.block.global_defs.add(dst_value)

            if ret_name in trace_sims:
                ret_killed_exprs.append(trace_expr)

        for kill_expr in ret_killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        if len(ptr_killed_exprs):
            self.kill_forward_exprs(ptr_killed_exprs)

        cons_values = []
        cons_expr = None
        if constraint:
            # print("Has-cons: %s" % (constraint))
            cons_values, cons_expr = self.get_constraint(constraint, 3)
            # print("Con- %s %s" % (cons_values, cons_expr))

        for pre_block in self.block.predecessors:
            for new_expr in new_exprs:
                if len(cons_values):
                    # new_expr.constraints.extend(cons_values)
                    for cons_v in cons_values:
                        if cons_v not in new_expr.constraints:
                            new_expr.constraints.append(cons_v)
                elif cons_expr is not None:
                    if 'S' not in new_expr.constraints:
                        new_expr.constraints.append('S')
                # print("format-taint: %s %s" % (new_expr, new_expr.constraints))
                new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                new_expr.expr.taint_loc = self.block.addr
                new_expr.expr.flag &= 0xfeff
                new_expr.taint_propagaton_level += 1
                pre_block.backward_exprs.append(new_expr)

    def _find_taint_propagate_argv(self, argv, end_flag=None):
        """
        :param argv: a pointer list.
        :param end_flag: the end flag while read argv.
        """
        def find_taint_arg_index(ast, trace_sims, argv):
            if ast.op != 'Store' or argv not in ast.variables:
                return None
            offset = None
            format_arg_ptr = ast.args[0]
            if format_arg_ptr.op == 'BVS':
                offset = 0
            elif format_arg_ptr.op == '__add__' and len(format_arg_ptr.args) == 2:
                base_ptr, offset_ast = format_arg_ptr.args[0], format_arg_ptr.args[1]
                if base_ptr.op == 'BVS' and offset_ast.op == 'BVV':
                    offset = offset_ast.args[0]

            if offset is None:
                return None

            i = offset // self.arch.bytes if offset % self.arch.bytes == 0 else None
            return i

        def find_arg_end_index(argv_ptr, end_flag):
            # print("find-arg-end-index: %s %s" % (argv_ptr, end_flag))
            context_block = list(self.block.predecessors)[0]
            code_locations = context_block.code_locations
            actions = context_block.actions
            ins_len = len(code_locations)
            for i in range(ins_len-1, -1, -1):
                code_location = code_locations[i]
                action = actions[code_location]
                if action.action_type != 's' or action.value != 0:
                    continue
                if (type(argv_ptr) is int and
                        action.addr_type == 'S' and type(action.addr_value)):
                    offset =  action.addr_value - argv_ptr
                    return (offset // self.arch.bytes) if offset%self.arch.bytes == 0 else None
                elif type(argv_ptr) is str:
                    st_addr = action.dst_alias if action.dst_alias else action.dst
                    if type(st_addr) is tuple:
                        op, opnds = st_addr[0], st_addr[1]
                        if op == '+' and opnds[0] == argv_ptr and type(opnds[1]) is int:
                            return (opnds[1] // self.arch.bytes) if opnds[1]%self.arch.bytes == 0 else None

        argv_ptr = argv
        argv_value = self.get_value(argv)
        # print("argv-ptr: %s" % (argv_value))
        if argv_value and get_mem_permission(argv_value) == 'stack':
            argv_ptr = argv_value
        end_index = find_arg_end_index(argv_ptr, end_flag)
        if not end_index:
            return
        # print("argv-end-index: %s" % (end_index))

        for trace_expr in self.block.forward_exprs:
            if trace_expr.expr.flag & 0x100 == 0:
                continue

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            arg_index = find_taint_arg_index(trace_ast, trace_sims, argv)
            # print("tainted-arg-index: %s" % (arg_index))

            if arg_index is not None and arg_index < end_index:
                self.block.is_tainted = 2
                weaks_command_exec[self.block.addr].append(trace_expr)

    def _parse(self, s, fmtstr_reg):
        """
        Parse format strings.

        :param fmt_idx: The index of the (pointer to the) format string in the arguments list.
        :returns:       A FormatString object which can be used for replacing the format specifiers with arguments or
                        for scanning into arguments.
        """
        if self.block.format_args:
            return

        # print("parse-format: %s" % (fmtstr_reg))

        fmtstr_ptr = self.get_value(fmtstr_reg)
        # print("fmtstr-ptr-value: %s" % (fmtstr_ptr))
        if fmtstr_ptr is None:
            l.debug("Symbolic pointer to (format) string in %s" % (self.block))
            return
        elif type(fmtstr_ptr) is str:
            print("The fmtstr pointer is argument %s" % (fmtstr_ptr))
            return

        pe = get_mem_permission(fmtstr_ptr)
        # print("format-ptr: %x %s" % (fmtstr_ptr, pe))
        # if pe != 'ro' and pe != 'rw':
        if 'r' not in pe:
            return

        fmtstr_ptr = BVV(fmtstr_ptr)
        # print("formart-ptr: %s" % (fmtstr_ptr))

        length = self.get_string_len(fmtstr_ptr)
        # print("Get-length: %s" % (length))
        if length.symbolic:
            l.debug("Symbolic (formart) string length in %s" % (self.block))

        # if self.state.solver.is_true(length == 0):
        if length.args[0] == 0:
            return FormatString(self, [b""])

        # print("formart-ptr: %s, with lenght: %s" % (fmtstr_ptr, length))
        fmt_xpr = self.state.memory.load(fmtstr_ptr, length)

        fmt = [ ]
        for i in range(fmt_xpr.size(), 0, -8):
            char = fmt_xpr[i - 1 : i - 8]
            try:
                conc_char = self.state.solver.eval_one(char)
            except SimSolverError:
                # For symbolic chars, just keep them symbolic
                fmt.append(char)
            else:
                # Concrete chars are directly appended to the list
                fmt.append(bytes([conc_char]))

        # print("fmt: %s" % fmt)
        # self._get_fmt_args(fmt)
        self._find_fmt_parameters(fmt)
        # print("Get-fmt-args done!")


from angr.errors import SimProcedureArgumentError, SimProcedureError, SimSolverError
