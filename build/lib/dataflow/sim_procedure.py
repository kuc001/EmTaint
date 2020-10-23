import inspect
import copy
import itertools
import claripy
from cle import Symbol


import logging
l = logging.getLogger(name=__name__)
l.setLevel("DEBUG")

symbolic_count = itertools.count()


class SimProcedure:
    """
    A SimProcedure is a wonderful object which describes a procedure to run on a state.

    You may subclass SimProcedure and override ``run()``, replacing it with mutating ``self.state`` however you like,
    and then either returning a value or jumping away somehow.

    A detailed discussion of programming SimProcedures may be found at https://docs.angr.io/docs/simprocedures.md

    :param arch:            The architecture to use for this procedure

    The following parameters are optional:

    :param symbolic_return: Whether the procedure's return value should be stubbed into a
                            single symbolic variable constratined to the real return value
    :param returns:         Whether the procedure should return to its caller afterwards
    :param is_syscall:      Whether this procedure is a syscall
    :param num_args:        The number of arguments this procedure should extract
    :param display_name:    The name to use when displaying this procedure
    :param cc:              The SimCC to use for this procedure
    :param sim_kwargs:      Additional keyword arguments to be passed to run()
    :param is_function:     Whether this procedure emulates a function
    """
    def __init__(
        self, project=None, cc=None, symbolic_return=None,
        returns=None, is_syscall=False, is_stub=False,
        num_args=None, display_name=None, library_name=None,
        is_function=None, **kwargs
    ):
        # WE'LL FIGURE IT OUT
        self.project = project
        self.arch = project.arch if project is not None else None
        self.addr = None
        self.cc = cc
        self.canonical = self

        self.state = project.factory.blank_state() if project else None

        self.kwargs = kwargs
        self.display_name = type(self).__name__ if display_name is None else display_name
        self.library_name = library_name
        self.syscall_number = None
        self.abi = None
        self.symbolic_return = symbolic_return

        # types
        self.argument_types = { } # a dictionary of index-to-type (i.e., type of arg 0: SimTypeString())
        self.return_type = None

        # set some properties about the type of procedure this is
        self.returns = returns if returns is not None else not self.NO_RET
        self.is_syscall = is_syscall
        self.is_function = is_function if is_function is not None else self.IS_FUNCTION
        self.is_stub = is_stub
        self.is_continuation = False
        self.continuations = {}

        # Get the concrete number of arguments that should be passed to this procedure
        if num_args is None:
            run_spec = inspect.getfullargspec(self.run)
            self.num_args = len(run_spec.args) - (len(run_spec.defaults) if run_spec.defaults is not None else 0) - 1
            # print("xxx %s has %d" % (self.display_name, self.num_args))
        else:
            self.num_args = num_args

        # runtime values
        self.arguments = None
        self.use_default_arguments = True
        self.ret_to = None
        self.ret_expr = None
        self.call_ret_expr = None
        self.inhibit_autoret = None
        self.flow_dir = None
        self.run_func = None
        self.block = None
        self.caller_function = None

    def __repr__(self):
        return "<SimProcedure %s%s%s%s%s>" % self._describe_me()

    def _describe_me(self):
        """
        return a 5-tuple of strings sufficient for formatting with ``%s%s%s%s%s`` to verbosely describe the procedure
        """
        return (
            self.display_name,
            ' (cont: %s)' % self.run_func if self.is_continuation else '',
            ' (syscall)' if self.is_syscall else '',
            ' (inline)' if not self.use_default_arguments else '',
            ' (stub)' if self.is_stub else '',
        )

    def execute(self, block, project, run_funciton, flow_dir=None, arguments=None, caller_function=None, ret_to=None):
        """
        Call this method with a block to execute the procedure.
        """
        # fill out all the fun stuff we don't want to frontload
        if self.addr is None and not block:
            self.addr = block.addr
        if self.project is None:
            self.project = project
            if self.state is None:
                self.state = project.factory.blank_state()
        if self.arch is None:
            self.arch = project.arch

        if run_funciton is None:
            raise Exception("the run function is None!")

        inst = copy.copy(self)
        inst.block = block
        inst.caller_function = caller_function
        inst.ret_to = ret_to
        inst.inhibit_autoret = False
        inst.flow_dir = flow_dir
        inst.run_func = run_funciton

        # check to see if this is a syscall and if we should override its return value
        override = None
        if inst.is_syscall:
            pass # TODO

        if callable(override):
            try:
                r = override(state, run=inst)
            except TypeError:
                r = override(state)
            inst.use_state_arguments = True

        elif override is not None:
            r = override
            inst.use_state_arguments = True

        else:
            # get the arguments

            # handle if this is a continuation from a return
            if inst.is_continuation:
                pass # TODO

            else:
                if arguments is None:
                    inst.use_default_arguments = True
                    sim_args = [ inst.arg(_) for _ in range(inst.num_args) ]
                    inst.arguments = sim_args
                else:
                    inst.use_default_arguments = False
                    sim_args = arguments[:inst.num_args]
                    inst.arguments = arguments

            print('args: %s' % (inst.arguments))
            # run it
            l.debug("Executing %s%s%s%s%s with %s, %s", *(inst._describe_me() + (sim_args, inst.kwargs)))
            r = getattr(inst, inst.run_func)(*sim_args, **inst.kwargs)

        return r

    def make_continuation(self, name):
        # make a copy of the canon copy, customize it for the specific continuation, then hook it
        if name not in self.canonical.continuations:
            cont = copy.copy(self.canonical)
            target_name = '%s.%s' % (self.display_name, name)
            should_be_none = self.project.loader.extern_object.get_symbol(target_name)
            if should_be_none is None:
                cont.addr = self.project.loader.extern_object.make_extern(target_name, sym_type=Symbol.TYPE_OTHER).rebased_addr
            else:
                l.error("Trying to make continuation %s but it already exists. This is bad.", target_name)
                cont.addr = self.project.loader.extern_object.allocate()
            cont.is_continuation = True
            cont.run_func = name
            self.canonical.continuations[name] = cont
            self.project.hook(cont.addr, cont)
        return self.canonical.continuations[name].addr

    #
    # Implement these in a subclass of SimProcedure!
    #

    NO_RET = False          # set this to true if control flow will never return from this function
    ADDS_EXITS = False      # set this to true if you do any control flow other than returning
    IS_FUNCTION = True      # does this procedure simulate a function?
    ARGS_MISMATCH = False   # does this procedure have a different list of arguments than what is provided in the
                            # function specification? This may happen when we manually extract arguments in the run()
                            # method of a SimProcedure.

    local_vars = ()         # if you use self.call(), set this to a list of all the local variable
                            # names in your class. They will be restored on return.

    def run(self, *args, **kwargs): # pylint: disable=unused-argument
        """
        Implement the actual procedure here!
        """
        raise SimProcedureError("%s does not implement a run() method" % self.__class__.__name__)

    def static_exits(self, blocks):  # pylint: disable=unused-argument
        """
        Get new exits by performing static analysis and heuristics. This is a fast and best-effort approach to get new
        exits for scenarios where states are not available (e.g. when building a fast CFG).

        :param list blocks: Blocks that are executed before reaching this SimProcedure.
        :return: A list of tuples. Each tuple is (address, jumpkind).
        :rtype: list
        """

        if self.ADDS_EXITS:
            raise SimProcedureError("static_exits() is not implemented for %s" % self)
        else:
            # This SimProcedure does not add any new exit
            return [ ]

    #
    # misc properties
    #

    @property
    def should_add_successors(self):
        return self.successors is not None

    #
    # Working with calling conventions
    #

    def set_args(self, args):
        arg_session = self.cc.arg_session
        for arg in args:
            if self.cc.is_fp_value(args):
                arg_session.next_arg(True).set_value(self.state, arg)
            else:
                arg_session.next_arg(False).set_value(self.state, arg)

    def arg(self, i):
        """
        Returns the ith argument. Raise a SimProcedureArgumentError if we don't have such an argument available.

        :param int i: The index of the argument to get
        :return: The argument
        """
        if self.use_default_arguments:
            if i >= len(default_arguments):
                r = 's%d' % (i-len(default_arguments))
            else:
                r = 'r%d' % (default_arguments[i])

        else:
            if i >= len(self.arguments):
                raise SimProcedureArgumentError("Argument %d does not exist." % i)
            r = self.arguments[i]           # pylint: disable=unsubscriptable-object

        return r

    def get_stack_arg_ptr(self, arg):
        index = int(arg[1:], 10)
        sp_name = 'r%d' % (self.arch.sp_offset)
        sp_at = self.block.live_defs[sp_name]
        if type(sp_at.value) is int:
            sp_value = sp_at.value
        else:
            l.info("Couldn't found stack pointer value in %s" % (self.block))
            return

        if self.arch.name == 'MIPS32':
            stack_offset = 0x10
        else:
            stack_offset = 0
        return sp_value + index * self.arch.bytes + stack_offset


    #
    # Control Flow
    #

    def inline_call(self, procedure, *arguments, **kwargs):
        """
        Call another SimProcedure in-line to retrieve its return value.  Returns an instance of the procedure with the ret_expr property set.

        :param procedure:       The class of the procedure to execute
        :param arguments:       Any additional positional args will be used as arguments to the
                                procedure call
        :param sim_kwargs:      Any additional keyword args will be passed as sim_kwargs to the
                                procedure construtor
        """
        e_args = [ self.state.solver.BVV(a, self.state.arch.bits) if isinstance(a, int) else a for a in arguments ]
        p = procedure(project=self.project, **kwargs)
        return p.execute(self.state, None, arguments=e_args)

    def ret(self, expr=None):
        """
        Add an exit representing a return from this function.
        If this is not an inline call, grab a return address from the state and jump to it.
        If this is not an inline call, set a return expression with the calling convention.
        """
        self.inhibit_autoret = True

        if expr is not None:
            if o.SIMPLIFY_RETS in self.state.options:
                l.debug("... simplifying")
                l.debug("... before: %s", expr)
                expr = self.state.solver.simplify(expr)
                l.debug("... after: %s", expr)

            if self.symbolic_return:
                size = len(expr)
                new_expr = self.state.solver.Unconstrained(
                        "symbolic_return_" + self.display_name,
                        size,
                        key=('symbolic_return', self.display_name)) #pylint:disable=maybe-no-member
                self.state.add_constraints(new_expr == expr)
                expr = new_expr

            self.ret_expr = expr

        ret_addr = None
        if self.use_state_arguments:
            ret_addr = self.cc.teardown_callsite(
                    self.state,
                    expr,
                    arg_types=[False]*self.num_args if self.cc.args is None else None)

        if not self.should_add_successors:
            l.debug("Returning without setting exits due to 'internal' call.")
            return

        if self.ret_to is not None:
            ret_addr = self.ret_to

        if ret_addr is None:
            raise SimProcedureError("No source for return address in ret() call!")

        self._exit_action(self.state, ret_addr)
        self.successors.add_successor(self.state, ret_addr, self.state.solver.true, 'Ijk_Ret')

    def call(self, addr, args, continue_at, cc=None):
        """
        Add an exit representing calling another function via pointer.

        :param addr:        The address of the function to call
        :param args:        The list of arguments to call the function with
        :param continue_at: Later, when the called function returns, execution of the current
                            procedure will continue in the named method.
        :param cc:          Optional: use this calling convention for calling the new function.
                            Default is to use the current convention.
        """
        self.inhibit_autoret = True

        if cc is None:
            cc = self.cc

        call_state = self.state.copy()
        ret_addr = self.make_continuation(continue_at)
        saved_local_vars = list(zip(self.local_vars, map(lambda name: getattr(self, name), self.local_vars)))
        simcallstack_entry = (self.state.regs.sp, self.arguments, saved_local_vars, self.state.regs.lr if self.state.arch.lr_offset is not None else None)
        cc.setup_callsite(call_state, ret_addr, args)
        call_state.callstack.top.procedure_data = simcallstack_entry

        # TODO: Move this to setup_callsite?
        if call_state.libc.ppc64_abiv == 'ppc64_1':
            call_state.regs.r2 = self.state.mem[addr + 8:].long.resolved
            addr = call_state.mem[addr:].long.resolved
        elif call_state.arch.name in ('MIPS32', 'MIPS64'):
            call_state.regs.t9 = addr

        self._exit_action(call_state, addr)
        self.successors.add_successor(call_state, addr, call_state.solver.true, 'Ijk_Call')

        if o.DO_RET_EMULATION in self.state.options:
            # we need to set up the call because the continuation will try to tear it down
            ret_state = self.state.copy()
            cc.setup_callsite(ret_state, ret_addr, args)
            ret_state.callstack.top.procedure_data = simcallstack_entry
            guard = ret_state.solver.true if o.TRUE_RET_EMULATION_GUARD in ret_state.options else ret_state.solver.false
            self.successors.add_successor(ret_state, ret_addr, guard, 'Ijk_FakeRet')

    def jump(self, addr):
        """
        Add an exit representing jumping to an address.
        """
        self.inhibit_autoret = True
        self._exit_action(self.state, addr)
        self.successors.add_successor(self.state, addr, self.state.solver.true, 'Ijk_Boring')

    def exit(self, exit_code):
        """
        Add an exit representing terminating the program.
        """
        self.inhibit_autoret = True
        self.state.options.discard(o.AST_DEPS)
        self.state.options.discard(o.AUTO_REFS)

        if isinstance(exit_code, int):
            exit_code = self.state.solver.BVV(exit_code, self.state.arch.bits)
        self.state.history.add_event('terminate', exit_code=exit_code)
        self.successors.add_successor(self.state, self.state.regs.ip, self.state.solver.true, 'Ijk_Exit')

    @staticmethod
    def _exit_action(state, addr):
        if o.TRACK_JMP_ACTIONS in state.options:
            state.history.add_action(SimActionExit(state, addr))

    def ty_ptr(self, ty):
        return SimTypePointer(self.arch, ty)

    def label_variable_type(self, reg, var_type):
        """
        Lable the reg's type as var_type.
        """
        if var_type == 'N':
            var_type = basic_types[self.arch.bits]

        if reg in self.block.live_defs:
            reg_at = self.block.live_defs[reg]
            reg_at.var_type = var_type
            update_action_var_type(self.caller_function.cfg, reg_at)

        elif reg in default_arg_names and reg not in self.caller_function.arguments:
            self.caller_function.arguments.append(reg)

    def label_return_type(self, ret_type):
        if ret_type == 'N':
            ret_type = basic_types[self.arch.bits]

        ret_name = 'r%d' % (self.arch.ret_offset)
        at = Action('p', CodeLocation(self.block.addr, 0), ret_name, 'RET', self.arch.bits)
        at.var_type = ret_type
        self.block.live_defs[ret_name] = at

    def label_return_type_v2(self, ret_name, ret_type):
        if ret_type == 'N':
            ret_type = basic_types[self.arch.bits]

        at = Action('p', CodeLocation(self.block.addr, 0), ret_name, 'RET', self.arch.bits)
        at.var_type = ret_type
        self.block.live_defs[ret_name] = at

    def set_strtok_ptr(self):
        """
        The strtok has a global ptr SAVE_PTR, we lable it with 'r1001'.
        """
        at = Action('p', CodeLocation(self.block.addr, 0), 'r1001', 'N', self.arch.bits)
        self.block.live_defs['r1001'] = at

    def get_reg_action(self, reg):
        pre_blocks = list(self.block.predecessors)
        if len(pre_blocks):
            context_bb = pre_blocks[0]
            return context_bb.live_defs[reg]

    def kill_forward_exprs(self, killed_exprs):
        ptr_ids = set()
        remove_exprs = []
        # print("killed-exprs: %s" % (killed_exprs))
        for kill_expr in killed_exprs:
            ptr_ids.add(kill_expr.expr.ptr_id)

        # print("ptr_ids: %s" % (ptr_ids))
        for trace_expr in self.block.forward_exprs:
            if trace_expr.expr.ptr_id in ptr_ids:
                remove_exprs.append(trace_expr)

        for remove_expr in remove_exprs:
            self.block.forward_exprs.remove(remove_expr)

    def reg_taint_propagate(self, dst, src, constraint=None):
        """
        Propagate taint data from one register to other.
        """
        if self.flow_dir != 'F':
            return

        copy_len_taint = False
        new_exprs = []
        killed_exprs = []
        # print("reg-taint-propagate: %s %s" % (dst, src))

        for trace_expr in self.block.forward_exprs:

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            if find_ptr_taint_v1(src, trace_ast, trace_sims) and not self.block.contain_exprs(trace_expr):
                print("Lucky, find tiant transfer, src 0x%x!" % (trace_expr.expr.ptr_id))
                new_expr = trace_expr.replace(trace_ast, dst, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.taint_loc = self.block.addr
                new_expr.expr.ptr_id = self.block.addr
                new_exprs.append(new_expr)

            elif constraint and constraint in trace_sims and trace_ast.op == 'BVS':
                copy_len_taint = True

            elif dst in trace_sims and trace_ast.op == 'BVS':
                print("Killed: %s" % (trace_expr))
                killed_exprs.append(trace_expr)

        if len(killed_exprs):
            self.kill_forward_exprs(killed_exprs)

        if len(new_exprs) == 0:
            if copy_len_taint and self.block.addr not in tainted_length_locs:
                tainted_length_locs.append(self.block.addr)
            return

        if constraint:
            value = constraint
            if constraint in self.block.live_defs:
                cons_at = self.block.live_defs[constraint]
                if type(cons_at.value) is int:
                    value = cons_at.value
                elif type(cons_at.value) is list:
                    value = cons_at.value[0]

        for pre_block in self.block.predecessors:
            for new_expr in new_exprs:
                if constraint:
                    new_expr.expr.constraints.append(value)

                if copy_len_taint:
                    new_expr.expr.flag |= 0x1000
                new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                pre_block.backward_exprs.append(new_expr)

    def taint_propagate_to_ret(self, src):
        """
        Propagate taint data from src to return pointer (strstr, strchr, etc.).
        """
        # print("taint-propagate-to-ret:")
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)

        for trace_expr in self.block.forward_exprs:

            trace_ast = trace_expr.expr.ast
            trace_sims = trace_expr.expr.sims

            if find_ptr_taint_v1(src, trace_ast, trace_sims) and not self.block.contain_exprs(trace_expr):
                new_expr = trace_expr.replace(trace_ast, ret_name, rep_type='ptr')
                new_expr.expr.trace_dir = 'F'
                new_expr.index = 0
                new_exprs.append(new_expr)

            if ret_name in trace_expr.expr.sims:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        for succ_block in self.block.successors:
            for new_expr in new_exprs:
                succ_block.forward_exprs.append(new_expr)
                print("Lucky, find taint propagate to ret in %s" % (self.block))

        return 0

    def get_string_len(self, s):
        """
        Find string length in binary.
        """
        step = 1
        chunk_size = 1
        null_seq = self.state.solver.BVV(0, 8)
        max_symbolic_bytes = self.state.libc.buf_symbolic_bytes
        # max_str_len = self.state.libc.max_str_len
        max_str_len = 512
        search_len = max_str_len
        # print("max_str_len: %s" % (max_str_len))

        r, c, i = self.state.memory.find(s, null_seq, search_len, max_symbolic_bytes=max_symbolic_bytes, step=step, chunk_size=chunk_size)

        print(r, c, i)
        result = r - s
        if result.args[0] > max_str_len:
            result = BVV(max_str_len)

        return result

    def has_trace_expr(self):
        if self.flow_dir == 'B' or self.flow_dir == 'F' and len(self.block.forward_exprs) == 0:
            return False
        return True

    def exec_free(self, ptr):
        """
        Free pointer and may kill expr in forward.
        """
        killed_exprs = []
        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            base_ptr = trace_expr.expr.base_ptr
            if ptr == base_ptr:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)
            print("Free-ptr %s" % (kill_expr))


    def propagate_int_taint_to_ret(self, ptr, name=None):
        """
        In forward, if the ptr is taint, then it may propagate taint to ret (int).
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)

        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ptr in sims and trace_ast.op == 'BVS':
                ret_type = basic_types[self.arch.bits]
                new_expr = trace_expr.replace(trace_ast, ret_name, rep_type=ret_type)
                new_expr.expr.trace_dir = 'F'
                new_expr.expr.var_type = ret_type
                new_expr.index = 0
                if name:
                    new_expr.expr.value = BVS(name)
                new_exprs.append(new_expr)

            if ret_name in sims:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        for succ_block in self.block.successors:
            for new_expr in new_exprs:
                print("Find-ret-int-taint: %s" % (new_exprs))
                succ_block.forward_exprs.append(new_expr)

        return 0

    def initial_arguments_taint_source(self, describe):
        """
        Initial taint source with function's arguments (e.g. recv).
        """
        trace_exprs = []
        read_len = 1

        for arg, arg_desc in describe.items():

            if arg_desc == 'dst':
                data_ast = BVS(arg)
                taint_expr = construct_trace_expr(data_ast,
                                                    value=None,
                                                    pattern='LBF',
                                                    data_type='Tdata',
                                                    trace_dir='B',
                                                    block_addr=self.block.addr,
                                                    stmt_idx=0,
                                                    index=0,
                                                    var_type='ptr',
                                                    base_ptr=arg)

                taint_expr.expr.flag = 0x100
                taint_expr.expr.ptr_id = self.block.addr
                taint_expr.expr.taint_loc = self.block.addr
                taint_expr.expr.taint_source = self.block.addr
                trace_exprs.append(taint_expr)
                print("Get-taint-source: %s %s" % (self.block, taint_expr))

            elif arg_desc == 'length':
                length = get_value(self.block, arg)
                length = length if type(length) is int else BVS(arg)
                read_len *= length

            elif arg_desc == 'size':
                size = get_value(self.block, arg)
                size = size if type(size) is int else BVS(arg)
                read_len *= size

            elif arg_desc == 'src':
                src_ast = BVS(arg)
                taint_src_expr = construct_trace_expr(src_ast,
                                                      pattern='OB',
                                                      data_type='uData',
                                                      trace_dir='B',
                                                      block_addr=self.block.addr,
                                                      stmt_idx=0,
                                                      index=0,
                                                      var_type=basic_types[src_ast.size()])
                taint_src_expr.expr.taint_source = self.block.addr
                taint_src_expr.expr.flag = 0x4000
                trace_exprs.append(taint_src_expr)
                print("Taint-src: %s" % (taint_src_expr))

        if length is None and size is None:
            raise Exception("Couldn't find read length in taint source %s" % (self.block))

        if type(read_len) is int:
            print("Taint-source-len: %d" % (read_len))
            taint_expr.expr.constraints.append(read_len)

        else:
            read_len = claripy.simplify(read_len)
            constraint_expr = construct_trace_expr(read_len,
                                                value=None,
                                                pattern='OB',
                                                data_type='uData',
                                                trace_dir='B',
                                                block_addr=self.block.addr,
                                                stmt_idx=0,
                                                index=0,
                                                var_type=basic_types[read_len.size()])
            constraint_expr.expr.taint_source = self.block.addr
            constraint_expr.expr.flag = 0x8000
            trace_exprs.append(constraint_expr)
            print("Taint-source-len: %s" % (constraint_expr))

        for pre_block in self.block.predecessors:
            index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            for trace_expr in trace_exprs:
                trace_expr.index = index
                pre_block.backward_exprs.append(trace_expr)

    def initial_ret_taint_source(self, describe):
        """
        Initial taint source with function's return (e.g. getenv).
        """
        ret_name = 'r%d' % (self.arch.ret_offset)
        for arg, arg_desc in describe.items():
            argi_ast = BVS(arg)

            if arg_desc == 'src':
                pass

            elif arg_desc == 'length':
                pass

        data_ast = BVS(ret_name)
        taint_expr = construct_trace_expr(data_ast,
                                            value=None,
                                            pattern='LBF',
                                            data_type='Tdata',
                                            trace_dir='F',
                                            block_addr=self.block.addr,
                                            stmt_idx=0,
                                            index=0,
                                            var_type='ptr',
                                            base_ptr=ret_name)

        taint_expr.expr.flag = 0x100
        taint_expr.expr.ptr_id = self.block.addr
        for succ_block in self.block.successors:
            succ_block.forward_exprs.append(taint_expr)


from dataflow.global_config import default_arguments, basic_types, default_arg_names
from dataflow.vex_process import Action
from dataflow.code_location import CodeLocation
from dataflow.parse_ast import BVV, BVS, find_ptr_taint_v1, get_value
from dataflow.variable_type import update_action_var_type
from dataflow.data_collector import tainted_length_locs
from dataflow.variable_expression import construct_trace_expr

from angr.errors import SimProcedureError, SimProcedureArgumentError
from angr.sim_type import SimTypePointer
from angr.state_plugins.sim_action import SimActionExit
from angr.calling_conventions import DEFAULT_CC
