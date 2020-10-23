import inspect
import copy
import itertools
import claripy
from cle import Symbol


import logging
l = logging.getLogger(name=__name__)
# l.setLevel("INFO")

symbolic_count = itertools.count()

nvram_values = {}

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

    def execute(self, block, project, run_funciton, flow_dir=None, arguments=None, caller_function=None, ret_to=None, purpose=0):
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
        inst.purpose = purpose
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

            # print('args: %s' % (inst.arguments))
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
        # print("label_var_type: %s %s %s" % (self.block, reg, var_type))
        if var_type == 'N':
            var_type = basic_types[self.arch.bits]

        if reg in self.block.live_defs:
            reg_at = self.block.live_defs[reg]
            reg_at.var_type = var_type
            # print(reg_at)
            update_action_var_type(self.caller_function.cfg, reg_at)

        elif reg in default_arg_names and reg not in self.caller_function.arguments:
            self.caller_function.arguments.append(reg)

    def label_return_type(self, ret_type):
        if ret_type == 'N':
            ret_type = basic_types[self.arch.bits]

        ret_name = 'r%d' % (self.arch.ret_offset)
        src_name = 'R_%s' % (self.display_name)
        at = Action('p', CodeLocation(self.block.addr, 0), ret_name, ret_name, self.arch.bits)
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

    def get_value(self, reg):
        live_defs = self.block.live_defs
        if reg in live_defs:
            reg_at = live_defs[reg]
            # print(reg_at, reg_at.argument)
            if type(reg_at.value) is int:
                return reg_at.value
            elif type(reg_at.value) is list:
                for value in reg_at.value:
                    if value:
                        return value
            elif reg_at.argument and self.caller_function and reg_at.argument in self.caller_function.concret_contexts:
                return self.caller_function.concret_contexts[reg_at.argument]

    def get_reg_action(self, reg):
        pre_blocks = list(self.block.predecessors)
        if len(pre_blocks):
            context_bb = pre_blocks[0]
            return context_bb.live_defs[reg] if reg in context_bb.live_defs else None

    def kill_forward_exprs(self, killed_exprs):
        ptr_ids = set()
        remove_exprs = []
        for kill_expr in killed_exprs:
            # print("kill-expr: %s %x" % (kill_expr, kill_expr.expr.ptr_id))
            ptr_ids.add(kill_expr.expr.ptr_id)

        for trace_expr in self.block.forward_exprs:
            # print("f-expr: %s %x" % (trace_expr, trace_expr.expr.ptr_id))
            if trace_expr.expr.ptr_id in ptr_ids:
                remove_exprs.append(trace_expr)

        for remove_expr in remove_exprs:
            # print("remove-expr: %s" % (remove_expr))
            self.block.forward_exprs.remove(remove_expr)
        # print(self.block.forward_exprs)

    def get_min_cons_value(self, constraints):
        concret_cons = [c for c in constraints if type(c) is int and c != 0]
        return min(concret_cons) if len(concret_cons) else None

    def _calculate_copy_lenght_constraint(self, cons_values, taint_cons_exprs):
        """
        For the strncpy/memncpy's length argument.
        If the length arg is tainted, then calculate the length constraint.
        """
        for cons_expr in taint_cons_exprs:
            cons_type = cons_expr.expr.cons_type
            if cons_type == 4: #atoi/atol
                min_cons = self.get_min_cons_value(cons_expr.constraints)
                if min_cons:
                    cons_values.append(min_cons)

    def get_constraint(self, c, cons_type):
        cons_expr = None
        values = []
        # print("Get-cons in-%x" % (self.block.addr))
        # for pre_block in self.block.predecessors:
        #     print("Pre-block: %s" % (pre_block))
        if c in self.block.live_defs:
            cons_at = self.block.live_defs[c]
            if type(cons_at.value) is int:
                values.append(cons_at.value)
            elif type(cons_at.value) is list:
                for v in cons_at.value:
                    if type(v) is int:
                        values.append(v)

        if len(values):
            return values, cons_expr

        data_ast = BVS(c)
        cons_expr = construct_trace_expr(data_ast,
                                    value=None,
                                    pattern='OB',
                                    data_type='Cons',
                                    trace_dir='B',
                                    block_addr=self.block.addr,
                                    stmt_idx=0,
                                    index=0,
                                    var_type=basic_types[data_ast.size()])

        cons_expr.expr.cons_type = cons_type
        return values, cons_expr

    def reg_taint_propagate(self, dst, src, constraint=None, copy_type=0):
        """
        Propagate taint data from one register to other.
        e.g. memcpy/strcpy/strncpy ...
        :param copy_type: label different data copy.
            0 is string copy (strcpy)
            1 is data copy (memcpy)
        """
        if self.flow_dir != 'F':
            return

        copy_len_taint = False
        new_exprs = []
        mem_copy_exprs = []
        killed_exprs = []
        taint_cons_exprs = []
        # print("reg-taint-propagate: %s %s" % (dst, src))

        for trace_expr in self.block.forward_exprs:
            flag = trace_expr.expr.flag
            if self.purpose == 0 and flag & 0x100 == 0:
                continue
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            data_type = trace_expr.expr.data_type
            if find_ptr_taint_v1(src, trace_ast, trace_sims) and not self.block.contain_exprs(trace_expr):
                print("Lucky, find taint transfer in %x, ptr_id 0x%x" % (self.block.addr, trace_expr.expr.ptr_id))
                self.block.is_tainted = 2
                new_expr = trace_expr.replace(trace_ast, dst, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                # new_expr.expr.taint_loc = self.block.addr
                new_expr.expr.ptr_id = self.block.addr
                new_expr.expr.taint_live = self.block.addr
                new_exprs.append(new_expr)

            elif constraint and constraint in trace_sims and trace_ast.op == 'BVS':
                copy_len_taint = True
                taint_cons_exprs.append(trace_expr)
                print("Found-copy-len-taint: %s %s" % (self.block, trace_expr))

            elif dst in trace_sims and trace_ast.op == 'BVS':
                dst_value = get_value(self.block, dst)
                # print("Killed-%x %s with %s" % (self.block.addr, trace_expr, dst_value))
                if type(dst_value) is int and get_scope(dst_value) == 'global':
                    self.block.global_defs.add(dst_value)
                killed_exprs.append(trace_expr)

            elif (copy_type == 1 and src in trace_sims and
                    (data_type == 'Tdata' and len(trace_expr.expr.sim_actions) or
                    data_type != 'Tdata')):
                new_expr = trace_expr.replace(src, dst, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.ptr_id = self.block.addr
                new_expr.expr.taint_live = self.block.addr
                mem_copy_exprs.append(new_expr)

        if len(killed_exprs):
            self.kill_forward_exprs(killed_exprs)

        cons_values = []
        cons_expr = None
        if constraint and len(taint_cons_exprs) == 0:
            cons_values, cons_expr = self.get_constraint(constraint, cons_type=3)

        if len(taint_cons_exprs):
            self._calculate_copy_lenght_constraint(cons_values, taint_cons_exprs)

            for taint_cons_expr in taint_cons_exprs:
                if self.display_name in ['memcpy', 'memmove'] and taint_cons_expr.expr.cons_type in [4, 6]:
                    if taint_cons_expr not in weaks_only_length[self.block.addr]:
                        weaks_only_length[self.block.addr].append(taint_cons_expr)

        # print("Cons- values: %s cons_expr: %s" % (cons_values, cons_expr))
        # if len(new_exprs) and self.display_name == 'strcpy':
        #     print("Lucky, find tainted strcpy in %s" % (self.block))

        for pre_block in self.block.predecessors:
            last_index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            for new_expr in new_exprs:
                if constraint and copy_len_taint:
                    new_expr.expr.taint_loc = self.block.addr
                    new_expr.expr.flag |= 0x1000
                elif constraint is None:
                    new_expr.expr.taint_loc = self.block.addr
                    new_expr.expr.flag &= 0xefff
                else:
                    new_expr.expr.taint_loc = None

                # if len(cons_values) and not copy_len_taint:
                for c in cons_values:
                    if c not in new_expr.constraints:
                        # print("add-cons-5: %s %s" % (new_expr, c))
                        new_expr.constraints.append(c)

                # Why???
                if len(cons_values) and not copy_len_taint:
                    pass
                elif new_expr.expr.data_type == 'Tdata' and cons_expr is not None and cons_expr not in pre_block.backward_exprs:
                    cons_expr.index = last_index
                    pre_block.backward_exprs.append(cons_expr)
                    new_expr.cons_ids.append(cons_expr.expr.alias_id)

                new_expr.index = last_index
                new_expr.expr.flag &= 0xfeff
                new_expr.taint_propagaton_level += 1
                pre_block.backward_exprs.append(new_expr)

            for new_expr in mem_copy_exprs:
                new_expr.index = last_index
                new_expr.expr.flag &= 0xfeff
                pre_block.backward_exprs.append(new_expr)
                # print("Find-mem-copy: %s %s" % (self.block, new_expr))

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
                new_expr.expr.ptr_id = self.block.addr
                new_expr.index = 0
                new_exprs.append(new_expr)

            if ret_name in trace_expr.expr.sims:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        for succ_block in self.block.successors:
            for new_expr in new_exprs:
                new_expr.forward_path.add(self.block.addr)
                new_expr.taint_propagaton_level += 1
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

        # print(r, c, i)
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
            # print("Free-ptr %s" % (kill_expr))


    def propagate_int_taint_to_ret(self, ptr, name=None, cons_type=0):
        """
        In forward, if the ptr is taint, then it may propagate taint to ret (int).
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)

        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ptr in sims and (trace_ast.op == 'BVS' or is_str_pointer(trace_ast)):
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
                new_expr.expr.cons_type = cons_type
                succ_block.forward_exprs.append(new_expr)
                if cons_type == 4:
                    new_expr.expr.ptr_id = self.block.addr
                    if len(new_expr.constraints): # atoi/atol
                        self._calculate_atoi_constraint(new_expr)
                print("Find-ret-taint (%s): %s with-cons-type: %d" % (name, new_expr, cons_type))
                print("  -->with-cons: %s" % (new_expr.constraints))

        return 0

    def _calculate_atoi_constraint(self, ret_expr):
        """
        For the atoi(*ptr), the ptr pointer to a string.
        If the string has a length constraint, then calculate the max atoi return value.
        """
        constraints = ret_expr.constraints
        concret_cons = [c for c in constraints if type(c) is int and c != 0]
        min_cons = min(concret_cons) if len(concret_cons) else None
        if min_cons is None:
            return
        if min_cons < 8:
            cons_value = 10**min_cons - 1
            ret_expr.constraints = [cons_value]

    def _add_special_cons(self, ptr_id, cons_type):
        for trace_expr in self.block.forward_exprs:
            if trace_expr.expr.ptr_id == ptr_id:
                sym_cons = 'C%d' % (cons_type)
                trace_expr.add_constraint(sym_cons)
                # trace_expr.expr.constraints.append(sym_cons)
                # print("Special-cons: %s %s" % (trace_expr, ptr_id))

    def add_special_constraint(self, ptr, cons_type, name=None):
        """
        Some libc function will attach constraint to taint data.
        For example, inet_pton, gethostbyname, etc...
        """
        # print("Add-special-cons: %s %s" % (self.block, name))
        find_flag = 0
        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ptr in sims and trace_ast.op == 'BVS':
                find_flag = 1
                ptr_id = trace_expr.expr.ptr_id
                self._add_special_cons(ptr_id, cons_type)

        if find_flag == 0:
            return

        # ret_name = 'r%d' % (self.arch.ret_offset)
        # data_ast = BVS(ret_name)
        # cons_expr = construct_trace_expr(data_ast,
        #                                  value=None,
        #                                  pattern='OF',
        #                                  data_type='Cons',
        #                                  trace_dir='F',
        #                                  block_addr=self.block.addr,
        #                                  stmt_idx=0,
        #                                  index=0,
        #                                  var_type=basic_types[data_ast.size()])

        # print("Add-special-ret: %s" % (cons_expr))
        # for succ_block in self.block.successors:
        #     succ_block.forward_exprs.append(cons_expr)

    def add_special_constraint_v2(self, s1, s2, cons_type, name=None):
        """
        Some libc function will attach constraint to taint data.
        For example, strcmp, etc... (cons_type=2)
        """
        ptr_ids = set()
        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            if (s1 in sims or s2 in sims) and trace_ast.op == 'BVS':
                ptr_id = trace_expr.expr.ptr_id
                ptr_ids.add(ptr_id)

        if len(ptr_ids) == 0:
            return

        # print("Add-special-cons-%d: %s %s" % (cons_type, self.block, name))
        cons_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        data_ast = BVS(ret_name)
        for ptr_id in ptr_ids:
            cons_expr = construct_trace_expr(data_ast,
                                             value=None,
                                             pattern='OF',
                                             data_type='Cons',
                                             trace_dir='F',
                                             block_addr=self.block.addr,
                                             stmt_idx=0,
                                             index=0,
                                             var_type=basic_types[data_ast.size()])
            cons_expr.expr.ptr_id = ptr_id
            cons_expr.expr.cons_type = cons_type
            cons_exprs.append(cons_expr)

        for succ_block in self.block.successors:
            for cons_expr in cons_exprs:
                succ_block.forward_exprs.append(cons_expr)
                # print("Add-cons-%d in %x %s" % (cons_type, succ_block.addr, cons_expr))

    def label_successor_constraint_type(self, cons_type):
        """
        Label the successor block's constraint type for different libc function,
        : cons_type = 1 : inet_pton, etc. (return 0, no constraint)
        : cons_type = 2 : strcmp, etc. (return 0, has constraint)
        : cons_type = 3 : strlen, atoi, etc. (constraints on length or size)
        """
        for succ_block in self.successors:
            succ_block.cons_type = cons_type

    def update_with_heap(self, heap_size):
        """
        In backward, the malloc libc function return heap address,
        and the backward trace expr dependence with the returned address.
        : param heap_size: the malloc's argument
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        for trace_expr in self.block.backward_exprs:
            sims = trace_expr.expr.sims
            sim_actions = trace_expr.expr.sim_actions
            trace_ast = trace_expr.expr.ast
            data_type = trace_expr.expr.data_type

            # if data_type == 'Tdata' and len(sim_actions) == 0 and ret_name in sims:
            if ret_name in sims:
                rep_name = 'ptr_%x' % (self.block.addr)
                new_expr = trace_expr.replace(ret_name, rep_name, rep_type='ptr')
                new_expr.expr.trace_dir = 'B'
                new_exprs.append(new_expr)
                killed_exprs.append(trace_expr)

        if len(new_exprs):
            cons_values, cons_expr = self.get_constraint(heap_size, cons_type=7)

        for kill_expr in killed_exprs:
            self.block.backward_exprs.remove(kill_expr)

        for new_expr in new_exprs:
            self.block.backward_exprs.append(new_expr)
            if cons_values:
                new_expr.expr.memory_size = cons_values[0]
            elif cons_expr:
                new_expr.expr.memory_size = cons_expr.expr.alias_id
            # print("malloc-new: %s %s heap-size %s" % (self.block, new_expr, str(cons_values)))
        return 0

    def process_open_handle(self, fd, fd_type, cons_type):
        """
        In backward, check whether the trace data dependence to a open libc.
        : param fd: the opens function's file handle.
        : param fd: the file handle's type, 0 is int, 1 is pointer.
        : param cons_type: the constraint type.
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        fd_type = basic_types['default'] if fd_type == 0 else 'ptr'
        for trace_expr in self.block.backward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ret_name in sims:
                killed_exprs.append(trace_expr)
                if trace_ast.op == 'BVS':
                    new_expr = trace_expr.replace(ret_name, fd, rep_type=fd_type)
                    new_expr.expr.trace_dir = 'B'
                    new_expr.expr.cons_type = cons_type
                    new_exprs.append(new_expr)
                    # print("ooo->open-%x %s" % (self.block.addr, new_expr))
                # else:
                #     rep_name = '%s_%x' % (self.display_name, self.block.addr)
                #     new_expr = trace_expr.replace(ret_name, rep_name, rep_type=basic_types['default'])
                #     new_expr.expr.trace_dir = 'B'
                #     new_exprs.append(new_expr)

        for kill_expr in killed_exprs:
            self.block.backward_exprs.remove(kill_expr)

        for pre_block in self.block.predecessors:
            last_index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            for new_expr in new_exprs:
                new_expr.index = last_index
                pre_block.backward_exprs.append(new_expr)

        return 0

    def process_socket_handle(self, cons_type):
        """
        In backward, check whether the trace data dependence to a socket.
        : param cons_type: the constraint type.
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        for trace_expr in self.block.backward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ret_name in sims:
                killed_exprs.append(trace_expr)
                rep_name = '%s_%x' % (self.display_name, self.block.addr)
                new_expr = trace_expr.replace(ret_name, rep_name, rep_type=basic_types['default'])
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.cons_type = cons_type
                new_exprs.append(new_expr)

        for kill_expr in killed_exprs:
            self.block.backward_exprs.remove(kill_expr)

        for new_expr in new_exprs:
            self.block.backward_exprs.append(new_expr)

        return 0

    def check_backward_libc_return(self, ret_type=0):
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        # print("check-lib-ret: %s" % (self.block))
        for trace_expr in self.block.backward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if ret_name in sims:
                killed_exprs.append(trace_expr)
                if ret_type == 1:
                    rep_name = 'o'
                else:
                    rep_name = '%s_%x' % (self.display_name, self.block.addr)
                new_expr = trace_expr.replace(ret_name, rep_name, rep_type=basic_types['default'])
                new_expr.expr.trace_dir = 'B'
                new_exprs.append(new_expr)

        for kill_expr in killed_exprs:
            self.block.backward_exprs.remove(kill_expr)

        for new_expr in new_exprs:
            self.block.backward_exprs.append(new_expr)

        return 0

    def get_string(self, ptr):
        """
        Get the constant string from the address ptr.
        :param ptr: a pointer
        """
        str_ptr = self.get_value(ptr)
        if str_ptr is None:
            l.debug("Symbolic pointer to (format) string in %s" % (self.block))
            return

        pe = get_mem_permission(str_ptr)
        # print("format-ptr: %x %s" % (fmtstr_ptr, pe))
        if 'r' not in pe:
            return

        ptr_ast = BVV(str_ptr)

        length = self.get_string_len(ptr_ast)
        # print("Get-length: %s" % (length))
        if length.symbolic:
            l.debug("Symbolic (formart) string length in %s" % (self.block))

        if length.args[0] == 0:
            return
        str_xpr = self.state.memory.load(ptr_ast, length)
        return str_xpr

    def nvram_set_value(self, key, value):
        """
        Some firmware use nvram save data and load data.
        This function is used to module the nvram set value.
        :param key: a constant string.
        :param value: the set value.
        """
        # print("nvram-set-value in %s" % (self.block))
        for trace_expr in self.block.forward_exprs:
            sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if value in sims and trace_ast.op == 'BVS':
                key_str = self.get_string(key)
                if key_str is not None:
                    nvram_values[key_str.__hash__()] = trace_expr.deep_copy()
                    # print(key_str)
                    # fmt = [ ]
                    # for i in range(key_str.size(), 0, -8):
                    #     char = key_str[i - 1 : i - 8]
                    #     try:
                    #         conc_char = self.state.solver.eval_one(char)
                    #     except SimSolverError:
                    #         # For symbolic chars, just keep them symbolic
                    #         fmt.append(char)
                    #     else:
                    #         # Concrete chars are directly appended to the list
                    #         fmt.append(bytes([conc_char]))
                    # print("fmt: %s" % fmt)
                    # print("set-expr: %s %s" % (trace_expr, nvram_values[key_str.__hash__()].cons_ids))


    def nvram_get_value(self, key):
        """
        Some firmware use nvram save data and load data.
        This function is used to module the nvram get value.
        :param key: a constant string.
        :return: return the get value by key.
        """
        key_str = self.get_string(key)
        if key_str is not None:
            key_id = key_str.__hash__()
            if key_id in nvram_values:
                value_expr = nvram_values[key_id]
                ret_name = 'r%d' % (self.arch.ret_offset)
                data_ast = BVS(ret_name)
                value_ast = value_expr.expr.ast
                new_expr = value_expr.replace(value_ast, data_ast, rep_type=value_expr.expr.var_type)
                new_expr.clear_cycle_locs()
                new_expr.clear_path()
                new_expr.index = 0
                new_expr.expr.ptr_id = self.block.addr

                for succ_block in self.block.successors:
                    succ_block.forward_exprs.append(new_expr)

    def process_strtok_r(self, s, delim, save_ptr):
        """
        Process strtok_r libc function's taint propagation.
        """
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        for trace_expr in self.block.forward_exprs:
            trace_ast = trace_expr.expr.ast
            if (((s in trace_expr.expr.sims and trace_ast.op == 'BVS' ) or
                     (save_ptr in trace_expr.expr.sims and trace_ast.op == 'Store' and trace_ast.args[0].op == 'BVS')) and
                    not self.block.contain_exprs(trace_expr)):
                new_expr = trace_expr.replace(trace_ast, ret_name, rep_type='ptr')
                new_expr.expr.trace_dir = 'F'
                new_expr.expr.ptr_id = self.block.addr
                new_expr.index = 0
                new_exprs.append(new_expr)

            # if s != save_ptr and save_ptr in trace_expr.expr.sims and trace_ast.op == 'BVS':
            #     killed_exprs.append(trace_expr)

            elif ret_name in trace_expr.expr.sims:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        if len(new_exprs):
            trace_expr = new_exprs[0]
            trace_ast = trace_expr.expr.ast
            s_ptr = BVS(save_ptr, trace_ast.size())
            save_data = claripy.Store(s_ptr, s_ptr.size())
            # new_expr = trace_expr.replace(trace_expr.expr.ast, save_data, rep_info=sim_types, rep_sim_actions=xx)
            new_expr = trace_expr.deep_copy()
            new_expr.expr.ast = save_data
            code_location = CodeLocation(self.block.addr, 0)
            new_expr.expr.sims.clear()
            new_expr.expr.initial_sims(var_type='ptr')
            new_expr.expr.initial_sim_actions(code_location, var_type='ptr')
            new_expr.expr.trace_dir = 'B'

            for pre_block in self.block.predecessors:
                last_index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                new_expr.expr.kill_store_action_by_loc()
                new_expr.expr.flag &= 0xfeff
                new_expr.taint_propagaton_level += 1
                new_expr.expr.taint_live = self.block.addr
                new_expr.index = last_index
                pre_block.backward_exprs.append(new_expr)

        for succ_block in self.block.successors:
            for new_expr in new_exprs:
                new_expr.taint_propagaton_level += 1
                succ_block.forward_exprs.append(new_expr)
                # print("In-strtok, find %s" % (new_expr))

        return 0


    def initial_arguments_taint_source(self, describe):
        """
        Initial taint source with function's arguments (e.g. recv).
        """
        trace_exprs = []
        taint_expr = None
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

                # taint_expr.expr.flag = 0x100
                taint_expr.expr.ptr_id = self.block.addr
                # taint_expr.expr.taint_loc = self.block.addr
                taint_expr.expr.taint_source = self.block.addr
                trace_exprs.append(taint_expr)
                # print("Get-taint-source: %s %s" % (self.block, taint_expr))

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
                # print("Taint-src: %s" % (taint_src_expr))

        if length is None and size is None:
            raise Exception("Couldn't find read length in taint source %s" % (self.block))

        if type(read_len) is int:
            taint_expr.constraints.append(read_len)
            # print("Taint-source-len: %d" % (read_len))

        else:
            read_len = claripy.simplify(read_len)
            constraint_expr = construct_trace_expr(read_len,
                                                value=None,
                                                pattern='OB',
                                                data_type='Cons',
                                                trace_dir='B',
                                                block_addr=self.block.addr,
                                                stmt_idx=0,
                                                index=0,
                                                var_type=basic_types[read_len.size()])
            constraint_expr.expr.taint_source = self.block.addr
            constraint_expr.expr.flag = 0x8000
            taint_expr.cons_ids.append(constraint_expr.expr.alias_id)
            trace_exprs.append(constraint_expr)
            print("Taint-source-len: %s" % (constraint_expr))

        for pre_block in self.block.predecessors:
            index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            for trace_expr in trace_exprs:
                trace_expr = trace_expr.deep_copy()
                trace_expr.index = index
                trace_expr.inter_funcs.append('%x' % pre_block.func_addr)
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
        taint_expr.expr.taint_source = self.block.addr
        taint_expr.expr.ptr_id = self.block.addr
        # print("Init-ret-tiant: %s %s" % (taint_expr, taint_expr.expr.constraints))
        for succ_block in self.block.successors:
            taint_expr.inter_funcs.append('%x' % self.block.func_addr)
            succ_block.forward_exprs.append(taint_expr)


from dataflow.global_config import default_arguments, basic_types, default_arg_names
from dataflow.vex_process import Action
from dataflow.code_location import CodeLocation
from dataflow.parse_ast import BVV, BVS, find_ptr_taint_v1, get_value, get_scope, get_mem_permission, not_contain_ls, is_str_pointer
from dataflow.variable_type import update_action_var_type
from dataflow.data_collector import weaks_only_length
from dataflow.variable_expression import construct_trace_expr

from angr.errors import SimProcedureError, SimProcedureArgumentError
from angr.sim_type import SimTypePointer
from angr.state_plugins.sim_action import SimActionExit
from angr.calling_conventions import DEFAULT_CC
