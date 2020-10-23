#!/usr/bin/env python

from .global_config import default_arg_names


class FunctionAttribute(object):
    def __init__(self, addr, procedural_name=None, binary_name=None, start_node=None, cfg=None):
        self.addr = addr
        self.procedural_name = procedural_name
        self.binary_name = binary_name
        self.start_node = start_node
        self.start_nodes = None
        self.loops = []

        self.cfg = cfg
        self.graph_parser = None

        self.inc_locations = set()

        self.callsite_arg_definitions = {}
        self.callsite_ret_definitions = {}

        self.callee_use_exprs = {}
        self.callee_def_exprs = {}
        self.callee_ret_def_exprs = {}

        self.input_global_taints = {}

        self.arg_contexts = []
        self.arg_constraints = []
        self.taint_contexts = set()
        self.taint_exprs = []
        self.analyzed_taint_source = set()

        self.icall_targets = {}

        self.arguments = []
        self.concret_contexts = {}

        self.is_loop = False

        # Label the function been analyzed state.
        self.flag = 0x0

        """
        The special_flag record the function's state.
            0000 0001 : label the function has been analyzed.
        """
        self.special_flag = 0x0

        self.trace_dir = None
        self.taint_source = False

        self.concrete_inc_addrs = set()
        self.global_addrs = set()

    def __repr__(self):
        if self.procedural_name and self.addr == 0:
            return "<extern-function (%s) (%s)>" % (self.procedural_name, self.arguments)

        else:
            return "<function (0x%x) (%s)>" % (self.addr, self.arguments)

    def __eq__(self, other):
        if isinstance(other, FunctionAttribute):
            return self.addr == other.addr and self.procedural_name == other.procedural_name
        return False

    def __hash__(self):
        return self.addr if self.addr !=0 else hash(self.procedural_name)

    def get_block(self, addr):
        """
        Get a CFG block in function.cfg.graph by addr.
        """
        return self.cfg.get_node_by_addr(addr)

    def correct_arguments(self):
        """
        Some identified arguments are error, correct them.
        """
        # first_arg = default_arg_names[0]
        # if first_arg not in self.arguments:
        #     self.arguments.clear()

        arg_max = -1
        for i, default_arg in enumerate(default_arg_names):
            if default_arg in self.arguments:
                arg_max = i
                break

        for i, default_arg in enumerate(default_arg_names):
            if i > arg_max:
                break
            if default_arg not in self.arguments:
                self.arguments.append(default_arg)

    def determine_node_in_loop(self, node):
        """
        If a node in a cycle, then return the cycle
        :param node: a node in the function cfg
        :return loop
        """
        for loop in self.loops:
            if node in loop.body_nodes:
                return loop
        return None

    def calculate_context_id(self, context_exprs):
        """
        Calculate the context exprs' id
        """
        result_id = 0
        ids = set()
        for trace_expr in context_exprs:
            for var, sim in trace_expr.expr.sims.items():
                var_id = hash(var)
                if var_id not in ids:
                    ids.add(var_id)
                    result_id += var_id
        return result_id

    def is_taint_context_analyzed(self, taint_expr):
        """
        If the taint arguments or global pointer has been analyzed before.
        Avoid analyze a function more times with same context.
        """
        base_ptr = taint_expr.expr.base_ptr
        taint_ast = taint_expr.expr.ast
        taint_src = taint_expr.expr.taint_source
        if type(base_ptr) is int and base_ptr not in self.taint_contexts:
            self.taint_contexts.add(base_ptr)
            return False

        elif type(base_ptr) is str or base_ptr is None:
            ast_id = taint_expr.expr.ast.__hash__()
            if (taint_ast.op == 'BVS' and taint_src and
                    taint_src not in self.analyzed_taint_source):
                self.analyzed_taint_source.add(taint_src)
                self.taint_contexts.add(ast_id)
                return False
            elif ast_id not in self.taint_contexts:
                self.taint_contexts.add(ast_id)
                return False

        return True

    def sort_arguments(self):
        """
        Rearrange the arguments.
        """
        if len(self.arguments) == 0:
            return

    def reset_inter_func_path(self, funcea, input_expr, taint_expr):
        """
        :param funcea: the function address of a function.
        :param input_expr: the input expr of a function.
        :param taint_expr: the summarized tainted expr of a function.
        """
        # print("reset-func-path: input-> %s, return-> %s" % (input_expr, taint_expr))
        # print("  -->input-path: %s\n  -->taint-path: %s" % (input_expr.inter_funcs, taint_expr.inter_funcs))
        funcea = '%x' % funcea
        old_path = taint_expr.inter_funcs
        input_path = input_expr.inter_funcs
        j = -1
        for i, addr in enumerate(old_path):
            if addr == funcea:
                j = i
                break
        if j == -1:
            taint_expr.inter_funcs = input_path.copy()
            taint_expr.inter_funcs.append(funcea)
        else:
            taint_expr.inter_funcs = input_path.copy() + old_path[j:]
        # print("new-path: %s" % (taint_expr.inter_funcs))
        taint_expr.inter_icall_level = input_expr.inter_icall_level
        # taint_expr.taint_propagaton_level = input_expr.taint_propagaton_level

    def get_taint_exprs(self, caller_function, callsite_taints):
        taint_results = []
        context_ids = {}
        input_taints = callsite_taints[:]
        # print("caller_function: %s %s" % (caller_function, caller_function.input_global_taints))
        if caller_function and len(caller_function.input_global_taints):
            for base_addr, g_taints in caller_function.input_global_taints.items():
                input_taints.extend(g_taints)

        for input_expr in input_taints:
            con_id = input_expr.expr.ast.__hash__()
            context_ids[con_id] = input_expr

        for taint_expr in self.taint_exprs:
            taint_id = taint_expr.expr.taint_id
            # print("Function %s has taint:\n %s, id: %d" % (self, taint_expr, taint_id))
            # print("context_ids: %s" % (context_ids))
            if self.is_add_taint(taint_expr, taint_results) and taint_id in context_ids:
                new_expr = taint_expr.deep_copy()
                input_expr = context_ids[taint_id]
                new_expr.expr.taint_id = input_expr.expr.taint_id
                new_expr.expr.taint_source = input_expr.expr.taint_source

                self.reset_inter_func_path(self.addr, input_expr, new_expr)

                # new_expr.forward_path = input_expr.forward_path
                # new_expr.backward_path = input_expr.backward_path
                taint_results.append(new_expr)

        return taint_results

    def check_arg_ptrs(self, arg_info):
        """
        Check whether function's argument has been analyzed before.
        """
        remove_args = []
        for arg in arg_info:
            if arg in self.arg_contexts:
                remove_args.append(arg)

            else:
                self.arg_contexts.append(arg)

        for arg in remove_args:
            arg_info.pop(arg)

    def get_var_concret_value(self, block, var):
        arg = None
        if 'r' in var:
            pre_blocks = list(block.predecessors)
            pre_block = pre_blocks[0] if len(pre_blocks) else block
            if var in pre_block.live_defs:
                var_at = pre_block.live_defs[var]
                arg = var_at.argument

        elif 't' in var:
            arg = block.live_defs[var].argument

        if arg and arg in self.concret_contexts:
            return self.concret_contexts[arg]

    def get_pre_sequence_in_function(self, start_nodes):
        """
        Get control flow graph's pre-order.
        """
        def _should_add_loop(cfg, loop, pre_sequence_nodes):
            # print("add_loop %s" % (pre_sequence_nodes))
            for s_node in loop.start_nodes:
                in_nodes = cfg.graph.predecessors(s_node)
                # print(in_nodes)
                for in_node in in_nodes:
                    if in_node not in pre_sequence_nodes and in_node not in loop.body_nodes:
                        return False
            return True

        self.start_nodes = start_nodes
        pre_sequence_nodes = self.cfg.pre_sequence_nodes
        traversed_nodes = set()
        for s_node in start_nodes:
            pre_sequence_nodes.append(s_node)
        for s_node in start_nodes:
            traversed_nodes.add(s_node)

        analyzed_loops = []
        worklist = start_nodes[:]

        while worklist:
            block = worklist.pop()
            succ_blocks = self.cfg.graph.successors(block)
            for succ_block in succ_blocks:
                # print("psu-debug: %s has succ %s %s" % (block, succ_block, succ_block.is_loop))
                if succ_block.is_loop:
                    loop = self.determine_node_in_loop(succ_block)
                    if loop is None or loop in analyzed_loops:
                        continue

                    # print("psu-debug: analyze loop %s" % (loop))
                    # analyzed_loops.append(loop)
                    choosed = _should_add_loop(self.cfg, loop, pre_sequence_nodes)
                    # print("loop %s %s, choosed %s" % (succ_block, loop, choosed))
                    if choosed:
                        analyzed_loops.append(loop)
                        for n in loop.start_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                        for n in loop.end_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                        # pre_sequence_nodes.extend(loop.start_nodes)
                        # pre_sequence_nodes.extend(loop.end_nodes)
                        worklist.extend(loop.end_nodes)

                else:
                    choosed = True
                    # pre_blocks = cfg.graph.predecessors(succ_block)
                    in_edges = self.cfg.graph.in_edges(succ_block)
                    if len(in_edges) >= 2:
                        for pre_block, _ in in_edges:
                            if pre_block not in pre_sequence_nodes:
                                choosed = False
                                break
                    if choosed:
                        # if succ_block.addr == 0x2bc5db:
                        #     print("add succ node %s" % (succ_block))
                        #     print("block %s, pre blocks %s" % (block, pre_blocks))
                        if succ_block not in traversed_nodes:
                            pre_sequence_nodes.append(succ_block)
                            worklist.append(succ_block)
                            # print("node %s has in sequence" % (succ_block))
                            traversed_nodes.add(succ_block)

    def get_global_taints(self, block, forward_exprs):
        """
        If the function has global taint exprs, then check whether the tainted
        data propagate to this block.
        """
        for base_addr, taint_exprs in self.input_global_taints.items():
            # if base_addr in self.taint_contexts:
            #     continue
            if base_addr in block.global_addrs:
                for taint_expr in taint_exprs:
                    iid = taint_expr.iid
                    if iid in block.traced_iids:
                        continue
                    block.traced_iids.add(iid)
                    new_expr = taint_expr.copy()
                    forward_exprs.append(new_expr)
                    # print("Found-Gtaint: %s %s" % (block, new_expr))

    def is_add_taint(self, taint_expr, input_taints):
        taint_ast_id = taint_expr.expr.ast.__hash__()
        for input_taint in input_taints:
            if input_taint.expr.ast.__hash__() == taint_ast_id:
                return False
        return True

    def kill_global_define(self, input_expr):
        pass

    def merge_input_global_taints_v1(self, callsite, input_taints):
        """
        The input_taints are all global tainted exprs.
        """
        for base_addr, taint_exprs in input_taints.items():
            if base_addr not in self.input_global_taints:
                self.input_global_taints[base_addr] = []
            for input_expr in taint_exprs:
                if self.is_add_taint(input_expr, self.input_global_taints[base_addr]):
                    new_expr = input_expr.deep_copy()
                    new_expr.clear_path()
                    new_expr.index = 0
                    new_expr.set_taint_id()
                    new_expr.clear_sim_actions_locs()
                    new_expr.expr.is_ret = False

                    new_expr.inter_funcs.append('%x' % (self.addr))
                    if callsite.node_type == 'iCall':
                        new_expr.inter_icall_level += 1

                    self.input_global_taints[base_addr].append(new_expr)
                    # print(" -->Add-global-taint(v1): %x %s" % (base_addr, new_expr))

    def merge_input_global_taints_v2(self, callsite, input_taints):
        """
        The input_taints come from callsite.
        """
        remove_exprs = []
        for input_expr in input_taints:
            if not input_expr.expr.only_global():
                continue
            remove_exprs.append(input_expr)
            base_addr = input_expr.expr.base_ptr
            if base_addr not in self.input_global_taints:
                self.input_global_taints[base_addr] = []
            if self.is_add_taint(input_expr, self.input_global_taints[base_addr]):
                new_expr = input_expr.deep_copy()
                new_expr.clear_path()
                new_expr.index = 0
                new_expr.set_taint_id()
                new_expr.clear_sim_actions_locs()
                new_expr.expr.is_ret = False

                new_expr.inter_funcs.append('%x' % self.addr)
                if callsite.node_type == 'iCall':
                    new_expr.inter_icall_level += 1

                self.input_global_taints[base_addr].append(new_expr)
                # print(" -->Add-global-taint(v2): %x %s" % (base_addr, new_expr))

        # for r_expr in remove_exprs:
        #     input_taints.remove(r_expr)

    def add_analyzed_taint_contexts(self, input_taint_exprs):
        """
        While the function has been analyzed by the input_taint_exprs,
        then add the taint context to self.taint_contexts
        """
        for taint_expr in input_taint_exprs:
            base_ptr = taint_expr.expr.base_ptr
            if type(base_ptr) is int:
                self.taint_contexts.add(base_ptr)
            else:
                context_id = taint_expr.expr.ast.__hash__()
                self.taint_contexts.add(context_id)

        for base_addr in self.input_global_taints:
            self.taint_contexts.add(base_addr)

    def parameter_has_redefined(self, trace_expr):
        """
        The function has re-define to trace_expr.
        """
        for taint_expr in self.taint_exprs:
            if not taint_expr.expr.is_ret and trace_expr.is_ast_equal(taint_expr):
                return True
        return False

    def kill_input_global_taints(self, block):
        """
        The function has a re-define to a global address.
        Then kill the input global tainted data with this global addr.
        """
        for gaddr in block.global_defs:
            if gaddr in self.input_global_taints:
                self.input_global_taints.pop(gaddr)

    def set_definition_contexts(self, definition_exprs):
        """
        :param list definition_exprs: all this function have definitoins (parameter def or global def).
        """
        for definition_expr in definition_exprs:
            if definition_expr.expr.data_type != 'Tdata':
                continue

            base_ptr = definition_expr.expr.base_ptr
            if type(base_ptr) is int:
                # self.taint_contexts.add(base_ptr)
                pass
            else:
                self.taint_exprs.append(definition_expr)
                # print("set-callee-def-context: %x %s" % (self.addr, definition_expr))
