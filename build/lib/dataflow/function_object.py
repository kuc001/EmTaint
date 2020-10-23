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

        self.arg_contexts = []
        self.taint_contexts = set()
        # self.taint_context_ids = []
        self.taint_exprs = []

        self.icall_targets = {}

        self.arguments = []
        self.concret_contexts = {}

        self.is_loop = False

        # Label the function been analyzed state.
        self.flag = 0x0

        self.taint_source = False

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
        first_arg = default_arg_names[0]
        if first_arg not in self.arguments:
            self.arguments.clear()

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

    def is_taint_context_analyzed(self, context_exprs):
        """
        If the taint arguments or global pointer has been analyzed before.
        Avoid analyze a function more times with same context.
        """
        flag = True
        for trace_expr in context_exprs:
            # for var, sim in trace_expr.expr.sims.items():
            #     if type(var) is str and var not in self.taint_contexts:
            #         self.taint_contexts.add(var)
            #         return False

            base_ptr = trace_expr.expr.base_ptr
            # print("base-ptr: %s" % (base_ptr))
            # print("taint-contexts: %s" % (self.taint_contexts))
            if type(base_ptr) is int and base_ptr not in self.taint_contexts:
                self.taint_contexts.add(base_ptr)
                flag = False

            elif type(base_ptr) is str:
                ast_id = trace_expr.expr.ast.__hash__()
                if ast_id not in self.taint_contexts:
                    self.taint_contexts.add(ast_id)
                    flag = False

        return flag

    def sort_arguments(self):
        """
        Rearrange the arguments.
        """
        if len(self.arguments) == 0:
            return

    def get_taint_exprs(self, context_exprs):
        taint_results = []
        context_ids = {}
        for trace_expr in context_exprs:
            con_id = trace_expr.expr.ast.__hash__()
            context_ids[con_id] = trace_expr.expr.taint_id
            print("context: %s, ast: %d, id: %d" % (trace_expr, con_id, trace_expr.expr.taint_id))

        for taint_expr in self.taint_exprs:
            taint_id = taint_expr.expr.taint_id
            print("Function %s has taint:\n %s, id: %d" % (self, taint_expr, taint_id))
            if taint_id in context_ids:
                new_expr = taint_expr.deep_copy()
                new_expr.expr.taint_id = context_ids[taint_id]
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
                    if loop in analyzed_loops:
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
