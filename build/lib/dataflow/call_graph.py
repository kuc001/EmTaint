#!/usr/bin/env python

from .cfg_base import CFGBase

class CallGraph(CFGBase):
    def __init__(self):

        super(CallGraph, self).__init__()

        self._nodes = {}

        self.loops = []

        self._initialize_graph()

    def get_function_by_addr(self, addr):
        if addr in self._nodes:
            return self._nodes[addr]

    def get_all_callsites_to_function(self, function):
        """
        Get all callsite which call the given function.
        """
        callsites = []
        funcea = function.addr
        pre_functions = self.graph.predecessors(function)

        for pre_function in pre_functions:
            caller_sites = pre_function.callees.get(funcea)
            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for cs in caller_sites:
                callsites.append(cs)

        return callsites

    def travel_call_graph(self, node, worklist):
        changed = False
        worklist_set = set()
        stack = [node]
        worklist.append(node)
        worklist_set.add(node.addr)

        while stack:
            node = stack.pop()
            successor_nodes = self.graph.successors(node)
            caller_addr = node.addr
            for suc_node in successor_nodes:
                called_addr = suc_node.addr

                if suc_node.addr not in worklist_set \
                        and suc_node.addr not in self.analyses_done_set:
                    stack.append(suc_node)
                    worklist.append(suc_node)
                    worklist_set.add(suc_node.addr)
                    changed = True
        return changed

    def worklist_update(self, node, worklist):
        changed = False
        for n in self.graph.successors(node):
            if n.addr not in self.analyses_done_set:
                self.travel_call_graph(n, worklist)
                changed = True
        return changed

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

    def get_start_nodes(self):
        start_nodes = set()

        for n in self.graph.nodes():
            # print(n, n.binary_name)
            # print(list(self.graph.predecessors(n)))
            if n.binary_name == 'main' and n.addr > 0 and self.graph.in_degree(n) == 0:
                # print("get-start-node: %s" % (n))
                start_nodes.add(n)

        return start_nodes

    def get_all_nodes_by_root(self, root):
        """
        Get all nodes in the tree which root nood is given.
        """
        all_nodes = []
        traversed_nodes = set()

        all_nodes.append(root)
        traversed_nodes.add(root)

        stack = [root]
        while stack:
            node = stack.pop()
            succ_nodes = self.graph.successors(node)
            for succ_n in succ_nodes:
                if succ_n.addr and succ_n not in traversed_nodes:
                    all_nodes.append(succ_n)
                    traversed_nodes.add(succ_n)
                    stack.append(succ_n)

                    # print("edge: %s -> %s" % (node, succ_n))

        return all_nodes

    def _get_loop_callees(self, loop):
        loop_callees = set()

        for node in loop.body_nodes:

            succ_nodes = self.graph.successors(node)
            for succ_node in succ_nodes:
                loop_callees.add(succ_node)
                # print("loop %s call %s" % (node, succ_node))

        return loop_callees

    def get_pre_sequence_call_graph(self, start_node, tree_nodes, pre_sequence_nodes):
        """
        Get the pre sequences nodes in a call graph by root node start_node.
        """
        def _should_add_loop(loop, tree_nodes, pre_sequence_nodes):
            for s_node in loop.start_nodes:
                in_nodes = self.graph.predecessors(s_node)
                for in_node in in_nodes:
                    if (in_node not in pre_sequence_nodes and
                            in_node not in loop.body_nodes and
                            in_node in tree_nodes):
                        return False
            return True

        pre_sequence_nodes.append(start_node)
        traversed_nodes = set()
        traversed_nodes.add(start_node)

        debug_set = set()

        analyzed_loops = []
        worklist = [start_node]
        while worklist:
            block = worklist.pop()

            # DEBUG
            succ_blocks = self.graph.successors(block)
            # print("\n%s has succs %s" % (block, list(succ_blocks)))

            succ_blocks = self.graph.successors(block)

            for succ_block in succ_blocks:
                if succ_block.addr == 0:
                    continue

                # print("debug succ block: %s, is loop: %s" % (succ_block, succ_block.is_loop))
                if succ_block.is_loop:
                    loop = self.determine_node_in_loop(succ_block)
                    # print("loop %s" % (loop))
                    if loop in analyzed_loops:
                        continue

                    choosed = _should_add_loop(loop, tree_nodes, pre_sequence_nodes)
                    # print("choosed: %s" % (choosed))
                    if choosed:
                        analyzed_loops.append(loop)

                        for n in loop.start_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                                # print("loop add %s" % (n))

                        for n in loop.end_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                                # print("loop add %s" % (n))

                        # worklist.extend(loop.end_nodes)

                        loop_callees = self._get_loop_callees(loop)
                        for callee_node in loop_callees:
                            if callee_node.addr == 0:
                                continue

                            pre_nodes = list(self.graph.predecessors(callee_node))

                            choosed = True
                            if len(pre_nodes) >= 2:
                                for pre_n in pre_nodes:
                                    if (pre_n.addr and
                                            not pre_n.is_loop and
                                            pre_n in tree_nodes and
                                            pre_n not in pre_sequence_nodes):

                                        choosed = False
                                        break

                            if choosed and callee_node not in traversed_nodes:
                                pre_sequence_nodes.append(callee_node)
                                worklist.append(callee_node)
                                traversed_nodes.add(callee_node)

                else:
                    choosed = True
                    in_edges = self.graph.in_edges(succ_block)
                    if len(in_edges) >= 2:
                        for pre_block, _ in in_edges:
                            if pre_block.addr == 0:
                                continue

                            if pre_block not in pre_sequence_nodes and pre_block in tree_nodes:
                                choosed = False
                                debug_set.add(succ_block)
                                # print("%s has pre %s" % (succ_block, pre_block))
                                break

                    if choosed and succ_block not in traversed_nodes:
                        pre_sequence_nodes.append(succ_block)
                        worklist.append(succ_block)
                        traversed_nodes.add(succ_block)
                        # print("add %s" % (succ_block))

        # for n in debug_set:
        #     if n not in pre_sequence_nodes:
        #         print("not add %s" % (n))

