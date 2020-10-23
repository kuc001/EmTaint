import networkx
from collections import defaultdict

import logging
l = logging.getLogger("loopfinder")
l.setLevel("INFO")


class Loop(object):
    def __init__(self, first_node, body_nodes, graph):
        self.first_node = first_node
        self.body_nodes = body_nodes
        self.graph = graph

        self.start_nodes = []
        self.end_nodes = []
        self.in_nodes = []
        self.out_nodes = []

        self.constraints = []
        self.inc_variables = {}
        self.recurisive_info = []

        # Lable the loop execute state, whether the loop should forward or
        # backward.
        self.execute_flag = 0x0

        self.analyzed_times = 0

    def __repr__(self):
        s = "<Loop @ %#x, %d blocks>" % (self.first_node.addr, len(self.body_nodes))
        return s

    def __eq__(self, other):
        if isinstance(other, Loop):
            return self.first_node == other.first_node
        return False

    def __hash__(self):
        return self.first_node.addr


class LoopFinder(object):
    """
    Extracts all the loops from all the functions in a binary.
    """

    def get_loops_from_call_graph(self, call_graph):
        """
        Return all Loop instances that can be extracted from a graph.
        """
        graph = call_graph.graph
        sub_graphs = []
        # for subg in networkx.strongly_connected_component_subgraphs(graph):
        for subg in (networkx.induced_subgraph(graph, nodes).copy() for nodes in networkx.strongly_connected_components(graph)):
            if len(subg.nodes()) == 1:
                if len(list(subg.successors(list(subg.nodes())[0]))) == 0:
                    continue

            me = self._initial_loop_object(call_graph, subg)
            sub_graphs.append(me)
        call_graph.loops = sub_graphs

    def get_loop_inout_nodes_from_call_graph(self, call_graph):
        graph = call_graph.graph
        for loop in call_graph.loops:
            for node in loop.body_nodes:
                succ_nodes = graph.successors(node)
                outs = [n for n in succ_nodes if n not in loop.body_nodes]
                if len(outs):
                    loop.end_nodes.append(node)
                pre_nodes = graph.predecessors(node)
                ins = [n for n in pre_nodes if n not in loop.body_nodes]
                if len(ins):
                    loop.start_nodes.append(node)

    def get_loops_from_graph(self, function):
        """
        Return all Loop instances that can be extracted from a graph.
        """
        cfg = function.cfg
        graph = cfg.graph
        sub_graphs = []

        # print("Get loops in function: %s" % (function))
        # for node in graph.nodes():
        #     print("cfg node: %s" % (node))

        # for subg in networkx.strongly_connected_component_subgraphs(graph):
        for subg in (networkx.induced_subgraph(graph, nodes).copy() for nodes in networkx.strongly_connected_components(graph)):
            if len(subg.nodes()) == 1:
                if len(list(subg.successors(list(subg.nodes())[0]))) == 0:
                    continue

            me = self._initial_loop_object(cfg, subg)
            sub_graphs.append(me)
        function.loops = sub_graphs
        return sub_graphs

    def get_loop_inout_nodes(self, function):
        cfg = function.cfg
        for loop in function.loops:
            for node in loop.body_nodes:
                succ_nodes = cfg.get_successors(node)
                outs = [n for n in succ_nodes if n not in loop.body_nodes]
                if len(outs):
                    loop.end_nodes.append(node)
                pre_nodes = cfg.get_predecessors(node)
                ins = [n for n in pre_nodes if n not in loop.body_nodes]
                if len(ins):
                    loop.start_nodes.append(node)

    def _get_original_node(self, cfg, node):
        if hasattr(node, 'node_type') and (node.node_type == 'Call' or node.node_type == 'iCall' and type(node.target) is int):
            return cfg.callsites[node.__hash__()]

        else:
            return cfg._nodes[node.addr]

    def _initial_loop_object(self, func_cfg, loop_graph):
        """
        Ctreate a loop instance and get start nodes, end nodes and sequence of a loop.
        """

        start_nodes = []
        end_nodes = []
        in_nodes = set()
        out_nodes = set()

        loop_nodes = {}
        original_nodes = []

        for node in loop_graph.nodes():
            # print("Loop :%s" % (node))
            original_node = self._get_original_node(func_cfg, node)
            original_nodes.append(original_node)
            loop_nodes[node.addr] = node

        for node in original_nodes:
            pre_nodes = func_cfg.graph.predecessors(node)
            ins = [n for n in pre_nodes if n.addr not in loop_nodes]
            if len(ins):
                start_nodes.append(node)

                for in_node in ins:
                    in_nodes.add(in_node)

            succ_nodes = func_cfg.graph.successors(node)
            outs = [n for n in succ_nodes if n.addr not in loop_nodes]
            if len(outs):
                end_nodes.append(node)

                for out_node in outs:
                    out_nodes.add(out_node)

        # print("\nLoop %s len: %d" % (original_nodes[0], len(original_nodes)))
        # for src, dst in loop_graph.edges():
        #     print("%s -> %s" % (src, dst))

        if len(start_nodes) == 0 and hasattr(func_cfg, 'addr'):
            start_node = func_cfg._nodes[func_cfg.addr]
            start_nodes.append(start_node)

        if len(start_nodes) == 0:
            first_node = original_nodes[0]
            loop = Loop(first_node, original_nodes, loop_graph)
            l.info("The loop %s has not start nodes. Do it future." % (loop))

        else:
            original_start_node = start_nodes[0]
            loop_start_node = loop_nodes[original_start_node.addr]
            # print("\nloop start: %s\n" % (loop_start_node))

            loop_bodys = self._get_loop_sequence_nodes(func_cfg, loop_start_node, loop_graph)
            first_node = loop_bodys[0]
            loop = Loop(first_node, loop_bodys, loop_graph)

        loop.start_nodes = start_nodes
        loop.end_nodes = end_nodes
        loop.in_nodes = list(in_nodes)
        loop.out_nodes = list(out_nodes)

        # print("loop %s has in nodes: %s" % (loop, loop.in_nodes))
        # print("loop %s has out nodes: %s" % (loop, loop.out_nodes))

        # print("Get loop: %s" % (loop))

        return loop

    def _get_loop_sequence_nodes(self, func_cfg, loop_start_node, loop_graph):
        new_start_nodes = []
        trace_path = defaultdict(list)
        branch_info = defaultdict(list)
        path_contain_branchs = {}

        traversed_nodes = {loop_start_node}

        s_node = loop_start_node
        path_contain_branchs[s_node] = set()
        trace_path[s_node].append(s_node)

        stack = [s_node]

        while stack:
            node = stack.pop()

            succ_nodes = loop_graph.successors(node)
            for succ_node in succ_nodes:
                if succ_node == node:
                    continue

                if succ_node in traversed_nodes:
                    branch_info[succ_node].append(s_node)
                    continue

                pre_nodes = loop_graph.predecessors(succ_node)
                if any([n for n in pre_nodes if n != succ_node and n not in traversed_nodes]):
                    if succ_node not in new_start_nodes:
                        new_start_nodes.append(succ_node)

                    path_contain_branchs[s_node].add(succ_node)
                    branch_info[succ_node].append(s_node)

                else:
                    traversed_nodes.add(succ_node)
                    stack.append(succ_node)
                    trace_path[s_node].append(succ_node)

                    if succ_node in path_contain_branchs[s_node]:
                        path_contain_branchs[s_node].remove(succ_node)

            if len(stack) == 0 and len(new_start_nodes):
                s_node = new_start_nodes.pop()
                path_contain_branchs[s_node] = set()
                if s_node.addr == loop_start_node.addr:
                    break

                traversed_nodes.add(s_node)
                trace_path[s_node].append(s_node)
                stack.append(s_node)

        # print("\nLoop path info:")
        # for s_node, sequence in trace_path.items():
        #     print("\nstart node: %s" % (s_node))
        #     for n in sequence:
        #         print("%s" % (n))

        # print("\nBrancn info:")
        # for end_node, start_nodes in branch_info.items():
        #     print("end node: %s" % (end_node))
        #     print("start nodes: %s" % (start_nodes))

        # print("\nEach path contain remain branch:")
        # for s_node, remain_branch in path_contain_branchs.items():
        #     print("Branch start: %s" % (s_node))
        #     print("remain branchs: %s" % (remain_branch))

        loop_sequence = []
        self._generate_loop_sequence(loop_start_node, trace_path, branch_info, path_contain_branchs, loop_sequence)

        # print("\nsequence length: %d" % (len(loop_sequence)))
        # for n in loop_sequence:
        #     print("%s" % (n))

        loop_bodys = []
        for n in loop_sequence:
            old_node = self._get_original_node(func_cfg, n)
            if old_node not in loop_bodys:
                old_node.is_loop = True
                loop_bodys.append(old_node)

        # print("\nLast sequence len: %d" % (len(loop_bodys)))
        # for n in loop_bodys:
        #     print("%s" % (n))

        return loop_bodys

    def _generate_loop_sequence(self, start_node, trace_path, branch_info, path_contain_branchs, loop_sequence):
        loop_sequence.extend(trace_path[start_node])
        s_node = start_node
        remain_branchs = path_contain_branchs[s_node]
        while remain_branchs:

            choose_branchs = self._choose_branch(remain_branchs, branch_info, loop_sequence)

            for cb in choose_branchs:
                self._generate_loop_sequence(cb, trace_path, branch_info, path_contain_branchs, loop_sequence)

                if cb in remain_branchs:
                    remain_branchs.remove(cb)

            # print("choose branch: %s" % (choose_branchs))
            # for remain_branch in remain_branchs:
            #     print("\nnode %s has branch %s" % (s_node, remain_branch))

            #     self._get_start_of_branch(remain_branch, remain_branchs, branch_info, loop_sequence)

        # print("\n Loop sequence:")
        # for n in loop_sequence:
        #     print("%s" % (n))

    def _get_start_of_branch(self, branch, current_branchs, branch_info, loop_sequence):

        analyzed_branch = {branch}
        branch_starts = []

        if branch in branch_info:
            start_nodes = branch_info[branch]

        else:
            start_nodes = []

        while start_nodes:
            new_start_nodes = []
            for bc in start_nodes:
                if bc in analyzed_branch:
                    continue

                analyzed_branch.add(bc)
                # if bc in loop_sequence:
                #     print("The branch %s has been done!" % (bc))

                # elif bc not in current_branchs:
                #     print("The branch %s is out of current tree." % (bc))

                if bc in current_branchs and bc not in loop_sequence:
                    branch_starts.append(bc)
                    if bc in branch_info:
                        ns = branch_info[bc]
                        new_start_nodes.extend(ns)

            start_nodes = new_start_nodes

        # for bc in branch_starts:
        #     print("  has start %s" % (bc))

        return branch_starts

    def _choose_branch(self, current_branchs, branch_info, loop_sequence):

        start_of_branch = {}
        choose_branchs = []
        for branch in current_branchs:

            branch_starts = self._get_start_of_branch(branch, current_branchs, branch_info, loop_sequence)

            start_of_branch[branch] = branch_starts

            if len(branch_starts) == 0:
                choose_branchs.append(branch)

        if len(choose_branchs) == 0:
            for branch, branch_starts in start_of_branch.items():
                for other_branch in branch_starts:
                    if branch in start_of_branch[other_branch]:
                        choose_branchs.append(branch)
                        choose_branchs.append(other_branch)

        return choose_branchs
