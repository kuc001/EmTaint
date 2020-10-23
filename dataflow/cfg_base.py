#!/usr/bin/env python

import networkx

import logging
l = logging.getLogger("cfg_base")
l.setLevel('DEBUG')


class CFGBase(object):
    def __init__(self):

        # Initialization
        self._graph = None

        self._nodes = None

    def _initialize_graph(self):
        self._graph = networkx.DiGraph()

    @property
    def graph(self):
        return self._graph

    def get_predecessors(self, node):
        return self._graph.predecessors(node)

    def get_successors(self, node):
        return self._graph.successors(node)

    def get_root_nodes(self):
        """
        How to find root nodes in recursive functions well.
        (TODO)
        """
        root_nodes = set()
        analyzed_loops = []
        loops = networkx.simple_cycles(self._graph)
        # print self._graph.nodes()
        for n in self._graph.nodes():
            for loop in loops:
                if n in loop and n not in analyzed_loops:
                    root_nodes.add(n)
                    analyzed_loops.extend(loop)
                    break
            # print "in degree", self._graph.in_degree(n)
            if self._graph.in_degree(n) == 0:
                root_nodes.add(n)
        return root_nodes

    def find_loop_nodes(self):
        cycles = networkx.simple_cycles(self.graph)
        return cycles

    def get_node_by_addr(self, addr):
        if addr in self._nodes:
            return self._nodes[addr]
        else:
            l.debug("node addr %x" % (addr))
            raise KeyError

    def travel_graph(self, node, worklist, analyzed_nodes):
        worklist_set = set()
        stack = [node]
        worklist.append(node)
        worklist_set.add(node.addr)

        while stack:
            node = stack.pop()
            successor_nodes = self.graph.successors(node)
            for suc_node in successor_nodes:
                if suc_node.addr not in worklist_set \
                        and suc_node.addr not in analyzed_nodes:
                    stack.append(suc_node)
                    worklist.append(suc_node)
                    worklist_set.add(suc_node.addr)

    def worklist_update(self, node, worklist, analyzed_nodes):
        changed = False
        for n in self.graph.successors(node):
            if n.addr not in analyzed_nodes:
                self.travel_graph(n, worklist, analyzed_nodes)
                changed = True
        return changed

    def get_cycle_out_nodes(self, cycles):
        cycle_nodes = set()
        cycle_out_nodes = set()
        for loop in cycles:
            for node in loop.body_nodes:
                cycle_nodes.add(node)

        for node in cycle_nodes:
            succ_nodes = self.graph.successors(node)
            out_nodes = [n for n in succ_nodes if n not in cycle_nodes]
            for n in out_nodes:
                cycle_out_nodes.add(n)
        return cycle_out_nodes

    def get_succ_nodes_out_cycle(self, node, loop_nodes, analyzed_nodes):
        """
        If the succ nodes of node is in loop nodes, return a empty list.
        """
        stack = [node]
        traversed = []

        while stack:
            node = stack.pop()
            successor_nodes = self.graph.successors(node)
            for suc_node in successor_nodes:
                if (suc_node not in traversed and
                        suc_node.addr not in analyzed_nodes):
                    if suc_node in loop_nodes:
                        return []
                    stack.append(suc_node)
                    traversed.append(suc_node)
        return traversed

    def worklist_update_by_cycle(self, out_nodes, loops, work_list, analyzed_nodes):
        """
        :param out_nodes: the out nodes of the loop in loops.
        :param loops: a list, each element is a calss Loop
        """
        changed = False
        loop_nodes = []
        for loop in loops:
            loop_nodes.extend(loop.body_nodes)
        loop_nodes = list(set(loop_nodes))

        for n in out_nodes:
            if n.addr not in analyzed_nodes:
                new_nodes = self.get_succ_nodes_out_cycle(n, loop_nodes, analyzed_nodes)
                for n_node in new_nodes:
                    work_list.append(n_node)
                if len(new_nodes):
                    changed = True
        return changed
