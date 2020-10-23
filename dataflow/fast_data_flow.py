#!/usr/bin/ven python


import networkx
from .vex_process import EngineVEX
from .code_location import CodeLocation

from .errors import BlockActionsNone

import logging
l = logging.getLogger("fast_data_flow")
l.setLevel('INFO')


class LiveSims(object):

    def __init__(self, name, stype):

        self.name = name
        self.stype = stype

    def __eq__(self, other):
        return type(other) is LiveSims and self.name == other.name and self.stype == other.stype

    def __hash__(self):
        return hash(self.name) + hash(self.stype)

    def __repr__(self):
        return '<Live-Sim %s %s>' % (str(self.name), self.stype)


class FastDataFlow(EngineVEX):

    def __init__(self, project):

        super(FastDataFlow, self).__init__(project)


    def _add_use(self, new_use, loc, live_uses):
        if new_use in live_uses:
            live_uses[new_use].add(loc)
        else:
            live_uses[new_use] = {loc}

    def _lookup_uses(self, search, live_uses):

        for use in live_uses:
            name = use.name
            if search == name:
                return use

            elif type(search) is str and type(name) is tuple and search == name[0]:
                return use

    # TODO
    def _lookup_uses_v2(self, search, live_uses):
        """
        Find the definition of search in live_uses
        """
        for use in live_uses:
            name = use.name
            if s_var == name:
                return use

    def _backward_update(self, block, live_uses, live_uses_per_block, graph):

        pre_blocks = graph.predecessors(block)

        for pre_block in pre_blocks:
            # print("loop-pre: %s" % (pre_block))
            if pre_block.addr in live_uses_per_block:
                pre_live_uses = live_uses_per_block[pre_block.addr]

            else:
                pre_live_uses = {}
                live_uses_per_block[pre_block.addr] = pre_live_uses

            if len(pre_live_uses) == 0:
                for use, locs in live_uses.items():
                    pre_live_uses[use] = locs

            else:
                # print("merge-live-uses: %s %s" % (pre_block, block))
                self._merge_live_uses(pre_live_uses, live_uses)

    def _merge_live_uses(self, new_live_uses, old_live_uses):

        for old_use, locs in old_live_uses.items():
            # print("old-live-use: %s %s" % (old_use, locs))
            if old_use in new_live_uses:
                new_live_uses[old_use] |= locs

            else:
                new_live_uses[old_use] = locs

    def _check_inc_operations(self, block, live_uses_per_block):
        pass

    def process_block_in_forward(self, block):
        pass

    def process_block_in_backward(self, block, live_uses, ddg_graph, analyzed_special_addrs, is_loop=False):
        """
        This method only track 'reg', 'stack', 'direct mem access' variable.
        if trace mem access data, the name must be (base, offset).
        :param live_uses: is a dict, e.g. {LiveSims: set(location)}
        """
        live_defs = block.live_defs
        actions = block.actions
        if len(actions) == 0:
            return

        code_locations = block.code_locations
        ins_len = len(code_locations)
        for i in range(ins_len-1, -1, -1):

            code_location = code_locations[i]
            action = actions[code_location]
            action_type = action.action_type

            if action_type == 'p':
                put_reg = action.dst
                put_data = action.src
                put_data_alias = action.src_alias
                live_sim = self._lookup_uses(put_reg, live_uses)

                if type(put_data) is str:
                    put_data_at = live_defs[put_data]
                    if (put_data_at.action_type == 'wl' and
                            put_data_at.addr_value is None and
                            type(put_data_at.src_alias) is tuple and
                            type(put_data_at.src_alias[1][0]) is str and
                            'r' in put_data_at.src_alias[1][0]):
                        # print(10*"="+"%s" % (action))
                        # print(10*"="+"%s" % (put_data_at))
                        if code_location not in analyzed_special_addrs:
                            analyzed_special_addrs.add(code_location)
                            name = put_data_at.src_alias[1]
                            new_use = LiveSims(name, 'link')
                            self._add_use(new_use, code_location, live_uses)
                            # print("add-link: %s" % (new_use))

                if live_sim:
                    if live_sim.stype == 'link':
                        kwargs = {'stype': 'link', 'action': 'p', 'data': put_reg}
                    else:
                        kwargs = {'stype': 'reg', 'action': 'p', 'data': put_reg}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)
                        # print("ADD-g: %s %s" % (code_location, target_loc))

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    stype = live_sim.stype
                    if stype == 'reg':
                        new_use = LiveSims(put_data, 'reg')

                    else:
                        name = (put_data, live_sim.name[1])
                        new_use = LiveSims(name, 'mem')
                    # live_uses[new_use] = {code_location}
                    self._add_use(new_use, code_location, live_uses)

                if (is_loop and put_reg != self.sp_name and
                        type(put_data_alias) is tuple and
                        put_data_alias[0] in ['+', '-'] and
                        code_location not in analyzed_special_addrs):
                    analyzed_special_addrs.add(code_location)
                    add_use = LiveSims(put_data, 'reg')
                    if add_use in live_uses:
                        live_uses[add_use].add(code_location)

                    else:
                        live_uses[add_use] = {code_location}
                    # print("add-use: %s %s" % (add_use, code_location))

            elif action_type == 'w':
                wr_tmp = action.dst
                wr_data, wr_data_alias = action.src, action.src_alias
                live_sim = self._lookup_uses(wr_tmp, live_uses)

                if live_sim:
                    # kwargs = {'stype': live_sim.stype, 'action': 'w', 'data': wr_tmp}
                    kwargs = {'stype': 'reg', 'action': 'w', 'data': wr_tmp}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    if wr_data != self.gp_name:
                        stype = live_sim.stype
                        if stype == 'reg':
                            new_use = LiveSims(wr_data, 'reg')

                        else:
                            name = (wr_data, live_sim.name[1])
                            new_use = LiveSims(name, stype)

                        self._add_use(new_use, code_location, live_uses)
                        # print("update-use: %s %s" % (new_use, code_location))

            elif action_type == 'wo':
                # print("xx- %s" % (action))
                wr_tmp = action.dst
                wr_datas = action.src
                opnds = wr_datas[1]
                live_sim = self._lookup_uses(wr_tmp, live_uses)

                if live_sim:
                    # kwargs = {'stype': live_sim.stype, 'action': 'wo', 'data': wr_tmp}
                    kwargs = {'stype': 'reg', 'action': 'wo', 'data': wr_tmp}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)
                        # print("add-edge: %s -> %s %s" % (code_location, target_loc, kwargs))

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    stype = live_sim.stype
                    if stype == 'reg':
                        if type(opnds[0]) is str:
                            new_use = LiveSims(opnds[0], 'reg')
                            self._add_use(new_use, code_location, live_uses)
                            # print("update-use: %s %s" % (new_use, code_location))

                        if type(opnds[1]) is str:
                            new_use = LiveSims(opnds[1], 'reg')
                            self._add_use(new_use, code_location, live_uses)
                            # print("update-use: %s %s" % (new_use, code_location))

                    else:
                        if live_sim.name[1] == 0:
                            new_use = LiveSims(opnds, stype)
                            self._add_use(new_use, code_location, live_uses)
                        else:
                            l.debug("We ignore the mem data trace with add/sub operation!")

            elif action_type == 'wu':
                wr_tmp =action.dst
                wr_data = action.src
                live_sim = self._lookup_uses(wr_tmp, live_uses)

                if live_sim:
                    # kwargs = {'stype': live_sim.stype, 'action': 'wu', 'data': wr_tmp}
                    kwargs = {'stype': 'reg', 'action': 'wu', 'data': wr_tmp}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    stype = live_sim.stype
                    if stype == 'reg':
                        new_use = LiveSims(wr_data, 'reg')

                    else:
                        name = (wr_data, live_sim.name[1])
                        new_use = LiveSims(name, 'mem')
                    # live_uses[new_use] = {code_location}
                    self._add_use(new_use, code_location, live_uses)

            elif action_type == 'wl':
                wr_tmp = action.dst
                l_data = action.src_alias if action.src_alias else action.src
                live_sim = self._lookup_uses(wr_tmp, live_uses)

                if live_sim:
                    # kwargs = {'stype': live_sim.stype, 'action': 'wl', 'data': wr_tmp}
                    kwargs = {'stype': 'mem', 'action': 'wl', 'data': wr_tmp}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    stype = live_sim.stype
                    if stype == 'reg':
                        name = l_data[1] if type(l_data) is tuple else (l_data, 0)
                        if name[0] != self.gp_name:
                            new_use = LiveSims(name, 'mem')
                            self._add_use(new_use, code_location, live_uses)

                    else:
                        l.debug("We ignore the indirect mem access.")

            elif action_type == 's':
                data_alias = action.src_alias
                data = data_alias if type(data_alias) is str else action.src
                s_addr = action.dst_alias if action.dst_alias else action.dst
                addr = s_addr[1] if type(s_addr) is tuple else (s_addr, 0)

                live_sim = self._lookup_uses(addr, live_uses)

                if live_sim:
                    # kwargs = {'stype': live_sim.stype, 'action': 's', 'data': action.src}
                    kwargs = {'stype': 'mem', 'action': 's', 'data': action.src}
                    for target_loc in live_uses[live_sim]:
                        ddg_graph.add_edge(code_location, target_loc, **kwargs)

                    # pop use variable if we have found it's def.
                    live_uses.pop(live_sim)

                    new_use = LiveSims(data, 'reg')
                    # live_uses[new_use] = {code_location}
                    self._add_use(new_use, code_location, live_uses)

                if is_loop and type(data_alias) is tuple and data_alias[0] in ['+', '-']:
                    add_use = LiveSims(data, 'reg')
                    if add_use in live_uses:
                        live_uses[add_use].add(code_location)

                    else:
                        live_uses[add_use] = {code_location}
                    # print("add-use: %s" % (add_use))

            else:
                l.debug("Ignore action.")

    def execute_loop(self, loop, loop_execute_times=1):
        loop_sequence = loop.body_nodes
        loop_graph = loop.graph
        loop_len = len(loop_sequence)

        live_uses_per_block = {}
        analyzed_special_addrs = set()
        ddg_graph = networkx.DiGraph()

        for j in range(loop_execute_times):
            for i in range(loop_len-1, -1, -1):
                block = loop_sequence[i]
                block_addr = block.addr
                if block_addr in live_uses_per_block:
                    live_uses = live_uses_per_block[block_addr]

                else:
                    live_uses = {}
                    live_uses_per_block[block_addr] = live_uses

                if block.node_type in ['Call', 'iCall', 'Extern']:
                    self._pop_ret_live_sim(live_uses)

                # print("\nloop_block %s" % (block))
                # block.irsb.pp()
                # for sim, locs in live_uses.items():
                #     print(sim, locs)

                self.process_block_in_backward(block, live_uses, ddg_graph, analyzed_special_addrs, is_loop=True)

                live_uses_per_block[block_addr] = {}

                self._backward_update(block, live_uses, live_uses_per_block, loop_graph)

                # print("\nloop_block (A) %s" % (block))
                # for sim, locs in live_uses.items():
                #     print(sim, locs)

                # live_uses_per_block[block_addr] = {}

        # TEST
        # for node in ddg_graph.nodes():
        #     print("node: %s" % (node))

        # for src, dst, data in ddg_graph.edges(data=True):
        #     print(src, dst, data)

        return ddg_graph

    def _pop_ret_live_sim(self, live_uses):
        pop_uses = []
        for use in live_uses:
            use_name = use.name
            if (type(use_name) is str or type(use_name) is tuple) and self.ret_name in use_name:
                pop_uses.append(use)

        for u in pop_uses:
            # print("pop ret sim: %s" % (str(u.name)))
            live_uses.pop(u)

    def _get_loop_tmp(self, node, loop_graph):
        loop_tmps = set()
        for _, _, datas in loop_graph.in_edges(node, data=True):
            loop_tmps.add(datas['data'])

        return loop_tmps

    def _label_inc_in_action(self, function, inc_info):
        """
        Lable loop inc variable in block actions.
        """
        inc_blocks = {}
        loc_set = set()
        for loc in inc_info:
            block_addr = loc.block_addr
            block = function.get_block(block_addr)
            if block not in inc_blocks:
                inc_blocks[block] = []
            inc_blocks[block].append(loc)

        for block, inc_locs in inc_blocks.items():
            # print("Inc-block: %s" % (block))
            actions = block.actions
            live_defs = block.live_defs
            for loc in inc_locs:
                tmps = inc_info[loc]
                # print("inc-loc: %s" % (loc))
                action = actions[loc]
                if action.action_type == 'wo':
                    bases, offset = [], []
                    for opnd in action.src[1]:
                        if type(opnd) is str:
                            opnd_at = live_defs[opnd]
                            if opnd_at.action_type in ['w', 'p', 'wu']:
                                alias_opnd = live_defs[opnd].src
                            else:
                                alias_opnd = live_defs[opnd].dst

                            opnd_value = opnd_at.value
                            if type(opnd_value) is int and opnd_at.src_type in ['S', 'G']:
                                # print("Get stack or global addr inc: %x" % (opnd_value))
                                function.concrete_inc_addrs.add(opnd_value)

                        else:
                            alias_opnd = opnd

                        if opnd in tmps:
                            action.inc_flag += 1
                            bases.append((opnd, alias_opnd))
                        else:
                            offset.append((opnd, alias_opnd))

                    if len(bases) == 1 and len(offset) == 1:
                        action.inc_base = bases[0]
                        action.inc_offset = offset[0]
                        # print(action.inc_base, action.inc_offset)

                    elif len(bases) == 2:
                        action.inc_base = bases

    def _label_link_in_action(self, function, link_info):
        """
        Check whether have a link load instruction.
        """
        link_blocks = {}
        for loc in link_info:
            block_addr = loc.block_addr
            block = function.get_block(block_addr)
            if block not in link_blocks:
                link_blocks[block] = []
            link_blocks[block].append(loc)

        for block, link_locs in link_blocks.items():
            actions = block.actions
            live_defs = block.live_defs
            for loc in link_locs:
                at = actions[loc]
                if at.action_type != 'p':
                    continue
                put_src = at.src
                src_at = live_defs[put_src]
                if src_at.action_type == 'wl':
                    # print("Good, find link load %s" % (src_at))
                    src_at.link_flag = 1

    def label_inc_flag_in_loop(self, function, graph):

        inc_info = {}
        link_info = set()
        for subg in (networkx.induced_subgraph(graph, nodes).copy() for nodes in networkx.strongly_connected_components(graph)):
            if len(subg.nodes()) == 1:
                if len(list(subg.successors(list(subg.nodes())[0]))) == 0:
                    continue

            loop_locs = []
            for src, dst, data in subg.edges(data=True):
                # print("inc-edge: %s ->  %s %s" % (src, dst, data))
                if data['stype'] == 'reg' and data['action'] == 'wo':
                    loop_tmps = self._get_loop_tmp(src, subg)
                    inc_info[src] = loop_tmps

                elif data['stype'] == 'link' and data['action'] == 'p':
                    link_info.add(dst)

        self._label_inc_in_action(function, inc_info)

        self._label_link_in_action(function, link_info)
