#!/usr/bin/env python

import json
from collections import defaultdict
from .block_node import IDABlock, ExternFuncNode, TmpNode, FuncNode
from .cfg_base import CFGBase
from .function_object import FunctionAttribute
from .call_graph import CallGraph

import logging
l = logging.getLogger("ida_process")
l.setLevel('INFO')


# process_data_info = {}
process_data_type = [
    'vPtr',
    'iCall',
    'funcPtr',
    'extPtr',
    'extData',
]


libc_addrs = {}


class IdaCFG(CFGBase):
    """
    Generate a complete control flow graph (CFG) for the analyzed binary.
    """
    def __init__(self):

        super(IdaCFG, self).__init__()

        self._ida_blocks = {}

        self._initialize_graph()

    def print_cfg_graph(self):
        for node in self.graph.nodes():
            print("IDA: %s" % (node))

    def find_function_start_ida_block(self, funcea):
        """
        Get start ida blocks from the ida cfg.
        """
        start_blocks = []
        s_block = self._ida_blocks.get(funcea)
        if s_block is None:
            return start_blocks

        start_blocks.append(s_block)

        for node in self.graph.nodes():
            if node.funcea == funcea and self.graph.in_degree(node) == 0 and node.addr != funcea:
                start_blocks.append(node)

        return start_blocks


class IDAProcess(object):
    """
    Generate a ida cfg and call graph by the block and jump info extracting from IDA Pro.
    """
    # _dataPath = "/home/iotse/angr-work/data/server/"
    _dataPath = "/home/iotse/angr-work/binaries/libwx_gtk2u_core/data/"

    def __init__(self, call_graph=None,
                 functions=None,
                 binary_cfg_info_path=None,
                 binary_block_info_path=None,
                 switch_info_path=None,
                 icall_info_path=None,
                 ijmp_info_path=None,
                 binary_bytes=None,
                 base_addr=0,
                 binary_name=None,
                 resolve_switch=False,
                 no_constuct=False):

        # super(CFGGenerate, self).__init__()

        self._nodes = {}
        self._ida_blocks = {}

        self.binary_bytes = binary_bytes
        self.base_addr = base_addr

        # Label the binary name. The main binary is labeled 'main', other is
        # lib name
        self.binary_name = binary_name

        self.resolve_switch = resolve_switch
        self.no_constuct = no_constuct

        self._vptrs_xref = defaultdict(list)
        self._icalls_xref = {}
        self._func_ptr_xref = defaultdict(list)
        self._extern_ptr_xref = defaultdict(list)
        self._extern_data_xref = defaultdict(list)

        self.functions_manager = {}

        self.icall_targets = defaultdict(dict)

        self.cg = call_graph if call_graph else CallGraph()
        self.ida_cfg = IdaCFG()

        self.cfg_record = json.load(open(binary_cfg_info_path, 'r'))
        self.blocks_record = json.load(open(binary_block_info_path, 'r'))

        self.icall_info_path = icall_info_path
        self.icall_info = {}

        self.ijmp_info = self.load_ijmp_info(ijmp_info_path)

        if self.resolve_switch:

            if switch_info_path:
                self.switch_record = json.load(open(switch_info_path, 'r'))
                self.functions = self.switch_record
                print(self.switch_record)

            else:
                self.no_constuct = True

        elif functions is None:
            self.functions = self.cfg_record

        else:
            self.functions = functions

        if not self.no_constuct:
            self._analyze()

    def _analyze(self):
        self.fast_generate_cfg_and_cg()

    def _initial_process_data_info(self, process_data_info):
        for _type in process_data_type:
            process_data_info[_type] = defaultdict(list)

    def read_binary_bytes(self, addr, size):
        if self.binary_bytes:
            return self.binary_bytes[addr:addr+size]
        else:
            return None

    def fast_generate_cfg_and_cg(self):
        """
        Fast generation of Control Flow Graph (CFG).
        """

        libc_names = defaultdict(list)

        function_count = 0
        for func_addr in self.functions:
            blocks = self.cfg_record[func_addr]['block']
            edges = self.cfg_record[func_addr]['jmp']
            function_name = self.cfg_record[func_addr]['name']
            funcea = int(func_addr, 16) + self.base_addr
            function_count += 1
            # print("Create cfg in function %s (%s) %d" % (func_addr, function_name, function_count))
            tail_calls = set()

            switch_targets = self.ijmp_info.get(funcea)
            # print("switch_targets: %s" % (switch_targets))

            for bb in blocks:
                nodes = []
                bb_start = bb[0]
                bb_end = bb[1]
                # print("Func: %x Block: (%x %x)" % (funcea, bb_start, bb_end))

                if bb_start == bb_end:
                    tail_calls.add(bb_start)
                    continue

                ida_block = IDABlock(bb_start, block_end=bb_end, funcea=funcea)
                self.ida_cfg._ida_blocks[bb_start] = ida_block
                self.ida_cfg.graph.add_node(ida_block)

            for edge in edges:
                src_addr, dst_addr = edge[0], edge[1]
                if dst_addr in tail_calls:
                    continue

                src_node = self.ida_cfg._ida_blocks[src_addr]
                dst_node = self.ida_cfg._ida_blocks[dst_addr]
                # print("src: %s, dst:%s" % (src_node, dst_node))

                kwargs = {'jumpkind': 'Boring'}
                self.ida_cfg.graph.add_edge(src_node, dst_node, **kwargs)

            if switch_targets:
                self._add_switch_edges(switch_targets)

            # Generate Call Graph.
            calls = self.cfg_record[func_addr]['call']

            # Add the function to the Call Graph.
            if funcea in self.cg._nodes:
                func_caller = self.cg._nodes[funcea]
                if func_caller.procedural_name is None:
                    func_caller.procedural_name = function_name

            else:
                # rebase_funcea = funcea + self.base_addr
                func_caller = FunctionAttribute(funcea, procedural_name=function_name, binary_name=self.binary_name)
                # print("create node: %s %s %s" % (func_caller, func_caller.procedural_name, id(func_caller)))
                self.cg._nodes[funcea] = func_caller
                self.cg.graph.add_node(func_caller)
                # print("add-new-node: %s" % (func_caller))

            for call_info in calls:
                bb_addr = call_info[0]
                callsite = call_info[1]
                target = call_info[2]
                # print("%x has call to %s" % (callsite, target))

                src_node = self.ida_cfg._ida_blocks.get(bb_addr)
                if src_node is None:
                    l.info("The have a block %x not been analyzed before, do it future." % (bb_addr))
                    continue

                src_node.callsites[callsite] = target

                if type(target) is not int:
                    target_name = str(target)
                    target_name_hash = hash(target_name)
                    # libc_names[target_name_hash].append(target_name)

                    if target_name_hash not in self.cg._nodes:
                        func_callee = FunctionAttribute(0, procedural_name=target_name, binary_name=self.binary_name)
                        # print("create node: %s" % (func_callee))
                        self.cg._nodes[target_name_hash] = func_callee
                    else:
                        func_callee = self.cg._nodes[target_name_hash]

                else:
                    rebase_target = target + self.base_addr
                    if rebase_target in self.cg._nodes:
                        func_callee = self.cg._nodes[rebase_target]

                    else:
                        func_callee = FunctionAttribute(rebase_target, binary_name=self.binary_name)
                        self.cg._nodes[rebase_target] = func_callee
                        # print("create node: %s %s %s" % (func_callee, func_callee.procedural_name, id(func_callee)))
                        # l.info("The callee %x not been added in functions, add it future." % (target))

                kwargs = {'jumpkind': 'Call'}
                self.cg.graph.add_edge(func_caller, func_callee, **kwargs)
                # print("%s -> %s" % (func_caller, func_callee))

    def add_icall_edge(self):

        for funcea, icall_targets in self.icall_info.items():
            function = self.cg.get_function_by_addr(funcea)
            print("Add-icall-edge: caller %s" % (function))
            if function is None:
                continue

            for callsite, targets in icall_targets.items():
                for target in targets:
                    callee = self.cg.get_function_by_addr(target)
                    print("Add-icall-edge: callee %s" % (callee))
                    if callee:
                        kwargs = {'jumpkind': 'Call'}
                        self.cg.graph.add_edge(function, callee, **kwargs)

    def _add_switch_edges(self, switch_targets):
        """
        Add switch jmp edges.
        """
        for block in self.ida_cfg._ida_blocks.values():
            for bb_addr, targets in switch_targets.items():
                if block.addr <= bb_addr < block.block_end:
                    for target in targets:
                        dst_node = self.ida_cfg._ida_blocks[target]
                        kwargs = {'jumpkind': 'Boring'}
                        self.ida_cfg.graph.add_edge(block, dst_node, **kwargs)

    def _add_block_data(self, block, data, data_type, data_info):
        if data_type not in data_info:
            data_info[data_type] = defaultdict(list)

        data_info[data_type][block].append(data)

    def collect_blocks_info(self):

        if self.resolve_switch:
            return self._collect_switch_info()

        else:
            return self._collect_block_info()

    def _collect_switch_info(self):

        blocks_data_info = {}
        for u_funcea in self.functions:
            switch_infos = self.switch_record.get(u_funcea)
            if switch_infos is None:
                continue

            funcea = int(u_funcea, 16)
            process_data_info = {}

            for block_addr, jmp_addr in switch_infos:
                print("switch: %x %x" % (block_addr, jmp_addr))
                ida_block = self.ida_cfg._ida_blocks.get(block_addr)
                t = (jmp_addr, None)
                self._add_block_data(ida_block, t, 'iJmp', process_data_info)

            blocks_data_info[funcea] = process_data_info
        return blocks_data_info

    def _collect_block_info(self):

        blocks_data_info = {}

        for u_funcea in self.functions:
            func_block_infos = self.blocks_record.get(u_funcea)
            if func_block_infos is None:
                continue

            funcea = int(u_funcea, 16)
            process_data_info = {}
            # self._initial_process_data_info(process_data_info)

            for u_bb_addr, block_infos in func_block_infos.items():

                print("block start %s (%s)" % (u_bb_addr, type(u_bb_addr)))
                print(block_infos)
                bb_addr = int(u_bb_addr, 10)
                # print("block %d %x" % (bb_addr, bb_addr))

                ida_block = self.ida_cfg._ida_blocks.get(bb_addr)
                if ida_block is None:
                    l.info("The block %x not in ida blocks!!!" % (bb_addr))
                    continue

                for bb_info in block_infos:
                    xref_addr, xref_data, xref_type = bb_info
                    if xref_type == 'xref_vptr':
                        t = (xref_addr, xref_data)
                        self._add_block_data(ida_block, t, 'vPtr', process_data_info)

                    elif xref_type == 'iCall':
                        t = (xref_addr, None)
                        ida_block.callsites[xref_addr] = 'iCall'
                        self._add_block_data(ida_block, t, 'iCall', process_data_info)

                    elif xref_type == 'func_ptr':
                        t = (xref_addr, xref_data)
                        self._add_block_data(ida_block, t, 'funcPtr', process_data_info)

                    elif xref_type == 'ext_ptr':
                        t = (xref_addr, str(xref_data))
                        # process_data_info['extPtr'][ida_block].append(t)
                        self._add_block_data(ida_block, t, 'extPtr', process_data_info)

                    elif xref_type == 'ext_data':
                        t = (xref_addr, str(xref_data))
                        self._add_block_data(ida_block, t, 'extData', process_data_info)

                    elif xref_type == 'data':
                        t = (xref_addr, xref_data)
                        self._add_block_data(ida_block, t, 'Data', process_data_info)

                    else:
                        l.info("Don't support the data type %s, add it future!" % (xref_type))

            if process_data_info:
                blocks_data_info[funcea] = process_data_info

        return blocks_data_info

    def pre_process_block_info(self):
        for data_type, data_info in process_data_info.items():
            if data_type == 'vPtr':
                for block, t in data_info.items():
                    self.process_vtable_ptr_xref(block, t)

            elif data_type == 'iCall':
                for block, t in data_info.items():
                    self.process_icall_xref(block, t)

            elif data_type == 'funcPtr':
                for block, t in data_info.items():
                    self.process_func_ptr_xref(block, t)

            elif data_type == 'extPtr':
                for block, t in data_info.items():
                    self.process_extern_ptr_xref(block, t)

            elif data_type == 'extData':
                for block, t in data_info.items():
                    self.process_extern_data_xref(block, t)

    def get_blocks_in_function(self, bb, blocks):
        blocks.append(bb)
        traversed_bbs = {bb}
        stack = [bb]
        while stack:
            b = stack.pop()
            edges = self.graph.out_edges(b, data=True)
            for _, dst, data in edges:
                if data['jumpkind'] == 'Call' or dst in traversed_bbs:
                    continue
                else:
                    traversed_bbs.add(dst)
                    blocks.append(dst)
                    stack.append(dst)

    def create_function_cfg(self, block):
        """
        :param block: the starting block of one function
        :return graph: a cfg graph of the function
        """
        traversed_blocks = []
        func_cfg = FuncCFG(block.addr)
        graph = func_cfg.graph
        graph.add_node(block)
        func_cfg._nodes[block.addr] = block
        traversed_blocks.append(block)
        stack = [block]
        while stack:
            node = stack.pop()
            func_cfg.pre_order_nodes.append(node)
            out_edges = self.graph.out_edges(node, data=True)
            if len(out_edges) == 0:
                func_cfg.exit_blocks.add(node)

            for _, succ_block, data in out_edges:
                if data['jumpkind'] in ['Call', 'I-Call']:
                    if len(out_edges) == 1:
                        func_cfg.exit_blocks.add(node)
                    continue

                graph.add_edge(node, succ_block)
                if succ_block not in traversed_blocks:
                    traversed_blocks.append(succ_block)
                    stack.append(succ_block)
                    func_cfg._nodes[succ_block.addr] = succ_block
        traversed_blocks.reverse()
        func_cfg.post_order_nodes = traversed_blocks
        return func_cfg

    def load_icall_info(self, icall_info=None):
        """
        Re-construct control flow graph.
        """
        if icall_info is None:
            if self.icall_info_path is None:
                return

            icall_info = json.load(open(self.icall_info_path, 'r'))

        if not isinstance(icall_info, dict):
            return

        for funcea, icall_targets in icall_info.items():
            if type(funcea) is str:
                funcea = int(funcea, 10)
            self.icall_info[funcea] = {}

            for addr, targets in icall_targets.items():
                if type(addr) is str:
                    addr = int(addr, 10)
                self.icall_info[funcea][addr] = targets
        # print("xpx: %s" % (self.icall_info))

    def load_ijmp_info(self, ijmp_info_path=None):
        """
        load switch jmp info.
        """
        if ijmp_info_path is None:
            return {}

        ijmp_info = json.load(open(ijmp_info_path, 'r'))

        if not isinstance(ijmp_info, dict):
            return {}

        switch_jmp_info = {}
        for funcea, ijmp_targets in ijmp_info.items():
            if type(funcea) is str:
                funcea = int(funcea, 10)
            switch_jmp_info[funcea] = {}

            for addr, targets in ijmp_targets.items():
                if type(addr) is str:
                    addr = int(addr, 10)
                switch_jmp_info[funcea][addr] = targets

        return switch_jmp_info


    # DEBUG
    def print_ida_cfg_graph(self):
        for n in self.ida_cfg.graph.nodes():
            print("Block node: %s" % (n))

    def print_cg_graph(self):
        print("Analyzed functions number: %d" % (len(self.cg.graph.nodes())))
        for n in self.cg.graph.nodes():
            print("CallGraph node: %s" % (n))
            print("pre - %s" % (list(self.cg.graph.predecessors(n))))
