#!/usr/bin/env python


import json
from collections import defaultdict
from .cfg_node import CFGBlock
from .cfg_base import CFGBase

import logging
l = logging.getLogger("generate_cfg")
l.setLevel('INFO')


class FunctionCFG(CFGBase):
    def __init__(self, addr, ida_object, project):

        super(FunctionCFG, self).__init__()

        self.addr = addr
        self.ida_object = ida_object
        self.proj = project

        self._nodes = {}
        self.callsites = {}
        self.pre_sequence_nodes = []
        self.callees = defaultdict(list)
        self.exit_blocks = set()

        self._initialize_graph()


    def get_node_by_addr(self, addr):
        return self._nodes[addr]

    def generate_function_cfg(self, function, start_ida_blocks):
        """
        :param function: the analyzed function
        :return graph: a cfg graph of the function
        """
        resolved_icalls = {}
        funcea = function.addr
        ida_cfg = self.ida_object.ida_cfg
        arch_flag = False
        if 'MIPS' in self.proj.arch.name:
            arch_flag = True

        traversed_ida_blocks = set()
        for s_block in start_ida_blocks:
            traversed_ida_blocks.add(s_block)

        stack = start_ida_blocks[:]

        icall_targets = self.ida_object.icall_info.get(funcea)

        while stack:
            ida_block = stack.pop()

            # print("Ida block %s" % (ida_block))

            self._translate_ida_block_to_irsb(ida_block, funcea)

            jumpkind, exit_node = self._add_irsb_node_to_cfg(ida_block, icall_targets, resolved_icalls)
            self.graph.add_node(exit_node)

            # print("%s contain %s" % (ida_block, ida_block.contain_blocks))
            # print("exit node: %s" % (exit_node))

            out_edges = ida_cfg.graph.out_edges(ida_block)

            jmp_block = None
            if arch_flag and len(out_edges) == 2:
                jmp_block, jmp_target = self._check_jump_block(exit_node)
                # print("Get- %s %s" % (jmp_block, jmp_target))

            if len(out_edges) == 0:
                # print("The ida block %s is the exit block in function %x" % (ida_block, funcea))
                self.graph.add_node(exit_node)
                if exit_node.node_type in ['Call', 'iCall', 'Extern']:
                    tmp_exit_node = CFGBlock(exit_node.addr+1, self, func_addr=self.addr, node_type='Boring')
                    self._nodes[tmp_exit_node.addr] = tmp_exit_node
                    self.exit_blocks.add(tmp_exit_node)
                    kwargs = {'jumpkind': 'Ret'}
                    self.graph.add_edge(exit_node, tmp_exit_node, **kwargs)
                else:
                    self.exit_blocks.add(exit_node)
                # print("CFG-exit-node: %s" % (exit_node))

            if jumpkind == 'call' and len(out_edges) == 0:
                continue

            else:
                for _, succ_ida_block in out_edges:
                    # print("%s has succ ida block: %s" % (ida_block, succ_ida_block))
                    self._translate_ida_block_to_irsb(succ_ida_block, funcea)

                    if succ_ida_block not in traversed_ida_blocks:
                        stack.append(succ_ida_block)
                        traversed_ida_blocks.add(succ_ida_block)

                if arch_flag and jmp_block:
                    self._process_special_node(exit_node, jmp_block, jmp_target, out_edges, jumpkind)

                else:
                    for _, succ_ida_block in out_edges:
                        start_node = succ_ida_block.contain_blocks[0]

                        if jumpkind == 'call':
                            kwargs = {'jumpkind': 'Ret'}
                            exit_node.jumpkind = 'Ret'
                            self.graph.add_edge(exit_node, start_node, **kwargs)

                        elif jumpkind == 'jmp':
                            kwargs = {'jumpkind': 'Boring'}
                            exit_node.jumpkind = 'Boring'
                            self.graph.add_edge(exit_node, start_node, **kwargs)

        if len(resolved_icalls):
            self._add_icall_target_node(resolved_icalls)
            # print("Found resolved icalls: %s" % (resolved_icalls))

    def _block_sclicing(self, block_start, block_end):
        irsbs = []
        block_size = block_end - block_start
        if block_size == 0:
            return [self.state.block(block_start).vex]

        irsb_size = 0
        slicing_addr = block_start
        slicing_size = block_size
        # print("block_sclicing: %x %d" % (block_start, block_size))
        while irsb_size < block_size:
            if slicing_size > 5000:
                slicing_size = 5000

            try:
                insn_bytes = self.ida_object.read_binary_bytes(slicing_addr, slicing_size)
                # print("insn_bytes: \n%s" % (insn_bytes))
                # print("addr: %x, size: %d" % (slicing_addr, slicing_size))
                irsb = self.proj.factory.block(slicing_addr, size=slicing_size, insn_bytes=insn_bytes).vex

                if irsb.instructions == 0 and 'MIPS' in self.proj.arch.name:
                    slicing_size += 4
                    irsb = self.proj.factory.block(slicing_addr, size=slicing_size, insn_bytes=insn_bytes).vex

                if irsb.jumpkind == 'Ijk_NoDecode':
                    raise Exception("No decode!")

                # irsb.pp()
                irsbs.append(irsb)
                irsb_size += irsb.size
                slicing_addr = block_start + irsb_size
                slicing_size = block_size - irsb_size

            except:
                l.info("We couldn't translate addr %x to vex!" % (slicing_addr))
                break

        return irsbs

    def _translate_ida_block_to_irsb(self, ida_block, funcea):
        """
        Translate a ida block to one or more irsb block.
        """
        if ida_block.contain_blocks:
            # l.info("The ida block %s has been translate to irsb. " % (ida_block))
            return

        base_addr = self.ida_object.base_addr
        bb_start, bb_end = ida_block.addr+base_addr, ida_block.block_end+base_addr
        irsbs = self._block_sclicing(bb_start, bb_end)

        if len(irsbs) == 0:
            l.info("IDA block %s has no irsb, error." % (ida_block))
            # exit(0)

        for irsb in irsbs:
            irsb_addr = irsb.addr
            block_node = CFGBlock(irsb_addr, self, node_type='Boring')
            block_node.irsb = irsb
            block_node.func_addr = funcea
            block_node.end = irsb_addr + irsb.size
            self._nodes[irsb_addr] = block_node
            ida_block.contain_blocks.append(block_node)
            # irsb.pp()

    def _add_irsb_node_to_cfg(self, ida_block, icall_targets, resolved_icalls):
        exit_nodes = []
        callsites = ida_block.callsites
        nodes = ida_block.contain_blocks
        nodes_len = len(nodes)

        for i, irsb_node in enumerate(nodes):
            callsite_addr, target = self._check_has_caller(irsb_node, callsites)
            old_addr = callsite_addr

            if callsite_addr:
                callsite_node = irsb_node
                ret_node = nodes[i+1] if i < nodes_len-1 else None

                # Special, the will be a block has only one instruction (call),
                # then we inc the callsite addr.
                if callsite_addr in self._nodes:
                    callsite_addr += 1

                if isinstance(target, int):
                    rebase_target = target + self.ida_object.base_addr
                    target_node = CFGBlock(callsite_addr, self, target=rebase_target, func_addr=self.addr, node_type='Call')
                    self.callees[rebase_target].append(target_node)
                    self.callsites[target_node.__hash__()] = target_node

                elif target == 'iCall':
                    target_node = CFGBlock(callsite_addr, self, target='iCall', func_addr=self.addr, node_type='iCall')
                    if icall_targets and old_addr in icall_targets:
                        targets = icall_targets[old_addr]
                        resolved_icalls[target_node] = targets

                else:
                    target_name = str(target)
                    target_node = CFGBlock(callsite_addr, self, target=target_name, func_addr=self.addr, node_type='Extern')
                    self.callees[target_name].append(target_node)

                self._nodes[callsite_addr] = target_node

                kwargs = {'jumpkind': 'Ijk_Call'}
                callsite_node.jumpkind = 'Ijk_Call'
                self.graph.add_edge(callsite_node, target_node, **kwargs)
                callsite_node.has_callsite = 1

                if ret_node is None:
                    return ('call', target_node)

                else:
                    kwargs = {'jumpkind': 'Ret'}
                    target_node.jumpkind = 'Ret'
                    self.graph.add_edge(target_node, ret_node, **kwargs)

            else:
                if i < nodes_len-1:
                    kwargs = {'jumpkind': 'Boring'}
                    irsb_node.jumpkind = 'Boring'
                    self.graph.add_edge(irsb_node, nodes[i+1])

                else:
                    return ('jmp', irsb_node)

    def _add_icall_target_node(self, resolved_icalls):
        for icall_node, targets in resolved_icalls.items():
            callsite_addr = icall_node.addr
            pre_nodes = list(icall_node.predecessors)
            succ_nodes = list(icall_node.successors)

            if len(targets):
                icall_node.icall_flag = 1
            #     for pre_node in pre_nodes:
            #         self.graph.remove_edge(pre_node, icall_node)
            #     for succ_node in succ_nodes:
            #         self.graph.remove_edge(icall_node, succ_node)
            #     self.graph.add_node(icall_node)
            #     # self.graph.remove_node(icall_node)

            for target in targets:
                if type(target) is str:
                    target_name = str(target)
                    target_node = CFGBlock(callsite_addr, self, target=target_name, func_addr=self.addr, node_type='Extern')
                    self.callees[target_name].append(target_node)

                else:
                    rebase_target = target + self.ida_object.base_addr
                    target_node = CFGBlock(callsite_addr, self, target=rebase_target, func_addr=self.addr, node_type='iCall')
                    self.callees[rebase_target].append(target_node)
                    self.callsites[target_node.__hash__()] = target_node

                for pre_node in pre_nodes:
                    kwargs = {'jumpkind': 'Ijk_Call'}
                    self.graph.add_edge(pre_node, target_node, **kwargs)
                    pre_node.has_callsite = 1
                    print("Add-icll-target: %s" % (target_node))

                for succ_node in succ_nodes:
                    kwargs = {'jumpkind': 'Ret'}
                    self.graph.add_edge(target_node, succ_node, **kwargs)

    def _get_callsite_and_ret_node(self, call_addr, nodes):
        _len = len(nodes)
        callsite_node, ret_node = None, None
        for i, node in enumerate(nodes):
            if node.addr <= call_addr < node.end:
                callsite_node = node
                if i < _len - 1:
                    ret_node = nodes[i+1]

                else:
                    ret_node = None

                break

        return callsite_node, ret_node

    def _check_has_caller(self, irsb_node, callsites):

        for addr, target in callsites.items():

            rebase_addr = addr+self.ida_object.base_addr
            if irsb_node.addr <= rebase_addr < irsb_node.end:
                return rebase_addr, target

        return None, None

    def print_cfg(self):
        for node in self.graph.nodes():
            print("Debug: %s" % (node))

    def print_cfg_edges(self):
        for src, dst in self.graph.edges():
            print("%s -> %s" % (src, dst))

    def _add_edge(self, src, dst, jumpkind):
        """
        Add block to cfg_graph.
        """
        if jumpkind == 'call':
            kwargs = {'jumpkind': 'Ret'}
            src.jumpkind = 'Ret'
            self.graph.add_edge(src, dst, **kwargs)

        elif jumpkind == 'jmp':
            kwargs = {'jumpkind': 'Boring'}
            src.jumpkind = 'Boring'
            self.graph.add_edge(src, dst, **kwargs)

    def find_all_predecessors(self, addr):
        node = self._nodes[addr]

        traversed_nodes = set()
        traversed_nodes.add(node)

        stack = [node]
        while stack:
            node = stack.pop()
            pre_nodes = self.graph.predecessors(node)
            for pre_node in pre_nodes:
                if pre_node not in traversed_nodes:
                    stack.append(pre_node)
                    traversed_nodes.add(pre_node)

        for n in traversed_nodes:
            print("%s" % (n))

        return traversed_nodes

    def get_special_exit_block(self):
        """
        For the non-returned function, how to get its exit block.
        Especially for the loop exit, e.g. vsftpd 0x40d330.
        """
        last_block = self.pre_sequence_nodes[-1]
        if last_block.is_loop:
            pre_blocks = list(self.graph.predecessors(last_block))
            # print("psu-test: xxx %s" % (pre_blocks))
            if len(pre_blocks) == 1:
                return pre_blocks[0]
            for pre_block in pre_blocks:
                if pre_block.is_loop:
                    return pre_block

    def create_block(self, addr, bytes_len, funcea):
        """
        Create a cfg block with irsb.
        """
        insn_bytes = self.ida_object.read_binary_bytes(addr, bytes_len)
        irsb = self.proj.factory.block(addr, size=bytes_len, insn_bytes=insn_bytes).vex
        # irsb.pp()

        block_node = CFGBlock(addr+1, self, node_type='Boring')
        block_node.irsb = irsb
        block_node.func_addr = funcea
        block_node.end = addr + irsb.size
        self._nodes[addr+1] = block_node

        return block_node

    def _check_jump_block(self, block):
        # print("Mips-jump-block: %s" % (block))
        addr = block.addr
        irsb = block.irsb
        last_stmt = irsb.statements[-1]
        if last_stmt.tag is 'Ist_Exit':
            return None, None

        # irsb.pp()
        new_block, target = None, None
        bytes_len = 0
        stmts = irsb.statements
        for index, stmt in enumerate(stmts):
            if stmt.tag is 'Ist_IMark':
                bytes_len += stmt.len
            elif stmt.tag is 'Ist_Exit' and 'Ico' in stmt.dst.tag:
                target = stmt.dst.value
                # print("  -> %x" % (target))
                new_block = self.create_block(addr, bytes_len, block.func_addr)
        return new_block, target

    def _process_special_node(self, exit_block, jmp_block, jmp_target, out_edges, jumpkind):
        """
        In Mips, some block has jmp instruction in block's middle.
            85 IRSB {
            86    t0:Ity_I1 t1:Ity_I1 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64
            87
            88    00 | ------ IMark(0x12005c5ac, 4, 0) ------
            89    01 | t2 = GET:I64(v0)
            90    02 | t1 = CmpNE64(t2,0x0000000000000000)
            91    03 | if (t1) { PUT(pc) = 0x12005c5b4; Ijk_Boring }
            92    04 | ------ IMark(0x12005c5b0, 4, 0) ------
            93    05 | t4 = GET:I64(sp)
            94    06 | t3 = Add64(t4,0x0000000000000138)
            95    07 | PUT(a0) = t3
            96    NEXT: PUT(pc) = 0x000000012005c5d0; Ijk_Boring
            97 }
        """
        funcea = exit_block.func_addr
        for pre_block, _, data in self.graph.in_edges(exit_block, data=True):
            # print("pre_block %s %s" % (pre_block, data))
            self.graph.add_edge(pre_block, jmp_block, **data)

        jmp_succ_bock = None
        succ_blocks = []
        for _, succ_ida_block in out_edges:
            start_node = succ_ida_block.contain_blocks[0]
            if start_node.addr == jmp_target:
                jmp_succ_bock = start_node

            else:
                succ_blocks.append(start_node)

        if jmp_succ_bock:
            # print("Add-edge: %s -> %s" % (jmp_block, jmp_succ_bock))
            self._add_edge(jmp_block, jmp_succ_bock, jumpkind)

        for succ_block in succ_blocks:
            self._add_edge(exit_block, succ_block, jumpkind)

    def get_start_nodes(self):
        """
        Get start nodes in cfg.
        """
        start_nodes = []
        for n in self.graph.nodes():
            if self.graph.in_degree(n) == 0 and n.addr != self.addr:
                start_nodes.append(n)

        s_node = self.get_node_by_addr(self.addr)
        start_nodes.append(s_node)

        return start_nodes
