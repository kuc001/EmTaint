#!/usr/bin/env python

import pyvex
import claripy
import networkx
from collections import defaultdict
from .variable_expression import VarExpr, TraceExpr, SimAction, Sim
# from .vex.statements import translate_stmt
from .code_location import CodeLocation

from .parse_ast import *

import logging
l = logging.getLogger("parse_binary")
l.setLevel('INFO')


choose_register = True
do_forward_store_redefine = False
do_forward_concrete_load = False

loop_inc_tmps_record = defaultdict(int)
loop_inc_locations = defaultdict(set)


class BinaryParser(object):
    def __init__(self, project, binary_bytes=None):

        self.proj = project
        self.binary_bytes = binary_bytes

        self.state = self.proj.factory.blank_state()

        # Initialize some property of arch
        self.arch_bits = self.proj.arch.bits
        self.ret_offset = self.proj.arch.ret_offset
        self.sp_offset = self.proj.arch.sp_offset
        self.bp_offset = self.proj.arch.bp_offset
        # self.max_offset = self.proj.arch.registers['cc_op'][0]
        self.arguments = self.proj.arch.argument_registers
        self.argument_vars = ['r%d' % o for o in self.arguments]

        self.sp_name = 'r%d' % (self.sp_offset)
        self.bp_name = 'r%d' % (self.bp_offset)

        # These ops are the claripy operators.
        self.add_ops = ['__add__']
        # self.ignore_ops = ['Extract', 'Concat', 'ZeroExt', 'SignExt']
        self.ignore_ops = []
        self.shift_ops = ['__lshift__']
        # self.shift_ops = ['__lshift__', '__rshift__']
        self.simplify_ops = ['__add__', '__sub__', '__mul__']
        self.concrete_ops = claripy.operations.leaf_operations_concrete

        # These ops are the type 'pyvex.expr.Binop'.
        self.complex_binops = []
        self.simple_binops = []
        self.ignore_binops = ['Iop_Sar64', 'Iop_Shr64']
        self.add_binops = ['Iop_Add64']
        self.sub_binops = ['Iop_Sub64']

        # Some insignificant symbol ast.
        self.insignificant_symbol = claripy.BVS("s", self.arch_bits, explicit_name=True)

        self.ignore_regs = self._get_ignore_regs()

    def _get_ignore_regs(self):

        ignore_registers = ['cc_op', 'cc_dep1', 'cc_dep2', 'cc_ndep', 'rip', 'ip']

        ignore_reg_offsets = []
        for reg in ignore_registers:
            if reg not in self.proj.arch.registers:
                continue
            reg_offset = self.proj.arch.registers[reg][0]
            ignore_reg_offsets.append(reg_offset)

        return ignore_reg_offsets

    def read_binary_bytes(self, addr, size):
        if self.binary_bytes:
            return self.binary_bytes[addr:addr+size]
        else:
            return None

    def block_sclicing(self, block_start, block_end):
        irsbs = []
        block_size = block_end - block_start
        if block_size == 0:
            return [self.state.block(block_start).vex]

        irsb_size = 0
        slicing_addr = block_start
        slicing_size = block_size
        print("block_sclicing: %x %d" % (block_start, block_size))
        while irsb_size < block_size:
            if slicing_size > 5000:
                slicing_size = 5000

            try:
                insn_bytes = self.read_binary_bytes(slicing_addr, slicing_size)
                print("insn_bytes: \n%s" % (insn_bytes))
                irsb = self.state.block(slicing_addr, size=slicing_size, insn_bytes=insn_bytes).vex

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

    def get_icall_trace_tmp(self, block):
        """
        Get the indirect callsite target's tmp in VEX
            call qword ptr [rax+10]
            NEXT: PUT(rip) = t3; Ijk_Call
        """
        irsb = block.irsb
        for stmt in irsb.statements:
            if type(irsb.next) is pyvex.expr.RdTmp:
                trace_tmp = 't%d' % irsb.next.tmp
                return trace_tmp

    def get_icall_ptr_info(self, block):
        tmp = self.get_icall_trace_tmp(block)
        if tmp is None:
            return None
        return claripy.BVS(tmp, self.arch_bits, explicit_name=True)

    def translate_sym_to_expr(self, sym):
        var = claripy.BVS(sym, self.arch_bits, explicit_name=True)
        expr = VarExpr(var)
        return expr

    def get_icall_ptr_expr(self, block):
        tmp = self.get_icall_trace_tmp(block)
        if tmp is None:
            return None

        expr = self.translate_sym_to_expr(tmp)
        expr.pattern = 'Cptr'
        expr.get_trace_variable()
        stmts_length = len(block.irsb.statements)
        code_location = CodeLocation(block.addr, stmts_length)
        expr.location = code_location
        expr.alias_id = code_location.__hash__()
        expr.source = code_location
        expr.trace_dir = 'B'
        trace_expr = TraceExpr(expr, stmts_length)
        return trace_expr

    def find_save_vptr_expr(self, block, index):
        vptr_exprs = []
        irsb = block.irsb
        block_addr = block.addr
        stmts = irsb.statements
        for stmt_idx, stmt in enumerate(stmts):
            if stmt_idx <= index:
                continue
            if (isinstance(stmt, pyvex.stmt.Put) and
                    isinstance(stmt.data, pyvex.expr.Const)):
                value = stmt.data.con.value
                if value in block.vtable_addrs:
                    src_data = claripy.BVV(value, self.arch_bits)
                    var = 'r%d' % (stmt.offset)
                    dst_data = claripy.BVS(var, self.arch_bits, explicit_name=True)
                    vptr_expr = VarExpr(dst_data)
                    vptr_expr.value = src_data
                    # vptr_expr._index = stmt_idx
                    code_location = CodeLocation(block_addr, stmt_idx)
                    vptr_expr.location = code_location
                    vptr_expr.alias_id = code_location.__hash__()
                    vptr_expr.source = code_location
                    trace_expr = TraceExpr(vptr_expr, stmt_idx)
                    vptr_exprs.append(trace_expr)

            elif (isinstance(stmt, pyvex.stmt.Store) and
                    isinstance(stmt.data, pyvex.expr.Const)):
                value = stmt.data.con.value
                if value in block.vtable_addrs:
                    src_data = claripy.BVV(value, self.arch_bits)
                    if isinstance(stmt.addr, pyvex.expr.RdTmp):
                        var = 't%d' % (stmt.addr.tmp)
                        sym_addr = claripy.BVS(var, self.arch_bits, explicit_name=True)
                        dst_data = claripy.Load(sym_addr, self.arch_bits)
                    elif isinstance(stmt.addr, pyvex.expr.Const):
                        value = stmt.addr.con.value
                        value_ast = claripy.BVV(value, self.arch_bits)
                        dst_data = claripy.Load(value_ast, self.arch_bits)
                    else:
                        l.info("Some error while finding save ptr!")

                    vptr_expr = VarExpr(dst_data)
                    vptr_expr.value = src_data
                    # vptr_expr._index = stmt_idx
                    code_location = CodeLocation(block_addr, stmt_idx)
                    vptr_expr.location = code_location
                    vptr_expr.alias_id = code_location.__hash__()
                    vptr_expr.source = code_location
                    trace_expr = TraceExpr(vptr_expr, stmt_idx)
                    vptr_exprs.append(trace_expr)
        return vptr_exprs

    def _find_constant_ptr_xref(self, stmts, index, unsolve_ptrs):
        result = []
        for stmt_idx, stmt in enumerate(stmts[index:]):
            true_idx = stmt_idx + index
            if (isinstance(stmt, pyvex.stmt.Put) and
                    isinstance(stmt.data, pyvex.expr.Const)):
                value = stmt.data.con.value
                if value in unsolve_ptrs:
                    src_data = claripy.BVV(value, self.arch_bits)
                    var = 'r%d' % (stmt.offset)
                    dst_data = claripy.BVS(var, self.arch_bits, explicit_name=True)
                    t = (true_idx, src_data, dst_data)
                    result.append(t)

            elif (isinstance(stmt, pyvex.stmt.Store) and
                    isinstance(stmt.data, pyvex.expr.Const)):
                value = stmt.data.con.value
                if value in unsolve_ptrs:
                    src_data = claripy.BVV(value, self.arch_bits)
                    if isinstance(stmt.addr, pyvex.expr.RdTmp):
                        var = 't%d' % (stmt.addr.tmp)
                        sym_addr = claripy.BVS(var, self.arch_bits, explicit_name=True)
                        dst_data = claripy.Store(sym_addr, self.arch_bits)
                    elif isinstance(stmt.addr, pyvex.expr.Const):
                        value = stmt.addr.con.value
                        value_ast = claripy.BVV(value, self.arch_bits)
                        dst_data = claripy.Store(value_ast, self.arch_bits)
                    else:
                        l.info("The stmt %s is special, do it future!" % (stmt))
                        continue

                    t = (true_idx, src_data, dst_data)
                    result.append(t)
        return result

    def _find_load_constant(self, stmts, index, ptr):
        result = []
        for stmt_idx, stmt in enumerate(stmts[index:]):
            if stmt.tag is 'Ist_IMark':
                return result

            true_idx = stmt_idx + index
            if (isinstance(stmt, pyvex.stmt.WrTmp) and
                    isinstance(stmt.data, pyvex.expr.Load)):
                translate_stmt(stmt, self.state)
                src_data = self.state.scratch.tmp_expr(stmt.tmp)
                var = 't%d' % (stmt.tmp)
                if src_data.concrete:
                    if src_data.args[0] == ptr:
                        dst_data = claripy.BVS(var, self.arch_bits, explicit_name=True)
                        t = (true_idx, src_data, dst_data)
                        result.append(t)
                        break
        return result

    def get_ptr_xref_info(self, block, ptr_info):
        collect_info = []
        collect_indexs = []
        solve_xrefs = []
        unsolve_ptrs = set()

        irsb = block.irsb
        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv

        block_ptrs = {}
        for xref_addr, ptr in ptr_info:
            block_ptrs[xref_addr] = ptr

        stmts = irsb.statements
        for i, stmt in enumerate(stmts):
            if len(block_ptrs) == 0:
                break

            if stmt.tag is 'Ist_IMark' and stmt.addr in block_ptrs:
                collect_indexs.append(i)
                ptr = block_ptrs[stmt.addr]
                block_ptrs.pop(stmt.addr)
                result = self._find_load_constant(stmts, i+1, ptr)
                if result:
                    collect_info.extend(result)
                    solve_xrefs.append(stmt.addr)

        for xref_addr, ptr in ptr_info:
            if xref_addr not in solve_xrefs:
                unsolve_ptrs.add(ptr)

        if len(unsolve_ptrs):
            index = min(collect_indexs)
            result = self._find_constant_ptr_xref(stmts, index+1, unsolve_ptrs)
            collect_info.extend(result)

        return collect_info

    def get_save_vptr_index(self, irsb, addr):
        for i, stmt in enumerate(irsb.statements):
            if (isinstance(stmt, pyvex.IRStmt.IMark) and stmt.addr == addr):
                return i

    def _find_put_def(self, stmt, expr, code_location, sp_tmp):
        """
        Find the definition of writing register.
        example: 'PUT(rax) = t8'
        """
        changed_trace_exprs = []
        if stmt.offset >= self.max_offset:
            return []

        sp_reg = 'r%d' % self.sp_offset
        put_reg = 'r%d' % stmt.offset

        if put_reg != sp_reg and put_reg in expr.expr.trace_vars:
            # print("expr %s has vars %s" % (expr, expr.expr.trace_vars))
            # print("Find put def %s" % (stmt))
            translate_stmt(stmt, self.state)
            src_data = self.state.registers.load(stmt.offset)
            new_expr = expr.replace(put_reg, src_data)
            new_expr.get_trace_variable(expr.expr.killed_vars)
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx

            for v in new_expr.expr.trace_vars:
                if sp_tmp and v == 't%d' % sp_tmp:
                    new_expr.simple_replace(v, sp_reg)
                    new_expr.get_trace_variable(expr.expr.killed_vars)
                    break

            changed_trace_exprs.append(new_expr)
        return changed_trace_exprs

    def _search_load_tmp(self, irsb, stmt, code_location, sp_tmp):
        load_addr_tmp = stmt.data.addr.tmp
        stmts = irsb.statements
        current_idx = code_location.stmt_idx
        for idx in range(current_idx-1, -1, -1):
            pre_stmt = stmts[idx]
            if (isinstance(pre_stmt, pyvex.stmt.WrTmp) and
                    not isinstance(pre_stmt.data, pyvex.expr.ITE)):
                if pre_stmt.tmp == load_addr_tmp:
                    translate_stmt(pre_stmt, self.state)
                    load_addr = self.state.scratch.tmp_expr(pre_stmt.tmp)
                    sp_tmp_name = 't%d' % (sp_tmp)
                    if sp_tmp_name in load_addr.variables:
                        return load_addr
                    break
        return None

    def _parse_unop_expr(self, stmt):
        if len(stmt.data.args) != 1:
            l.info("stmt: %s, do it future!" % (stmt))
            return

        arg_stmt = stmt.data.args[0]
        if isinstance(arg_stmt, pyvex.expr.RdTmp):
            rdtmp = 't%d' % (arg_stmt.tmp)
            return rdtmp

    def _find_wrtmp_def(self, irsb, stmt, expr, code_location, sp_tmp):
        """
        Finding a tmp (txx) definition.
        example t2 = Get(rdi) or t2 = LDle(t4) or t2 = Add(t5, 0x24)
        """
        new_exprs = []
        sp_reg = 'r%d' % self.sp_offset
        wrtmp = 't%d' % stmt.tmp
        _dir = 'N'
        use_datas = []

        if sp_tmp and stmt.tmp == sp_tmp:
            return []

        if wrtmp in expr.expr.trace_vars:
            # print("Find wrtmp def %s" % (stmt))
            if (isinstance(stmt.data, pyvex.expr.ITE)):
                # _type = stmt.data.result_type(irsb.tyenv)
                # data_size = get_type_size(_type)
                data_size = self.arch_bits
                true_expr = stmt.data.iftrue
                false_expr = stmt.data.iffalse
                # print("ture:%s false:%s" % (true_expr, false_expr))
                if isinstance(true_expr, pyvex.expr.RdTmp):
                    src_data1 = claripy.BVS('t%d' % true_expr.tmp, data_size, explicit_name=True)
                    use_datas.append(src_data1)

                elif isinstance(true_expr, pyvex.expr.Const):
                    value = true_expr.con.value
                    src_data1 = claripy.BVV(value, data_size)

                if isinstance(false_expr, pyvex.expr.RdTmp):
                    src_data2 = claripy.BVS('t%d' % false_expr.tmp, data_size, explicit_name=True)
                    use_datas.append(src_data2)

                elif isinstance(false_expr, pyvex.expr.Const):
                    value = false_expr.con.value
                    src_data2 = claripy.BVV(value, data_size)

            elif (isinstance(stmt.data, pyvex.expr.Load) and
                    isinstance(stmt.data.addr, pyvex.expr.RdTmp)):
                translate_stmt(stmt, self.state)
                new_data = self.state.scratch.tmp_expr(stmt.tmp)
                if sp_tmp is not None:
                    load_addr = self._search_load_tmp(irsb, stmt, code_location, sp_tmp)
                    if load_addr is not None:
                        new_data = claripy.Load(load_addr, self.arch_bits)
                        _dir = 'B'

                use_datas.append(new_data)

            else:
                # TODO
                # if the varialbe is rbx = Add(rsp, 0x40)
                if isinstance(stmt.data, pyvex.expr.Unop):
                    data_tmp = self._parse_unop_expr(stmt)
                    if data_tmp:
                        new_data = claripy.BVS(data_tmp, self.arch_bits, explicit_name=True)
                        use_datas.append(new_data)

                else:
                    translate_stmt(stmt, self.state)
                    new_data = self.state.scratch.tmp_expr(stmt.tmp)
                    # print("read data %s from %d" % (new_data, stmt.tmp))
                    if new_data.op in self.ignore_ops:
                        new_data = claripy.BVS('u', self.arch_bits, explicit_name=True)
                    elif new_data.op in self.shift_ops:
                        # print("$"*20 + "shift data %s" % (new_data))
                        new_data = self.convert_shift_operators(new_data)
                    use_datas.append(new_data)

            for use_data in use_datas:
                new_expr = expr.replace(wrtmp, use_data)
                new_expr.get_trace_variable(expr.expr.killed_vars)
                new_expr.expr.location = code_location
                new_expr.index = code_location.stmt_idx
                new_expr.expr.trace_dir = _dir

                if sp_tmp:
                    sp_tmp_name = 't%d' % sp_tmp
                    if sp_tmp_name in new_expr.expr.trace_vars:
                        new_expr.simple_replace(sp_tmp_name, sp_reg)
                        new_expr.get_trace_variable(expr.expr.killed_vars)

                new_exprs.append(new_expr)
        return new_exprs

    def _find_stack_def(self, stmts, code_location, store_tmp):
        write_tmps = {}
        stack_defs = {}
        # store_data, n_code_location = None, code_location
        stmt_index = code_location.stmt_idx
        block_addr = code_location.block_addr
        stmt_idx = stmt_index + 1
        for stmt in stmts[stmt_index+1:]:
            if stmt.tag is 'Ist_IMark':
                break

            translate_stmt(stmt, self.state)
            # print("stack sotre test: %s" % (stmt))
            if (isinstance(stmt, pyvex.stmt.WrTmp)):
                wrtmp = stmt.tmp
                write_tmps[wrtmp] = stmt_idx

            elif (isinstance(stmt, pyvex.stmt.Store) and
                    isinstance(stmt.addr, pyvex.expr.RdTmp)):
                if store_tmp != stmt.addr.tmp:
                    break

                # if stmt_idx != stmt_index:
                #     n_code_location = CodeLocation(code_location.block_addr, stmt_idx)

                if isinstance(stmt.data, pyvex.expr.Const):
                    value = stmt.data.con.value
                    size = stmt.data.con.size
                    store_data = claripy.BVV(value, size)
                else:
                    data_tmp = stmt.data.tmp
                    if data_tmp in write_tmps:
                        _idx = write_tmps[data_tmp]
                        store_data = self.state.scratch.tmp_expr(data_tmp)
                        current_location = CodeLocation(block_addr, _idx)
                        stack_defs[current_location] = (store_data, 'N')
                        # print("###TEST stack defs %s" % (stack_defs))

                        var = 't%d' % (stmt.data.tmp)
                        store_data = claripy.BVS(var, self.arch_bits, explicit_name=True)
                        current_location = CodeLocation(block_addr, stmt_idx)
                        stack_defs[current_location] = (store_data, 'F')
                        # print("###TEST stack defs %s" % (stack_defs))

                    else:
                        var = 't%d' % (stmt.data.tmp)
                        store_data = claripy.BVS(var, self.arch_bits, explicit_name=True)
                        current_location = CodeLocation(block_addr, stmt_idx)
                        stack_defs[current_location] = (store_data, 'N')
                break

            stmt_idx += 1
        return stack_defs

    def get_stack_pointer_offset(self, data):
        offset = None
        for arg in data.args:
            if arg.concrete:
                offset = arg.args[0]
        return offset

    def _find_reg_store_tmp_define(self, irsb, stmt, code_location, reg_offset, load_offsets):
        """
        Find a store addr tmp's definition by backward trace.
        Check whether the tmp variable is related to register.
        There are two cases, e.g.
            t8 = Get(rbp)
            -------------
            t9 = Add(t8, 0x24)
        :return true if find the store else false
        """
        find_reg, find_offset = False, None
        trace_tmp = stmt.addr.tmp
        stmts = irsb.statements
        current_idx = code_location.stmt_idx

        for idx in range(current_idx-1, -1, -1):
            pre_stmt = stmts[idx]
            if isinstance(pre_stmt, pyvex.stmt.WrTmp):
                if pre_stmt.tmp != trace_tmp:
                    continue

                if isinstance(pre_stmt.data, pyvex.expr.Get):
                    if pre_stmt.data.offset == reg_offset:
                        if find_offset is not None:
                            find_reg = True

                        elif 0 in load_offsets:
                            find_reg = True
                            find_offset = 0

                    break

                elif (isinstance(pre_stmt.data, pyvex.expr.Binop) and
                      pre_stmt.data.op in self.add_binops):

                    offset, tmp = None, None
                    for child_expr in pre_stmt.data.args:
                        if isinstance(child_expr, pyvex.expr.Const):
                            offset = child_expr.con.value
                        elif isinstance(child_expr, pyvex.expr.RdTmp):
                            tmp = child_expr.tmp

                    if offset in load_offsets:
                        find_offset = offset
                        trace_tmp = tmp

                    else:
                        break

                else:
                    l.info("Now we don't support the stmt %s" % (pre_stmt))
                    return None

            elif isinstance(pre_stmt, pyvex.stmt.Put):
                if pre_stmt.offset != reg_offset:
                    continue

                if isinstance(pre_stmt.data, pyvex.expr.RdTmp):
                    if pre_stmt.data.tmp == trace_tmp:
                        if find_offset is not None:
                            find_reg = True

                        elif 0 in load_offsets:
                            find_reg = True
                            find_offset = 0

                        break

        if find_reg and find_offset is not None:
            return find_offset
        else:
            return None

    def _find_register_store_def(self, irsb, stmt, expr, code_location):

        new_exprs = []

        # case 1: only trace the 'bp' register
        find_reg_offset = self.proj.arch.bp_offset
        symbol = 'r%d' % (find_reg_offset)

        # case 2: trace the register in expr
        # TODO

        load_info = find_load_with_symbol(expr.expr.ast, symbol)

        load_offsets = load_info.keys()

        find_offset = self._find_reg_store_tmp_define(irsb, stmt, code_location, find_reg_offset, load_offsets)

        if find_offset is None:
            return []

        load_ptr = load_info[find_offset]
        print("Find reg store: %s %s" % (stmt, load_ptr))

        if isinstance(stmt.data, pyvex.expr.Const):
            value = stmt.data.con.value
            size = stmt.data.con.size
            store_data = claripy.BVV(value, size)

            if value == 0:
                l.info("If expr %s is a ptr, the store data is zero, maybe the callee redefined it. do it future!" % (load_ptr))
                return []

        else:
            var = 't%d' % (stmt.data.tmp)
            store_data = claripy.BVS(var, self.arch_bits, explicit_name=True)

        new_expr = expr.replace(load_ptr, store_data)
        new_expr.get_trace_variable(expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_exprs.append(new_expr)

        return new_exprs


    def _find_stack_store_def(self, irsb, stmt, expr, code_location, sp_tmp):
        new_exprs = []
        sp_reg_name = 'r%d' % self.sp_offset
        offset = None
        # dst_var = 't%d' % (stmt.addr.tmp)
        addr_tmp = stmt.addr.tmp
        if addr_tmp == sp_tmp:
            dst_addr = claripy.BVS(sp_reg_name, self.arch_bits, explicit_name=True)
            offset = 0

        else:
            dst_addr = self._search_store_tmp(irsb, stmt, code_location, sp_tmp)
            if dst_addr is None:
                return []

            if dst_addr.op in self.add_ops:
                if len(dst_addr.args) != 2:
                    l.info("The stack variable %s is special, do it future!" % (dst_addr))
                    return []

                offset = self.get_stack_pointer_offset(dst_addr)

        if offset is None:
            return []

        ptr_info = expr.parse_vex_data(expr.expr.ast, sp_reg_name)
        # print("###TEST stack %s\n   %s" % (expr, ptr_info))
        load_datas = [ptr_info[o] for o in ptr_info if o == offset]
        if len(load_datas) != 1:
            return []

        load_data = load_datas[0]
        if isinstance(stmt.data, pyvex.expr.Const):
            value = stmt.data.con.value
            size = stmt.data.con.size
            store_data = claripy.BVV(value, size)

        else:
            var = 't%d' % (stmt.data.tmp)
            store_data = claripy.BVS(var, self.arch_bits, explicit_name=True)

        if store_data.op == 'BVV':
            # If the store data is 0, maybe the stack variable is
            # defined in a callee function.
            # TODO
            l.info("Store 0 to stack variable, do it future.")
            return []

        else:
            new_expr = expr.replace(load_data, store_data)
            new_expr.get_trace_variable(expr.expr.killed_vars)
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        return new_exprs

    def _backward_find_tmp_alias(self, irsb, trace_tmp, code_location, offset_info):
        """
        offset_info = {'r12':[o1, o2, ...], 't15':[o3, o4, ...], ...}
        """
        find_results = {}
        # tmp_alias = []
        find_offset = None
        search_syms = []
        stmts = irsb.statements
        current_idx = code_location.stmt_idx

        # irsb.pp()
        # print("offset info: %s" % (offset_info))

        for idx in range(current_idx-1, -1, -1):
            pre_stmt = stmts[idx]
            if isinstance(pre_stmt, pyvex.stmt.WrTmp):
                if pre_stmt.tmp != trace_tmp:
                    continue

                # print("DEBUG_1: %s" % (pre_stmt))

                if isinstance(pre_stmt.data, pyvex.expr.Get):
                    get_reg_name = 'r%d' % (pre_stmt.data.offset)
                    if find_offset is not None:
                        if get_reg_name in search_syms:
                            find_results[get_reg_name] = find_offset

                    else:
                        if get_reg_name in offset_info:
                            offsets = offset_info[get_reg_name]
                            if 0 in offsets:
                                find_results[get_reg_name] = 0

                    break

                if find_offset is None:
                    # TODO should think about the sub ops?
                    if (isinstance(pre_stmt.data, pyvex.expr.Binop) and
                            pre_stmt.data.op in self.add_binops):

                        offset, tmp = None, None
                        for child_expr in pre_stmt.data.args:
                            if isinstance(child_expr, pyvex.expr.Const):
                                offset = child_expr.con.value
                            elif isinstance(child_expr, pyvex.expr.RdTmp):
                                tmp = child_expr.tmp

                        # print("Find binop with %s %s" % (tmp, offset))
                        if offset is None or tmp is None:
                            break

                        for sym_name, offsets in offset_info.items():
                            if offset in offsets:
                                search_syms.append(sym_name)

                        # print("search syms: %s" % (search_syms))
                        if len(search_syms) == 0:
                            break

                        find_offset = offset
                        for sym in search_syms:
                            if 't' in sym and sym == 't%d' % (tmp):
                                find_results[sym] = find_offset

                        if len(search_syms) == 1 and 't' in search_syms[0]:
                            break

                        trace_tmp = tmp

                    else:
                        # l.info("Now we don't support the stmt %s" % (pre_stmt))
                        break

                else:
                    break

            elif isinstance(pre_stmt, pyvex.stmt.Put):
                # print("DEBUG_2: %s" % (pre_stmt))
                put_reg_name = 'r%d' % (pre_stmt.offset)
                # print(put_reg_name, offset_info)
                if put_reg_name in offset_info:
                    offsets = offset_info[put_reg_name]
                    # print("find put: %s" % (pre_stmt))
                    # print("trace tmp %s" % (trace_tmp))
                    # print(put_reg_name, search_syms)

                    if (isinstance(pre_stmt.data, pyvex.expr.RdTmp) and
                            pre_stmt.data.tmp == trace_tmp):
                        if find_offset is None:
                            if 0 in offset_info:
                                find_results[put_reg_name] = 0

                        elif put_reg_name in search_syms:
                            find_results[put_reg_name] = find_offset

                        break

        return find_results

    def _get_load_offset_info(self, load_infos, offset_info):
        for sym, datas in load_infos.items():
            if sym not in offset_info:
                offset_info[sym] = set()

            for offset in datas.keys():
                offset_info[sym].add(offset)

    def _find_tmp_store_def(self, irsb, stmt, expr, code_location):
        offset_info = {}
        new_exprs = []
        trace_tmp = stmt.addr.tmp

        load_infos = find_all_load_datas(expr.expr.ast)
        if len(load_infos) == 0:
            return []
        # print("load_infos: %s" % (load_infos))

        self._get_load_offset_info(load_infos, offset_info)

        # print("INFO: %s %s %s" % (code_location, stmt, trace_tmp))
        find_results = self._backward_find_tmp_alias(irsb, trace_tmp, code_location, offset_info)
        if len(find_results) == 0:
            return []
        # print("find tmp store: %s" % (find_results))

        load_datas = []
        for find_sym, find_offset in find_results.items():
            if find_sym in load_infos:
                load_data = load_infos[find_sym].get(find_offset)
                if load_data is not None:
                    load_datas.append(load_data)

        if len(load_datas) == 0:
            return []

        if isinstance(stmt.data, pyvex.expr.Const):
            value = stmt.data.con.value
            size = stmt.data.con.size
            store_data = claripy.BVV(value, size)

            if value == 0:
                l.info("The store data is zero, maybe the callee redefined it. do it future!")
                return []

        else:
            var = 't%d' % (stmt.data.tmp)
            store_data = claripy.BVS(var, self.arch_bits, explicit_name=True)

        new_ast_data = expr.expr.ast
        for load_ptr in load_datas:
            new_ast_data = new_ast_data.replace(load_ptr, store_data)
        new_expr = expr.deep_copy()
        new_expr.expr.ast = new_ast_data
        # new_expr = expr.replace(load_ptr, store_data)
        new_expr.get_trace_variable(expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_exprs.append(new_expr)
        return new_exprs

    def _find_store_def(self, irsb, stmt, expr, code_location, sp_tmp):
        """
        STle(t29) = t31
        """
        new_exprs = []
        sp_reg_name = 'r%d' % self.sp_offset
        if expr.is_stack_expr(sp_reg_name) and expr.expr.pattern is 'Vptr':
            # l.info("should return?")
            return []

        if isinstance(stmt.addr, pyvex.expr.RdTmp):
            # # First case: find stack def.
            # if sp_tmp is not None and sp_reg_name in expr.expr.trace_vars:
            #     # print("DEBUG: stack expr %s" % (expr))
            #     new_exprs = self._find_stack_store_def(irsb, stmt, expr, code_location, sp_tmp)

            # # Second case: find register def.
            # else:
            #     new_exprs = self._find_register_store_def(irsb, stmt, expr, code_location)

            new_exprs = self._find_tmp_store_def(irsb, stmt, expr, code_location)

        else:
            # Third case: find constant (.bss, .data) def.
            l.info("%s will be done in future!" % (stmt))
            new_exprs = self._find_constant_store_def()

        return new_exprs

    def _find_stack_store_def_bak(self, stmts, expr, code_location, store_tmp, offset):
        """
        Search a stack variable definition.
        for example:
            t15 = Get(rsp)
            t16 = Add64(t15, 0x18)
            STle(t16) = t10
        :param stmts: a list of stmtatement of IRSB
        :param expr: the trace variable expr
        :param stmt_index: index of finding the operator and store instruction
        :param store_tmp: the store tmp offset, e.g. STle(t12), then store_tmp=12
        :param offset: the offset of 'Add' operator
        """
        changed_trace_exprs = []
        sp_reg = 'r%d' % self.sp_offset
        if expr.is_stack_expr(sp_reg) and expr.expr.pattern is 'Vptr':
            # l.info("should return?")
            return []

        if sp_reg in expr.expr.trace_vars:
            ptr_info = expr.parse_vex_data(expr.expr.ast, sp_reg)
            print("###TEST stack %s\n   %s" % (expr, ptr_info))
            load_datas = [ptr_info[o] for o in ptr_info if o == offset]
            # print("find_stack_def %s %s" % (expr, load_datas))
            if len(load_datas) != 1:
                return []

            load_data = load_datas[0]
            stack_defs = self._find_stack_def(stmts, code_location, store_tmp)

            for location, data_info in stack_defs.items():
                store_data, _dir = data_info
                if store_data.op == 'BVV':
                    # If the store data is 0, maybe the stack variable is
                    # defined in a callee function.
                    # TODO
                    l.info("Store 0 to stack variable, do it future.")
                    return []

                # elif store_data.op == 'BVS':
                else:
                    new_expr = expr.replace(load_data, store_data)
                    new_expr.get_trace_variable(expr.expr.killed_vars)
                    new_expr.expr.location = location
                    new_expr.index = location.stmt_idx
                    new_expr.expr.trace_dir = _dir
                    changed_trace_exprs.append(new_expr)
        return changed_trace_exprs

    def _get_stack_pointer_offset(self, stmt, sp_tmp):
        offset = None
        if sp_tmp is None:
            return offset

        if (isinstance(stmt.data, pyvex.expr.Binop) and
                stmt.data.op in self.add_binops):
            con_offset, tmp_offset = None, None
            for child_expr in stmt.data.args:
                if isinstance(child_expr, pyvex.expr.Const):
                    con_offset = child_expr.con.value
                elif isinstance(child_expr, pyvex.expr.RdTmp):
                    tmp_offset = child_expr.tmp

            if con_offset and tmp_offset:
                if tmp_offset == sp_tmp:
                    offset = con_offset
        return offset

    def _find_stack_pointer_alias(self, stmt, expr, code_location, sp_tmp):
        sp_reg = 'r%d' % self.sp_offset
        new_exprs = []
        if expr.is_stack_expr(sp_reg) and expr.expr.pattern is 'Vptr':
            offset = self._get_stack_pointer_offset(stmt, sp_tmp)
            if offset is None:
                return []

            ptr_info = expr.parse_vex_data(expr.expr.ast, sp_reg)
            stack_vars = [ptr_info[o] for o in ptr_info if o == offset]
            if len(stack_vars) != 1:
                return []

            wrtmp = 't%d' % (stmt.tmp)
            new_expr = expr.replace(expr.expr.ast.args[0], wrtmp)
            new_expr.get_trace_variable(expr.expr.killed_vars)
            new_expr.expr.pattern = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)
        return new_exprs

    def _backward_find_use_alias(self, irsb, stmt, code_location, trace_expr, sp_tmp):
        """
        Find a alias name of a use variable ('u'), the variable 'u' must in load expr.
        for example:
            PUT (rbx) = t2
            trace_expr = load(t2 + 0x108), find the use of tmp 't2' by backward
        """
        new_expr = None
        if isinstance(stmt, pyvex.stmt.Store):
            new_expr = self._find_store_use(irsb, stmt, code_location, trace_expr, sp_tmp)

        elif isinstance(stmt, pyvex.stmt.WrTmp):
            new_expr = self._find_wrtmp_use_without_binop(stmt, trace_expr, code_location)

        elif isinstance(stmt, pyvex.stmt.Put):
            new_expr = self._find_put_use(stmt, trace_expr, code_location)

        # if sp_reg in trace_expr.trace_vars:
            # "t9 = Add(rsp + 0x8), t12 = LDle(t9)"
            # "load(load(rsp + 0x8) + 0x20)", t12 is the alias variable
            # TODO

        # elif trace_expr has 'load(rdi+0x8)':
            # trace_expr = load(load(rdi+0x8) + 0x20)
            # t9 = Add(rdi+0x8), t12 = LDle(t9), t12 is alias variable
            # TODO

        return new_expr

    def _back_execute_stmt(self, irsb, stmt, code_location, back_exprs, killed_exprs, sp_tmp=None):
        """
        Execute one stmt by backward data analysis
        """
        stmts = irsb.statements
        new_back_exprs = []

        stmt_idx = code_location.stmt_idx
        for trace_expr in back_exprs:
            # print("backward expr: %s %s" % (trace_expr, trace_expr.index))
            if stmt_idx >= trace_expr.index:
                continue

            new_exprs = []
            # print("backward stmt %s" % (stmt))
            if isinstance(stmt, pyvex.stmt.WrTmp):
                new_exprs = self._find_wrtmp_def(irsb, stmt, trace_expr, code_location, sp_tmp)
                # print("new 1: %s" % (new_exprs))
                n_exprs = self._find_stack_pointer_alias(stmt, trace_expr, code_location, sp_tmp)
                new_exprs.extend(n_exprs)
                # print("new 2: %s" % (n_exprs))

            elif isinstance(stmt, pyvex.stmt.Put):
                print("\nPut: %s" % (stmt))
                new_exprs = self._find_put_def(stmt, trace_expr, code_location, sp_tmp)
                # print("new 3: %s" % (new_exprs))

            elif isinstance(stmt, pyvex.stmt.Store):
                print("\nStore: %s" % (stmt))
                # print("Expr %s\n" % (trace_expr))
                new_exprs = self._find_store_def(irsb, stmt, trace_expr, code_location, sp_tmp)

            if trace_expr.expr.pattern in ['Vptr', 'Rptr']:
                new_expr = self._backward_find_use_alias(irsb, stmt, code_location, trace_expr, sp_tmp)
                if new_expr:
                    new_expr.forward_path = trace_expr.forward_path
                    new_expr.backward_path = trace_expr.backward_path
                    new_back_exprs.append(new_expr)

                    print("\n%s" % (code_location))
                    print("Backward old expr (alias) %s %s" % (trace_expr, trace_expr.expr.trace_vars))
                    print("new expr %s %s\n" % (new_expr, new_expr.expr.trace_vars))

            if len(new_exprs):
                for new_expr in new_exprs:
                    new_expr.forward_path = trace_expr.forward_path
                    new_expr.backward_path = trace_expr.backward_path

                new_back_exprs.extend(new_exprs)
                killed_exprs.append(trace_expr)

                print("\n%s" % (code_location))
                print("Backward old expr %s %s" % (trace_expr, trace_expr.expr.trace_vars))
                for new_expr in new_exprs:
                    print("new expr %s %s\n" % (new_expr, new_expr.expr.trace_vars))

                # self._alias_graph_add_edge(trace_expr, new_exprs)

        return new_back_exprs

    def backward_data_trace(self, block, backward_exprs, sp_tmp):
        """
        Trace expr by travel a block's isrb from last stmt to first stmt.
        """
        irsb = block.irsb

        # DEBUG
        # irsb.pp()

        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv
        sp_name = 'r%d' % self.sp_offset
        block_addr = irsb.addr

        alive_exprs = []
        stmts = irsb.statements
        for s_idx in range(len(stmts)-1, -1, -1):
            stmt = stmts[s_idx]
            if isinstance(stmt, pyvex.IRStmt.IMark):
                continue

            code_location = CodeLocation(block_addr, s_idx)
            killed_exprs = []
            new_backward_exprs = self._back_execute_stmt(irsb, stmt, code_location, backward_exprs, killed_exprs, sp_tmp)

            for new_expr in new_backward_exprs:
                if not block.is_loop:
                    self.simplify_expr(new_expr)

                if new_expr.expr.trace_dir == 'F':
                    block.forward_exprs.append(new_expr)
                    alive_exprs.append(new_expr)

                elif new_expr.expr.trace_dir == 'B':
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                # elif new_expr.is_stack_expr and new_expr.expr.pattern == 'Vptr':
                #     block.forward_exprs.append(new_expr)
                #     alive_exprs.append(new_expr)

                elif (new_expr.expr.pattern == 'Rptr' and
                        new_expr.expr.ast.op in self.concrete_ops):
                    # block.done_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                else:
                    new_expr.expr.trace_dir = 'B'
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)
                    # if new_expr.expr.ast.op == 'Load' and new_expr.expr.pattern in ['Vptr', 'Rptr']:
                    if new_expr.expr.pattern in ['Vptr', 'Rptr']:
                        copy_expr = new_expr.make_forward_copy()
                        copy_expr.forward_path = new_expr.forward_path
                        copy_expr.backward_path = new_expr.backward_path
                        block.forward_exprs.append(copy_expr)
                        alive_exprs.append(copy_expr)
                        # print("copy expr %s" % (copy_expr))

            for killed_expr in killed_exprs:
                # print("kill expr:\n%s\n" % (killed_expr))
                backward_exprs.remove(killed_expr)
                block.backward_exprs.remove(killed_expr)

        # DEBUG
        # for expr in alive_exprs:
        #     print("@-> DEBUG: Generate new forward alive expr %s" % (expr))
        return alive_exprs


    def trace_store_stmt(self, block):
        irsb = block.irsb

        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv

        stmts = irsb.statements
        for s_idx in range(len(stmts)-1, -1, -1):
            # TODO
            pass

    def trace_callee_arguments(self, block):
        pass

    def get_save_vtable_ptr_index(self, irsb, xref_addr):
        for i, stmt in enumerate(irsb.statements):
            if (isinstance(stmt, pyvex.IRStmt.IMark) and stmt.addr == xref_addr):
                return i

    def _initialize_execute_variable(self, sym_offset, sym_type, expr):
        """
        Initialize the variable while executing irsb
        :param sym_offset: offset of a tmp or a register
        :param sym_type: a symbol t (tmp) or r (register)
        :param expr: a variable expression
        """
        if expr.expr.value is not None and expr.expr.ast.op == 'BVS':
            if sym_type == 't':
                self.state.scratch.store_tmp(sym_offset, expr.expr.value)
            elif sym_type == 'r':
                self.state.registers.store(sym_offset, expr.expr.value)

    def _initialize_execute_variable2(self, sym, sym_type, expr):
        """
        Initialize the variable while executing irsb
        :param sym: a sym name of tmp or register
        :param sym_type: a symbol t (tmp) or r (register)
        :param expr: a variable expression
        """
        if sym_type == 't':
            sym_offset = int(sym[1:])
            self.state.scratch.store_tmp(sym_offset, expr.expr.value)

        elif sym_type == 'r':
            sym_offset = int(sym[1:])
            self.state.registers.store(sym_offset, expr.expr.value)

    def _execute_store_stmt(self, irsb, stmt, code_location, trace_exprs, trace_dir):
        if isinstance(stmt.data, pyvex.expr.RdTmp):
            st_tmp = stmt.data.tmp
            st_tmp_name = 't%d' % (st_tmp)

        elif isinstance(stmt.data, pyvex.expr.Const):
            pass

        else:
            l.info("Not support the stmt %s" % (stmt))

        if isinstance(stmt.addr, pyvex.expr.RdTmp):
            st_addr_tmp = stmt.addr.tmp
            st_addr_tmp_name = 't%d' % (st_addr_tmp)

        elif isinstance(stmt.addr, pyvex.expr.Const):
            pass

        else:
            l.info("Not support the stmt %s" % (stmt))

        if trace_dir == 'F':
            for trace_expr in trace_exprs:
                if trace_expr.index >= current_idx:
                    continue

                pattern = trace_expr.expr.pattern

                # Find store alias
                if st_tmp_name is not None and st_tmp_name in trace_expr.expr.trace_vars:
                    new_expr = self._find_store_alias(irsb, stmt, code_location, trace_expr)

                # Find argument pointer definition
                if pattern in ['Aptr']:
                    pass

                # TODO
                # self._find_store_killed()

        elif trace_dir == 'B':
            pass

    def _addr_tmp_with_binop(self, addr_tmp, tmp_alias):
        alias = tmp_alias[addr_tmp]

        for data in alias:
            if type(data) is tuple:
                binop = data[0]

                if binop in self.add_binops or binop in self.sub_binops:
                    return True

                elif 'to' in binop:
                    tmp = data[1][0]
                    with_op = self._addr_tmp_with_binop(tmp, tmp_alias)
                    if with_op:
                        return True
            else:
                if type(data) is str and 't' in data:
                    with_op = self._addr_tmp_with_binop(data, tmp_alias)
                    if with_op:
                        return True

                else:
                    return False

        return False

    def _find_tmp_alias(self, tmp, tmp_alias, results):
        alias = tmp_alias[tmp]

        for data in alias:
            if type(data) is tuple:
                binop = data[0]
                opnds = data[1]

                if 'to' in binop:
                    tmp = opnds[0]
                    self._find_tmp_alias(tmp, tmp_alias, results)

            else:
                if 'r' in data:
                    results.append(data)

                else:
                    tmp = data
                    self._find_tmp_alias(tmp, tmp_alias, results)

    def _find_addr_tmp_alias(self, addr_tmp, tmp_alias, results, offset=0):
        tmp = addr_tmp
        alias = tmp_alias[tmp]

        for data in alias:
            if type(data) is tuple:
                binop = data[0]
                opnds = data[1]

                if binop in self.add_binops:
                    for opnd_info in opnds:
                        results.append(('+', opnd_info))

                elif binop in self.sub_binops:
                    for opnd_info in opnds:
                        results.append(('-', opnd_info))

                elif 'to' in binop:
                    tmp = opnds[0]
                    self._find_addr_tmp_alias(tmp, tmp_alias, results)

            else:
                if 'r' in data:
                    results.append(('+', (data, offset)))

                else:
                    tmp = data
                    self._find_addr_tmp_alias(tmp, tmp_alias, results)

    def _pre_process_statement(self, block, stmt, tyenv, tmp_alias, reg_alias, loop_flag):
        """
        pre process a stmt, and get the stmt's info.
        """
        if isinstance(stmt, pyvex.stmt.Store):

            stmt_data = stmt.data
            st_size = stmt_data.result_size(tyenv)

            # STle(t2) = t3 or STle(0x46ed58) = t3
            if isinstance(stmt_data, pyvex.expr.RdTmp):
                data = 't%d' % (stmt_data.tmp)
                # datas = []
                # datas.append((data, 0))

                if loop_flag:
                    with_op = self._addr_tmp_with_binop(data, tmp_alias)
                    datas = (data, with_op)
                    # alias_results = []
                    # self._find_addr_tmp_alias(data, tmp_alias, alias_results)
                    # print("loop find: %s" % (alias_results))

                    # for sym, offset in alias_results:
                    #     datas.append((sym, offset))

                else:
                    datas = (data, )

                # datas = tuple(datas)

            # STle(t2) = 0x45 or STle(0x46ed58) = 0x7543bd
            elif isinstance(stmt_data, pyvex.expr.Const):
                data = stmt_data.con.value
                datas = (data, )
                # datas = ((data, 0),)

            else:
                l.info("Not support the stmt: %s" % (stmt))
                return None

            if isinstance(stmt.addr, pyvex.expr.RdTmp):
                addr = 't%d' % (stmt.addr.tmp)
                addrs = [('+', (addr, 0))]

                alias_results = []
                self._find_addr_tmp_alias(addr, tmp_alias, alias_results)
                # print("find store addr alias: %s" % (alias_results))

                for t in alias_results:
                    addrs.append(t)

                addrs = tuple(addrs)

            elif isinstance(stmt.addr, pyvex.expr.Const):
                addrs = stmt.addr.con.value

            else:
                l.info("Not support the stmt: %s" % (stmt))
                return None

            action = ('s', addrs, datas, st_size)

        elif isinstance(stmt, pyvex.stmt.WrTmp):

            dst = 't%d' % (stmt.tmp)
            stmt_data = stmt.data
            wr_size = stmt_data.result_size(tyenv)

            # t4 = LDle(t5) or t4 = LDle(0x46ed58)
            if isinstance(stmt_data, pyvex.expr.Load):
                wr_type = 'wl'

                load_addr = stmt_data.addr
                if isinstance(load_addr, pyvex.expr.RdTmp):
                    ld_tmp = 't%d' % (load_addr.tmp)
                    src = [('+', (ld_tmp, 0))]

                    alias_results = []
                    self._find_addr_tmp_alias(ld_tmp, tmp_alias, alias_results)
                    # print("find load addr alias: %s" % (alias_results))

                    for t in alias_results:
                        src.append(t)

                    src = tuple(src)

                elif isinstance(load_addr, pyvex.expr.Const):
                    src = load_addr.con.value

                else:
                    l.info("Not support the stmt: %s" % (stmt))
                    return None

            # t4 = Add(t3, 0x20)
            elif isinstance(stmt_data, pyvex.expr.Binop):
                wr_type = 'wo'
                binop = stmt_data.op

                # TODO
                # if choose_binop and binop not in self.choose_binop:
                #     return None

                opnds = []
                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value

                    else:
                        l.info("Not support the stmt: %s" % (stmt))
                        return None

                    opnds.append(opnd)

                alias_opnds = []
                alias_opnds.append(tuple(opnds))

                if 'Add' in binop or 'Sub' in binop and type(opnds[1]) is int:
                    alias_results = []
                    self._find_tmp_alias(opnds[0], tmp_alias, alias_results)
                    # print("block: %s %s" % (block, stmt))
                    # print("tmp alias: %s" % (tmp_alias))
                    # print("binop alias_results: %s" % (alias_results))

                    # o = opnds[1] if 'Add' in binop else (0-opnds[1])
                    o = opnds[1]
                    for sym in alias_results:
                        alias_opnds.append((sym, o))

                src = (binop, tuple(alias_opnds))

                tmp_alias[dst].append(src)

            # t4 = ITE(t1, t2, t3)
            elif isinstance(stmt_data, pyvex.expr.ITE):

                l.info("Should process the stmt %s in future." % (stmt))
                wr_type = 'wi'

                opnds = []
                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value

                    else:
                        l.info("Not support the stmt: %s" % (stmt))
                        return None

                    opnds.append(opnd)

                src = tuple(opnds)

            # t14 = 1Uto64(t15)
            elif isinstance(stmt_data, pyvex.expr.Unop):
                wr_type = 'wu'
                binop = stmt_data.op

                opnds = []
                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value

                    else:
                        l.info("Not support the stmt: %s" % (stmt))
                        return None

                    opnds.append(opnd)

                src = (binop, tuple(opnds))

                tmp_alias[dst].append(src)

            # t4 = Get(rdi) or t4 = t6
            else:
                wr_type = 'w'

                if isinstance(stmt_data, pyvex.expr.RdTmp):
                    src = 't%d' % (stmt_data.tmp)

                    tmp_alias[dst].append(src)

                elif isinstance(stmt_data, pyvex.expr.Get):
                    src = 'r%d' % (stmt_data.offset)

                    if src == self.sp_name:
                        block.stack_tmps.add(dst)

                    tmp_alias[dst].append(src)

                elif isinstance(stmt_data, pyvex.expr.Const):
                    src = stmt_data.con.value

                else:
                    l.info("Not support the stmt: %s" % (stmt))
                    return None

            action = (wr_type, dst, src, wr_size)

        elif isinstance(stmt, pyvex.stmt.Put):

            if choose_register and stmt.offset in self.ignore_regs:
                return None

            dst = 'r%d' % (stmt.offset)
            stmt_data = stmt.data
            put_size = stmt_data.result_size(tyenv)

            if isinstance(stmt_data, pyvex.expr.RdTmp):
                src = 't%d' % (stmt_data.tmp)
                # srcs = []
                # srcs.append((src, 0))

                if dst == self.sp_name:
                    block.stack_tmps.add(src)

                if dst in reg_alias:
                    tmp_alias[reg_alias[dst]].remove(dst)

                if loop_flag:
                    with_op = self._addr_tmp_with_binop(src, tmp_alias)
                    srcs = (src, with_op)
                    # alias_results = []
                    # self._find_addr_tmp_alias(src, tmp_alias, alias_results)
                    # print("loop find: %s" % (alias_results))

                    # for sym, offset in alias_results:
                    #     srcs.append((sym, offset))

                else:
                    srcs = (src, )

                tmp_alias[src].append(dst)
                reg_alias[dst] = src

                # srcs = tuple(srcs)

            elif isinstance(stmt_data, pyvex.expr.Const):
                src = stmt_data.con.value
                srcs = (src, )
                # srcs = ((src, 0),)

            else:
                l.info("Not support the stmt: %s" % (stmt))
                return None

            action = ('p', dst, srcs, put_size)

        else:
            return None

        return action

    def execute_block_irsb(self, block, block_actions, block_code_locations):
        irsb = block.irsb
        block_addr = block.addr
        loop_flag = block.is_loop

        # self.state.scratch.tyenv = irsb.tyenv
        # self.state.scratch.temps = {}

        tmp_alias = defaultdict(list)
        reg_alias = {}

        tyenv = irsb.tyenv
        stmts = irsb.statements

        count = 0
        last_ins = False
        call_flag = False
        if irsb.jumpkind == 'Ijk_Call':
            call_flag = True
            instructions = irsb.instructions

        for index, stmt in enumerate(stmts):

            code_location = CodeLocation(block_addr, index)

            # Ignore the Ijk_Call irsb's last store vex.
            if call_flag:
                if stmt.tag is 'Ist_IMark':
                    count += 1

                    if count == instructions:
                        last_ins = True

                # print("kkk- %s : %s %s" % (code_location, last_ins, stmt))
                if last_ins and isinstance(stmt, pyvex.stmt.Store):
                    # print("ignore %s" % (stmt))
                    continue

            # code_location = CodeLocation(block_addr, index)

            # l.info("stmt in %s" % (code_location))
            action = self._pre_process_statement(block, stmt, tyenv, tmp_alias, reg_alias, loop_flag)

            if action:
                block_actions[code_location] = action
                block_code_locations.append(code_location)

    def _backward_find_inc_variable_in_loop(self, function, loop):
        loop_sequence = loop.body_nodes
        loop_len = len(loop_sequence)

        tmp_graph = networkx.DiGraph()

        rd_tmps = {}
        rd_regs = {}
        wr_regs = {}
        trace_syms = {}

        loop_time = 0
        while loop_time < 2:
            loop_time += 1
            for i in range(loop_len-1, -1, -1):

                block = loop_sequence[i]
                print("\nloop_block %s" % (block))

                actions = block.actions
                code_locations = block.code_locations
                ins_len = len(code_locations)

                for i in range(ins_len-1, -1, -1):

                    code_location = code_locations[i]
                    action = actions[code_location]

                    action_type = action[0]

                    print("%s action: %s" % (code_location, str(action)))
                    print("%s trace: %s" % (code_location, trace_syms))

                    if action_type == 'p':
                        put_reg, put_datas = action[1], action[2]
                        put_data = put_datas[0]

                        if put_reg in trace_syms:
                            trace_info = trace_syms[put_reg]

                            for o, target_locations in trace_info.items():

                                for target_location in target_locations:
                                    tmp_graph.add_edge(code_location, target_location)

                                if type(put_data) is str:

                                    if put_data not in trace_syms:
                                        trace_syms[put_data] = {}

                                    new_info = trace_syms[put_data]

                                    if o not in new_info:
                                        new_info[o] = set()

                                    new_info[o].add(code_location)

                            trace_syms.pop(put_reg)

                        if len(put_datas) != 2 or put_reg == self.sp_name:
                            continue

                        with_op = put_datas[1]
                        if with_op:
                            if put_data not in trace_syms:
                                trace_syms[put_data] = {}

                            if 'N' not in trace_syms[put_data]:
                                trace_syms[put_data]['N'] = set()

                            trace_syms[put_data]['N'].add(code_location)

                    elif action_type == 'w':
                        wr_tmp, wr_data = action[1], action[2]
                        if wr_data == self.sp_name:
                            continue

                        if wr_tmp in trace_syms:
                            trace_info = trace_syms[wr_tmp]

                            for o, target_locations in trace_info.items():
                                for target_location in target_locations:
                                    tmp_graph.add_edge(code_location, target_location)

                                if wr_data not in trace_syms:
                                    trace_syms[wr_data] = {}

                                new_info = trace_syms[wr_data]

                                if o not in new_info:
                                    new_info[o] = set()

                                new_info[o].add(code_location)

                    elif action_type == 'wo':
                        wr_tmp, wr_datas = action[1], action[2]

                        if wr_tmp in trace_syms:
                            remov_syms = []
                            trace_info = trace_syms[wr_tmp]

                            for o, target_locations in trace_info.items():
                                for target_location in target_locations:
                                    tmp_graph.add_edge(code_location, target_location)

                                if o != 'N':
                                    remov_syms.append(o)

                                else:
                                    for sym in wr_datas[1]:
                                        if type(sym) is str:
                                            if sym not in trace_syms:
                                                trace_syms[sym] = {}

                                            new_info = trace_syms[sym]

                                            if 'N' not in new_info:
                                                new_info['N'] = set()

                                            new_info['N'].add(code_location)

                            for o in remov_syms:
                                trace_info.pop(o)

                    elif action_type == 'wu':
                        wr_tmp, wr_datas = action[1], action[2]

                        if wr_tmp in trace_syms:
                            unop_datas = wr_datas[1]
                            if len(unop_datas) != 1:
                                trace_syms.pop(wr_tmp)
                                continue

                            trace_info = trace_syms[wr_tmp]

                            for o, target_locations in trace_info.items():
                                for target_location in target_locations:
                                    tmp_graph.add_edge(code_location, target_location)

                                sym = unop_datas[0]
                                if type(sym) is str:
                                    if sym not in trace_syms:
                                        trace_syms[sym] = {}

                                    new_info = trace_syms[sym]

                                    if o not in new_info:
                                        new_info[o] = set()

                                    new_info[o].add(code_location)

                    elif action_type == 'wl':
                        wr_tmp, wr_datas = action[1], action[2]
                        remov_syms = []

                        if type(wr_datas) is not tuple:
                            continue

                        if wr_tmp in trace_syms:
                            trace_info = trace_syms[wr_tmp]

                            for o, target_locations in trace_info.items():
                                for target_location in target_locations:
                                    tmp_graph.add_edge(code_location, target_location)

                                if o != 'N':
                                    remov_syms.append(o)

                                else:
                                    for sym, lo in wr_datas:
                                        if 'r' in sym:
                                            if sym not in trace_syms:
                                                trace_syms[sym] = {}

                                            new_info = trace_syms[sym]

                                            if lo not in new_info:
                                                new_info[lo] = set()

                                            new_info[lo].add(code_location)

                            for o in remov_syms:
                                trace_info.pop(o)

                    elif action_type == 's':
                        st_addrs, st_datas = action[1], action[2]

                        if type(st_addrs) is not tuple:
                            continue

                        # print("s: %s" % (str(st_addrs)))
                        # print(trace_syms)

                        for st_addr, so in st_addrs:
                            if 'r' in st_addr and st_addr in trace_syms:
                                trace_info = trace_syms[st_addr]
                                remov_syms = []

                                for o, target_locations in trace_info.items():

                                    if o == so:
                                        for target_location in target_locations:
                                            tmp_graph.add_edge(code_location, target_location)

                                        st_data = st_datas[0]
                                        if type(st_data) is str:
                                            if st_data not in trace_syms:
                                                trace_syms[st_data] = {}

                                            new_info = trace_syms[st_data]

                                            if 'N' not in new_info:
                                                new_info['N'] = set()

                                            new_info['N'].add(code_location)

                                        remov_syms.append(o)

                                for o in remov_syms:
                                    trace_info.pop(o)

                                if len(trace_info) == 0:
                                    trace_syms.pop(st_addr)

                syms = [s for s in trace_syms]
                for sym in syms:
                    if 't' in sym:
                        trace_syms.pop(sym)

        for n in tmp_graph.nodes():
            print("kai: %s" % (n))

        for src, dst in tmp_graph.edges():
            print("edge: %s -> %s" % (src, dst))

        funcea = function.addr
        self._label_inc_flag_in_loop(funcea, tmp_graph)

        # for subg in networkx.strongly_connected_component_subgraphs(tmp_graph):
        #     if len(subg.nodes()) == 1:
        #         if len(list(subg.successors(list(subg.nodes())[0]))) == 0:
        #             continue

        #     nodes = subg.nodes
        #     print("sub_loop nodes%s" % (nodes))

    def _label_inc_flag_in_loop(self, funcea, graph):
        for subg in networkx.strongly_connected_component_subgraphs(graph):
            if len(subg.nodes()) == 1:
                if len(list(subg.successors(list(subg.nodes())[0]))) == 0:
                    continue

            nodes = subg.nodes()
            for code_location in nodes:
                print("sub_loop node%s" % (code_location))
                loop_inc_locations[funcea].add(code_location)
                # function.inc_locations.add(code_location)

    def _find_store_use2(self, st_addr, st_data, st_size, code_location, trace_expr):
        """
        For the IR "STle(t19) = t9", the tmp t9 is used, could be replaced with 'Store(t19)'
        """

        # TODO for the embedded store instructions.
        if code_location in trace_expr.expr.store_location:
            return []

        if type(st_addr) is int:
            addr_ast = claripy.BVV(st_addr, self.arch_bits)

        elif type(st_addr) is str:
            addr_ast = claripy.BVS(st_addr, self.arch_bits, explicit_name=True)

        elif type(st_addr) is tuple:
            ptr = claripy.BVS(st_addr[0], self.arch_bits, explicit_name=True)
            offset = claripy.BVV(st_addr[1], self.arch_bits)
            addr_ast = ptr + offset

        else:
            return []

        dst_data = claripy.Store(addr_ast, st_size)
        new_expr = trace_expr.replace(st_data, dst_data)
        new_expr.expr.store_location.append(code_location)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _add_store_action(self, st_data, code_location, old_expr, new_expr):

        add_sim_action_flag = False
        old_ast = old_expr.expr.ast
        sim_index = get_index_info_with_sim(old_ast, st_data)
        print("add_store: %s" % (sim_index))

        index_info = {}
        new_ast = new_expr.expr.ast
        deref_info = get_deref_info(new_ast, index_info)

        print("add_store: %s %s" % (deref_info, index_info))
        old_sim_actions = old_expr.expr.sim_actions

        # add_index = [i for i in sim_index if i in deref_info][0]
        # add_deref = deref_info[add_index]
        # new_sim_action = self._create_sim_action(add_index, add_deref, code_location)

        n = 0
        new_sim_actions = {}

        for index, deref in deref_info.items():

            if index in sim_index:
                n += 1

                if not add_sim_action_flag:
                    new_sim_action = self._create_sim_action(index, deref, code_location, action_type='store')
                    new_sim_actions[index] = new_sim_action
                    add_sim_action_flag = True

            elif deref is None:
                if index - n in old_sim_actions:
                    old_sim_action = old_sim_actions[index-n]
                    new_sim_action = self._change_sim_action_name_to_none(old_sim_action)
                    new_sim_actions[index] = new_sim_action

            else:
                if index - n in old_sim_actions:
                    new_sim_actions[index] = old_sim_actions[index-n]

        new_expr.expr.sim_actions = new_sim_actions

    def _add_load_action(self, wr_tmp, code_location, old_expr, new_expr):

        add_sim_action_flag = False
        old_ast = old_expr.expr.ast
        sim_index = get_index_info_with_sim(old_ast, wr_tmp)
        # print("add_load: %s" % (sim_index))

        index_info = {}
        new_ast = new_expr.expr.ast
        deref_info = get_deref_info(new_ast, index_info)

        # print("add_load: %s %s" % (deref_info, index_info))
        old_sim_actions = old_expr.expr.sim_actions

        n = 0
        new_sim_actions = {}

        for index, deref in deref_info.items():

            if index in sim_index:
                n += 1

                if not add_sim_action_flag:
                    new_sim_action = self._create_sim_action(index, deref, code_location, action_type='load')
                    new_sim_actions[index] = new_sim_action
                    add_sim_action_flag = True

            elif deref is None:
                if index - n in old_sim_actions:
                    old_sim_action = old_sim_actions[index-n]
                    new_sim_action = self._change_sim_action_name_to_none(old_sim_action)
                    new_sim_actions[index] = new_sim_action

            else:
                if index - n in old_sim_actions:
                    new_sim_actions[index] = old_sim_actions[index-n]

        new_expr.expr.sim_actions = new_sim_actions

    def _create_sim_action(self, index, deref, code_location, action_type=None):

        binop, opnds = deref[0], deref[1]
        action_data = deref[2]

        sim_action = SimAction(name=opnds, action_type=action_type, binop=binop, action_data=action_data)
        sim_action.def_locs.add(code_location)

        return sim_action

    def _change_sim_action_name_to_none(self, sim_action):

        new_sim_action = SimAction()
        new_sim_action.action_type = sim_action.action_type
        new_sim_action.live = sim_action.live
        new_sim_action.def_locs = sim_action.def_locs

        return new_sim_action

    def _change_sim_action_name(self, sim_action, new_name, new_action_data, binop):

        new_sim_action = SimAction(name=new_name, action_data=new_action_data, binop=binop)
        new_sim_action.action_type = sim_action.action_type
        new_sim_action.def_locs = sim_action.def_locs

        return new_sim_action

    def _update_sim_actions(self, trace_expr, old_actions, add_actions, subvar, repvar):
        """
        While generate a new expr, we should update the expr's sim_actions.
        """

        trace_ast = trace_expr.expr.ast
        deref_info, search_index = get_all_deref_info_with_search(trace_ast, r_ast)

        print("update sim_action in expr: %s" % (trace_expr))

        for index, deref in deref_info.items():
            print("deref info: %d %s" % (index, deref))

        for index in search_index:
            print("find index: %d" % (index))

    def _update_sim_actions_bak(self, trace_expr):

        index_info = {}
        old_sim_actions = trace_expr.expr.sim_actions
        ast = trace_expr.expr.ast
        # deref_info = get_deref_info(ast, index_info)
        deref_info = get_all_deref_info(ast)
        # print("expr- %s" % (trace_expr))
        # print("deref info: %s" % (deref_info))
        # print("index info: %s" % (index_info))

        same_names = {}
        new_sim_actions = {}

        # print("update_sim: %s %s" % (trace_expr, deref_info))

        for index, sim_action in old_sim_actions.items():
            # print("%d %s %s" % (index, sim_action.name, sim_action.action_data))

            old_name = sim_action.name
            deref = deref_info[index]

            # TODO thre error, while load(rax + 0x4) replace t0 load(rax + 0x20 + 0x4)
            if deref is not None:
                new_name = deref[1]
                action_type = sim_action.action_type
                if new_name != old_name:
                    binop = deref[0]
                    new_action_data = deref[2]
                    sim_action = self._change_sim_action_name(sim_action, new_name, new_action_data, binop)
                    new_sim_actions[index] = sim_action

                elif action_type == 'store':
                    new_sim_actions[index] = sim_action

                if action_type == 'load':
                    if new_name not in same_names:
                        same_names[new_name] = []

                    same_names[new_name].append(sim_action)

            elif old_name is not None:
                new_sim_actions[index] = self._change_sim_action_name_to_none(sim_action)

        if len(new_sim_actions) == 0:
            return

        for index, sim_action in new_sim_actions.items():
            name = sim_action.name

            if name and name in same_names and len(same_names[name]) >= 2:
                for sa in same_names[new_name]:
                    for def_loc in sa.def_locs:
                        sim_action.def_locs.add(def_loc)

                same_names.pop(name)

        for index, sim_action in old_sim_actions.items():

            name = sim_action.name
            if name is None:
                new_sim_actions[index] = sim_action

            elif name in same_names:
                same_load_actions = same_names[name]
                if len(same_names[name]) == 1:
                    if index not in new_sim_actions:
                        new_sim_actions[index] = sim_action

                else:
                    new_sim_action = sim_action.copy()

                    for sa in same_load_actions:
                        for def_loc in sa.def_locs:
                            new_sim_action.def_locs.add(def_loc)

                    new_sim_actions[index] = new_sim_action

                same_names.pop(name)

        trace_expr.expr.sim_actions = new_sim_actions

    def _update_sims_with_tmp(new_exprs):
        pass

    def _update_sims_with_reg(new_exprs):
        pass

    def _find_constant_store_use(self):
        return []

    def _find_pointer_redefine(self):
        pass

    def _find_store_redefine(self):
        pass

    def _find_put_use2(self, reg_name, put_data, code_location, trace_expr, trace_dir=None):

        new_expr = trace_expr.replace(put_data, reg_name)
        new_expr.expr.trace_dir = trace_dir
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_wrtmp_use2(self, wr_tmp, wr_data, code_location, trace_expr):

        new_expr = trace_expr.replace(wr_data, wr_tmp)
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_register_load_use2(self, wr_tmp, ld_addrs, code_location, trace_expr):

        # print("f_find_load: %s" % (trace_expr))
        sim_actions = trace_expr.expr.sim_actions

        if len(sim_actions) == 0:
            return []

        # for index, sim_action in sim_actions.items():
        #     print("%d %s (%s)" % (index, sim_action.action_data, sim_action.action_type))

        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            action_data = sim_action.action_data

            if name and action_data.op == 'Store':
                binop = sim_action.binop

                for _op, ld_addr in ld_addrs:
                    if _op == binop and name == ld_addr:
                        load_ptrs.append(sim_action.action_data)

        if len(load_ptrs) != 1:
            return []

        load_ptr = load_ptrs[0]

        new_expr = trace_expr.replace(load_ptr, wr_tmp)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx

        # self._remove_sim_actions(load_ptr, trace_expr, new_expr)

        return [new_expr]

    def _remove_sim_actions(self, load_ptr, old_expr, new_expr):

        add_sim_action_flag = False
        old_ast = old_expr.expr.ast
        load_child_len, sim_indexs = get_index_info_with_child_ast(old_ast, load_ptr)

        index_info = {}
        new_ast = new_expr.expr.ast
        deref_info = get_deref_info(new_ast, index_info)

        old_sim_actions = old_expr.expr.sim_actions

        n = 0
        new_sim_actions = {}

        for index in range(load_child_len):
            if index in sim_indexs:
                n += 1

            else:
                if index in old_sim_actions:
                    old_sim_action = old_sim_actions[index]
                    old_name = old_sim_action.name

                    if index-n in deref_info:
                        deref = deref_info[index-n]

                        if old_name is None and deref is not None:
                            binop, new_name, new_action_data = deref[0], deref[1], deref[2]
                            new_sim_action = self._change_sim_action_name(old_sim_action, new_name, new_action_data, binop)
                            new_sim_actions[index-n] = new_sim_action

                        else:
                            new_sim_actions[index-n] = old_sim_action

                    else:
                        l.info("Some error in remove sim action: %s %s" % (old_expr, new_expr))
                        return

        new_expr.expr.sim_actions = new_sim_actions

    def _find_load_value2(self, wr_tmp, ld_addr, ld_size, code_location, trace_expr):

        ld_addr_value = trace_expr.expr.value

        if ld_size == self.arch_bits:
            new_value = claripy.Load(ld_addr_value, ld_size)

        else:
            # Now, we not trace the pure data wthich is not pointer.
            return []

        trace_ast = claripy.BVS(wr_tmp, ld_size, explicit_name=True)

        new_expr = trace_expr.deep_copy()
        new_expr.expr.ast = trace_ast
        new_expr.expr.value = new_value
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_constant_load_use(self):
        # TODO
        pass

    def _find_wrtmp_use_with_binop(self, wr_tmp, opnd, value, code_location, trace_expr):

        new_expr = trace_expr.replace(opnd, wr_tmp)
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_expr.expr.value = value

        return [new_expr]

    def _find_wrtmp_with_binop_alias(self, op, wr_tmp, opnds, code_location, trace_expr):

        new_expr = None

        def check_binop_alias(opnds, sim_actions):
            binop_alias = None

            for sim_action in sim_actions.values():
                if (sim_action.action_type == 'store' and sim_action.name in opnds):
                    if sim_action.binop == '+' and 'Add' in op:
                        binop_alias = sim_action.action_data.args[0]

                    elif sim_action.binop == '-' and 'Sub' in op:
                        binop_alias = sim_action.action_data.args[0]

            return binop_alias

        # print("binop_alias: %s %s" % (wr_tmp, opnds))

        sim_actions = trace_expr.expr.sim_actions
        binop_alias = check_binop_alias(opnds, sim_actions)

        if binop_alias is not None:
            # print("find binop_alias: %s" % (str(binop_alias)))
            new_expr = trace_expr.replace(binop_alias, wr_tmp)
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx

        return new_expr

    def _kill_reg_defined2(self, reg_name, code_location, trace_expr):
        """
        In forward trace, the reg could be redefined.
        One: load(rax+0x8), and put(rax) = rbx, then expr load(rax+0x8) should be killed.
        two: load(rax+rdi), and put(rax) = rbx, then reg rax is killed, but we should reserve the expr and copy it.
        """
        # %TODO add variable alive
        if len(trace_expr.expr.trace_vars) >= 2:
            new_expr = trace_expr.deep_copy()
            new_expr.expr.trace_vars.remove(reg_name)
            new_expr.expr.killed_vars.add(reg_name)
            new_expr.index = code_location.stmt_idx
            new_expr.expr.trace_dir = 'F'

            return [new_expr]

        else:
            return []

    def _kill_register_define(self, reg_name, code_location, trace_expr):

        sims = trace_expr.expr.sims
        live_count = [1 for sim in sims.values() if sim and sim.live]
        if len(live_count) == 1:
            return None

        new_sim = Sim(live=False, def_loc=code_location)
        new_expr = trace_expr.deep_copy()
        new_sims = new_expr.expr.sims

        new_sims[reg_name] = new_sim

        return new_expr

    def _create_sim(self, reg_name, live, def_loc):

        new_sim = Sim(reg_name, False, code_location)

        return new_sim

    def _label_sim_action(self, new_exprs, code_location):

        for new_expr in new_exprs:

            # sim_action = SimAction()

            ast = new_expr.expr.ast

            deref_info = get_deref_info(ast)

            print("ls new_expr: %s" % (new_expr))
            print("%s %s" % (code_location, str(deref_info)))

    def _forward_store_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, the vex 'STle(t4) = t5'.
        """

        new_forward_exprs = []

        st_addrs, st_datas, st_size= action[1], action[2], action[3]
        st_data = st_datas[0]
        is_stack_store = False

        # print("f-store: %s %s" % (code_location, str(action)))

        if st_size == 8 or st_size == 16:
            # l.info("Not think about this store action %s while forward tracing ptr in %s." % (str(action), code_location))
            return []

        # Check the rbp is stack prt or regural ptr in the fist block of function.
        if type(st_addrs) is tuple:

            # The ins 'push rbp' will change the sp value, we ignore it.
            stack_info = [t[1] for t in st_addrs if t[1][0] == self.sp_name and t[1][1] >= 0]

            if len(stack_info):
                is_stack_store = True
                stack_addr = stack_info[0]

            st_type = 'reg'
            st_addr = st_addrs[0][1][0]

        elif type(st_addrs) is int:
            st_type = 'immi'
            st_addr = st_addrs

        else:
            l.info("Not support the action: %s" % (action))
            return []

        current_idx = code_location.stmt_idx
        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            if trace_expr.expr.pattern == 'OB':
                continue

            if is_stack_store and trace_expr.expr.ast.op not in ['BVV', 'BVS']:
                continue

            trace_sims = trace_expr.expr.sims

            if st_data in trace_sims:
                # print("store: %s %s" % (st_addr, st_data))

                if is_stack_store:
                    new_exprs = self._find_store_use2(stack_addr, st_data, st_size, code_location, trace_expr)

                else:
                    new_exprs = self._find_store_use2(st_addr, st_data, st_size, code_location, trace_expr)

                new_forward_exprs.extend(new_exprs)

            if trace_expr.expr.pattern == 'SLBF':
                self._find_pointer_redefine()

            if do_forward_store_redefine:
                self._find_store_redefine()

        return new_forward_exprs

    def _forward_put_stmt(self, block, action, code_location, forward_exprs):

        new_forward_exprs = []
        killed_exprs = []

        reg_name, put_datas = action[1], action[2]
        put_data = put_datas[0]

        current_idx = code_location.stmt_idx
        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            if trace_expr.expr.pattern == 'OB':
                continue

            trace_sims = trace_expr.expr.sims

            # print("expr- %s" % (trace_expr))
            # print("kai- trace_vars: %s" % (trace_expr.expr.trace_vars))
            # print("kai- trace_sims: %s" % (trace_sims))

            if put_data in trace_sims:

                if reg_name in trace_sims:
                    l.info("There will be some error in %s %s" % (code_location, trace_expr))
                    l.info("The old reg %s is killed by %s" % (reg_name, put_data))

                new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='F')

                new_forward_exprs.extend(new_exprs)

            # In forward trace, the reg will be redefined.
            if reg_name != self.sp_name and reg_name in trace_sims and trace_sims[reg_name].live:

                kill_sim = trace_sims[reg_name]
                # if kill_sim.live:
                #     print("\nreg_kill: %s %s" % (code_location, reg_name))
                #     print(" expr - %s" % (trace_expr))

                killed_exprs.append(trace_expr)

                new_expr = self._kill_register_define(reg_name, code_location, trace_expr)

                if new_expr is not None:
                    new_forward_exprs.append(new_expr)

        for kill_expr in killed_exprs:
            try:
                forward_exprs.remove(kill_expr)
                block.forward_exprs.remove(kill_expr)

            except:
                continue

        # In the Ijk_Ret block, if the stack reg is redefined, clear the forward_exprs.
        if reg_name == self.sp_name and block.irsb:
            jumpkind = block.irsb.jumpkind

            if jumpkind == 'Ijk_Ret':
                forward_exprs.clear()

        return new_forward_exprs

    def _forward_wrtmp_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, IR " t4 = Get(rdi) " could trace from rdi to tmp t4.
        """

        new_forward_exprs = []

        wr_tmp, wr_data = action[1], action[2]

        if wr_data == 'r%d' % (self.sp_offset):
            return []

        current_idx = code_location.stmt_idx
        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            if trace_expr.expr.pattern == 'OB':
                continue

            trace_sims = trace_expr.expr.sims

            if wr_data in trace_sims:

                sim = trace_sims[wr_data]
                if not sim.live or code_location == sim.def_loc:
                    continue

                new_exprs = self._find_wrtmp_use2(wr_tmp, wr_data, code_location, trace_expr)

                new_forward_exprs.extend(new_exprs)

        return new_forward_exprs

    def _forward_wrtmp_load_stmt(self, block, action, code_location, forward_exprs):

        new_forward_exprs = []

        wr_tmp, ld_addrs, ld_size = action[1], action[2], action[3]

        if type(ld_addrs) is int:
            ld_type = 'immi'

        elif type(ld_addrs) is tuple:
            ld_type = 'reg'
            ld_addr = ld_addrs[0][1][0]

        else:
            l.info("Not support the action: %s" % (str(action)))
            return []

        current_idx = code_location.stmt_idx
        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            if trace_expr.expr.pattern == 'OB':
                continue

            # print("expr: %s" % (trace_expr))
            # print("forward load: %s %s" % (code_location, str(action)))

            if ld_type == 'reg':
                if trace_expr.expr.ast.op == 'BVS':

                    if trace_expr.expr.pattern in ['LBF', 'SLBF'] and ld_addr in trace_expr.expr.sims:

                        new_exprs = self._find_load_value2(wr_tmp, ld_addr, ld_size, code_location, trace_expr)

                        new_forward_exprs.extend(new_exprs)

                else:
                    new_exprs = self._find_register_load_use2(wr_tmp, ld_addrs, code_location, trace_expr)

                    new_forward_exprs.extend(new_exprs)

                # elif trace_expr.expr.ast.op == 'Load' and trace_expr.expr.pattern == 'SLBF':
                #     pass

            elif ld_type == 'immi' and do_forward_concrete_load:
                self._find_constant_load_use()

        return new_forward_exprs

    def _forward_wrtmp_binop_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, IR "t4 = Add(t5, 0x20)" could trace into tmp t4.
        """

        new_forward_exprs = []

        wr_tmp, wr_data = action[1], action[2]
        binop = wr_data[0]
        opnds = wr_data[1]

        # print("f-wrtmp_binop: %s %s" % (code_location, str(action)))

        current_idx = code_location.stmt_idx
        stmt = block.irsb.statements[current_idx]

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            if trace_expr.expr.pattern in ['OB', 'RBF']:
                continue

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if trace_ast.op == 'BVS':
                trace_sym = trace_ast.args[0]
                sim = trace_sims[trace_sym]

                if not sim.live or trace_sym not in opnds:
                    continue

                if trace_expr.expr.pattern in ['LBF', 'SLBF']:
                    self._initialize_execute_variable2(trace_sym, 't', trace_expr)

                elif trace_expr.expr.value.concrete:
                    self._initialize_execute_variable2(trace_sym, 't', trace_expr)

                else:
                    continue

                translate_stmt(stmt, self.state)

                new_value = self.state.scratch.tmp_expr(stmt.tmp)

                new_exprs = self._find_wrtmp_use_with_binop(wr_tmp, trace_sym, new_value, code_location, trace_expr)
                new_forward_exprs.extend(new_exprs)

            # Find binop alias, e.g. mov rdi, rsp + 0x18 // load(rsp + 0x18)
            if trace_expr.is_stack_expr(self.sp_name):

                stack_binop = [opnd for opnd in opnds if opnd[0] == self.sp_name]

                if len(stack_binop):
                    new_expr = self._find_wrtmp_with_binop_alias(binop, wr_tmp, opnds, code_location, trace_expr)

                    if new_expr is not None:
                        new_forward_exprs.append(new_expr)

        return new_forward_exprs

    def _forward_execute_stmt(self, block, action, code_location, forward_exprs):
        action_type = action[0]

        if action_type == 's':
            new_forward_exprs = self._forward_store_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'p':
            new_forward_exprs = self._forward_put_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'w':
            new_forward_exprs = self._forward_wrtmp_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'wo':
            new_forward_exprs = self._forward_wrtmp_binop_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'wl':
            new_forward_exprs = self._forward_wrtmp_load_stmt(block, action, code_location, forward_exprs)

        elif action_type in ['wu', 'wi']:
            new_forward_exprs  =[]

        else:
            l.info("This action type %s is not support!" % (action_type))
            new_forward_exprs  =[]

        if len(new_forward_exprs):
            print("\nForward: %s" % (code_location))
            for new_expr in new_forward_exprs:
                print("new expr %s %s\n" % (new_expr, new_expr.expr.trace_vars))

                # self._update_sim_actions(new_expr)

        return new_forward_exprs

    def forward_data_trace2(self, block, forward_exprs):
        """
        param: irsb:
        param: forward_exprs: a list of forward trace variable expressions.
        """
        irsb = block.irsb

        self.state.scratch.tyenv = irsb.tyenv
        self.state.scratch.temps = {}

        code_locations = block.code_locations
        actions = block.actions

        alive_exprs = []
        for code_location in code_locations:

            action = actions[code_location]

            new_forward_exprs = self._forward_execute_stmt(block, action, code_location, forward_exprs)

            if len(new_forward_exprs) == 0:
                continue

            forward_exprs.extend(new_forward_exprs)
            block.forward_exprs.extend(new_forward_exprs)

            for new_expr in new_forward_exprs:
                if not block.is_loop:
                    self.simplify_expr(new_expr)

                if new_expr.expr.trace_dir != 'F':
                    new_expr.expr.trace_dir = 'F'

                    copy_expr = new_expr.make_backward_copy()
                    # copy_expr.expr.pattern = 'OBF'
                    copy_expr.forward_path = new_expr.forward_path
                    copy_expr.backward_path = new_expr.backward_path
                    block.backward_exprs.append(copy_expr)
                    alive_exprs.append(copy_expr)
                    # print("copy expr %s" % (copy_expr))

        return alive_exprs

    def backward_data_trace2(self, block, backward_exprs):
        """
        Trace expr by travel a block's isrb from last stmt to first stmt.
        """

        self.state.scratch.tyenv = block.irsb.tyenv
        self.state.scratch.temps = {}

        # if block.irsb:
        #     block.irsb.pp()

        code_locations = block.code_locations
        actions = block.actions
        ins_len = len(code_locations)

        alive_exprs = []
        for i in range(ins_len-1, -1, -1):

            code_location = code_locations[i]
            action = actions[code_location]

            # DEBUG
            print("%s %s" % (code_location, str(action)))
            print("backward exprs: %s" % (backward_exprs))

            new_backward_exprs = self._backward_execute_stmt2(block, action, code_location, backward_exprs)

            for new_expr in new_backward_exprs:
                if not block.is_loop:
                    self.simplify_expr(new_expr)

                if new_expr.expr.trace_dir == 'F':
                    block.forward_exprs.append(new_expr)
                    alive_exprs.append(new_expr)

                elif new_expr.expr.trace_dir == 'B':
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                else:
                    new_expr.expr.trace_dir = 'B'
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                    if 'BF' in new_expr.expr.pattern:
                        copy_expr = new_expr.make_forward_copy()
                        copy_expr.forward_path = new_expr.forward_path
                        copy_expr.backward_path = new_expr.backward_path
                        block.forward_exprs.append(copy_expr)
                        alive_exprs.append(copy_expr)
                        # print("copy expr %s" % (copy_expr))

        return alive_exprs

    def _backward_execute_stmt2(self, block, action, code_location, backward_exprs):
        action_type = action[0]

        if action_type == 's':
            new_backward_exprs = self._backward_store_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'p':
            new_backward_exprs = self._backward_put_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'w':
            new_backward_exprs = self._backward_wrtmp_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wo':
            new_backward_exprs = self._backward_wrtmp_binop_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wl':
            new_backward_exprs = self._backward_wrtmp_load_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wu':
            new_backward_exprs = self._backward_wrtmp_unop_stmt(block, action, code_location, backward_exprs)

        else:
            l.info("This action type %s is not support!" % (action_type))
            new_backward_exprs = []

        if len(new_backward_exprs):
            print("\nBackward: %s" % (code_location))
            for new_expr in new_backward_exprs:
                # print("new expr %s %s" % (new_expr, new_expr.expr.trace_vars))

                print("new expr has sims: %s" % (new_expr.expr.sims))

                # self._update_sim_actions(new_expr)

                print("new expr has sim_actions:")
                for index, sim_action in new_expr.expr.sim_actions.items():
                    print("sim_action: %d %s %s" % (index, sim_action, sim_action.action_data))

                print("")

        return new_backward_exprs

    def _backward_store_stmt(self, block, action, code_location, backward_exprs):

        new_backward_exprs = []

        st_addrs, st_datas, st_size = action[1], action[2], action[3]
        st_data = st_datas[0]
        is_stack_store = False

        # print("b-store: %s %s" % (code_location, str(action)))

        if type(st_addrs) is tuple:

            stack_info = [t[1] for t in st_addrs if t[1][0] == self.sp_name and t[1][1] >= 0]
            if len(stack_info):
                is_stack_store = True

            st_type = 'reg'
            st_addr = st_addrs[0][1][0]

        elif type(st_addrs) is int:
            st_type = 'immi'
            st_addr = st_addrs

        else:
            l.info("Not support the action: %s" % (action))
            return []

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            pattern = trace_expr.expr.pattern
            trace_sims = trace_expr.expr.sims
            # print("debug: %s %s %s" % (code_location, trace_expr, pattern))

            # In backward, save a ptr to mem could create a alias
            if ('BF' in pattern and
                    not is_stack_store and
                    st_size == self.arch_bits and
                    st_data in trace_sims):

                if type(st_data) is str:
                    new_alias = self._find_store_use2(st_addr, st_data, st_size, code_location, trace_expr)

                    new_backward_exprs.extend(new_alias)

                elif type(st_data) is int:
                    new_alias = self._find_constant_store_use()

            # if trace_expr.expr.pattern == 'OBF':
            #     continue

            # In backward, for the case: Load(rsp + 0x20): value
            if trace_expr.is_stack_expr(self.sp_name) and trace_expr.expr.value is not None:
                continue

            if st_type == 'reg':
                new_exprs = self._find_register_store_def2(st_addrs, st_data, st_size, code_location, trace_expr)

            elif st_type == 'immi':
                new_exprs = self._find_constant_store_def()

            if len(new_exprs):
                killed_exprs.append(trace_expr)
                new_backward_exprs.extend(new_exprs)

                try:
                    block.backward_exprs.remove(trace_expr)

                except:
                    pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _backward_put_stmt(self, block, action, code_location, backward_exprs):
        """
        In backward, IR "Put(rdi) = t4" could trace from rid to tmp t4.
        """

        new_backward_exprs = []

        reg_name, put_datas, put_size = action[1], action[2], action[3]
        put_data = put_datas[0]

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            trace_sims = trace_expr.expr.sims
            pattern = trace_expr.expr.pattern

            if reg_name == self.sp_name:

                if (type(put_data) is str and put_data in trace_sims):

                    if pattern == 'OB':
                        new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='B')

                    else:
                        new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='B')

                    new_backward_exprs.extend(new_exprs)

                    if len(new_exprs):
                        killed_exprs.append(trace_expr)
                        new_backward_exprs.extend(new_exprs)

                        try:
                            block.backward_exprs.remove(trace_expr)
                        except:
                            pass

            else:

                if (pattern != 'OB' and type(put_data) is str and put_data in trace_sims):

                    new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='F')
                    new_backward_exprs.extend(new_exprs)

                if reg_name in trace_sims:

                    sim = trace_sims[reg_name]
                    if not sim.live:

                        if code_location == sim.def_loc:
                            sim.live = True

                        continue

                    new_exprs = self._find_put_def2(reg_name, put_data, put_size, code_location, trace_expr)

                    if len(new_exprs):
                        killed_exprs.append(trace_expr)
                        new_backward_exprs.extend(new_exprs)

                        try:
                            block.backward_exprs.remove(trace_expr)
                        except:
                            pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _backward_wrtmp_stmt(self, block, action, code_location, backward_exprs):
        """
        In backward, IR "t4 = Get(rdi) or t4 = t5"
        """

        new_backward_exprs = []

        wr_tmp, wr_data, wr_size = action[1], action[2], action[3]

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            pattern = trace_expr.expr.pattern
            if (pattern != 'OB' and wr_data != self.sp_name and wr_data in trace_expr.expr.sims):
                new_alias = self._find_wrtmp_use2(wr_tmp, wr_data, code_location, trace_expr)

                new_backward_exprs.extend(new_alias)

            if wr_tmp in trace_expr.expr.sims:

                new_exprs = self._find_wrtmp_def2(wr_tmp, wr_data, wr_size, code_location, trace_expr)

                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

                    try:
                        block.backward_exprs.remove(trace_expr)
                    except:
                        pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _backward_wrtmp_binop_stmt(self, block, action, code_location, backward_exprs):

        new_backward_exprs = []
        execute_stmt_flag = False
        find_increment_flag = False

        # print("b_binop: %s %s" % (code_location, str(action)))

        wr_tmp, wr_data, wr_size = action[1], action[2], action[3]

        binop = wr_data[0]
        # opnds = wr_data[1]

        killed_exprs = []
        current_idx = code_location.stmt_idx
        stmt = block.irsb.statements[current_idx]

        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            if wr_tmp in trace_expr.expr.sims:

                # print("binop: %s" % (binop))
                if binop in self.ignore_binops:
                    new_wr_data = self.insignificant_symbol

                else:

                    if not execute_stmt_flag:
                        translate_stmt(stmt, self.state)
                        execute_stmt_flag = True

                        new_wr_data = self.state.scratch.tmp_expr(stmt.tmp)

                        if new_wr_data.op in self.shift_ops:
                            new_wr_data= self.convert_shift_operators(new_wr_data)

                    if not find_increment_flag and block.is_loop and code_location in block.inc_locs:
                        print("%s %s has inc %s" % (block, code_location, str(action)))
                        new_wr_data = self._create_increment_data(wr_data, wr_size)
                        print("get inc data: %s" % (new_wr_data))
                        find_increment_flag = True

                new_exprs = self._find_wrtmp_binop_def(wr_tmp, new_wr_data, code_location, trace_expr)

                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

                    try:
                        block.backward_exprs.remove(trace_expr)
                    except:
                        pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _backward_wrtmp_load_stmt(self, block, action, code_location, backward_exprs):

        new_backward_exprs = []
        execute_stmt_flag = False
        is_stack_load = False

        wr_tmp, ld_addrs = action[1], action[2]
        sp_name = 'r%d' % (self.sp_offset)

        if type(ld_addrs) is tuple:
            for ld_sym, ld_offset in ld_addrs:
                if ld_sym == sp_name:
                    is_stack_load = True
                    break

        killed_exprs = []
        current_idx = code_location.stmt_idx
        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            if wr_tmp in trace_expr.expr.sims:

                if not execute_stmt_flag:
                    stmt = block.irsb.statements[current_idx]
                    translate_stmt(stmt, self.state)
                    execute_stmt_flag = True

                    wr_data = self.state.scratch.tmp_expr(stmt.tmp)

                new_exprs = self._find_wrtmp_load_def(wr_tmp, wr_data, code_location, trace_expr)

                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

                    try:
                        block.backward_exprs.remove(trace_expr)
                    except:
                        pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        for new_expr in new_backward_exprs:
            new_expr.expr.ls_idx = current_idx

            if is_stack_load:
                new_expr.expr.trace_dir = 'B'

        return new_backward_exprs

    def _backward_wrtmp_unop_stmt(self, block, action, code_location, backward_exprs):

        new_backward_exprs = []

        wr_tmp, wr_data = action[1], action[2]
        opnds = wr_data[1]

        if len(opnds) != 1:
            l.info("Not support the action: %s" % (action))
            return []

        wr_opnd = opnds[0]
        if type(wr_opnd) is int or 't' not in wr_opnd:
            return []

        killed_exprs = []
        current_idx = code_location.stmt_idx
        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx:
                continue

            if wr_tmp in trace_expr.expr.sims:

                new_exprs = self._find_wrtmp_unop_def(wr_tmp, wr_opnd, code_location, trace_expr)

                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

                    try:
                        block.backward_exprs.remove(trace_expr)
                    except:
                        pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _find_register_store_def2(self, st_addrs, st_data, st_size, code_location, trace_expr):

        # print("b_find_store: %s" % (trace_expr))
        sim_actions = trace_expr.expr.sim_actions

        if len(sim_actions) == 0:
            return []

        # for index, sim_action in sim_actions.items():
        #     print("%d %s (%s)" % (index, sim_action.action_data, sim_action.action_type))

        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            binop = sim_action.binop
            action_data = sim_action.action_data

            if name and action_data.op == 'Load':
                for _op, st_addr in st_addrs:
                    if _op == binop and name == st_addr:
                        load_ptrs.append(action_data)

        if len(load_ptrs) == 0:
            return []

        elif len(load_ptrs) > 1:
            l.info("There are two load ptr should be update!")
            return []

        # print("backward-find-store: %s" % (load_ptrs))

        if type(st_data) is int:

            if st_data == 0:
                l.info("The store data is zero, maybe the callee redefined it. do it future!")

            st_data = claripy.BVV(st_data, st_size)

        elif type(st_data) is str:
            st_data = claripy.BVS(st_data, st_size, explicit_name=True)

        # new_ast_data = trace_expr.expr.ast
        # for load_ptr in load_ptrs:
        #     try:
        #         new_ast_data = new_ast_data.replace(load_ptr, st_data)

        #     except:
        #         l.info("register store def error, %s %s" % (load_ptr, st_data))
        #         return []

        load_ptr = load_ptrs[0]
        new_expr = trace_expr.replace(load_ptr, st_data)

        # new_expr = trace_expr.deep_copy()
        # new_expr.expr.ast = new_ast_data
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB':
            new_expr.expr.trace_dir = 'B'

        # self._update_sims(new_expr)

        # if len(load_ptrs) == 1:
        #     load_ptr = load_ptrs[0]
        #     self._remove_sim_actions(load_ptr, trace_expr, new_expr)

        # else:
        #     l.info("There are two or more load ptr in backward store: %s" % (trace_expr))

        return [new_expr]

    def _find_put_def2(self, reg_name, put_data, put_size, code_location, trace_expr):

        trace_dir = None
        if type(put_data) is int:
            put_data = claripy.BVV(put_data, put_size)
            trace_dir = 'B'

        new_expr = trace_expr.replace(reg_name, put_data)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = trace_dir
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_wrtmp_def2(self, wr_tmp, wr_data, wr_size, code_location, trace_expr):

        if type(wr_data) is int:
            wr_data = claripy.BVV(wr_data, wr_size)

        new_expr = trace_expr.replace(wr_tmp, wr_data)
        new_expr.get_trace_variable(trace_expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if type(wr_data) is str and 'r' in wr_data:
            wr_reg_sim = new_expr.expr.sims[wr_data]
            wr_reg_sim.def_loc = code_location

        return [new_expr]

    def _find_wrtmp_binop_def(self, wr_tmp, wr_data, code_location, trace_expr):

        new_expr = trace_expr.replace(wr_tmp, wr_data)
        new_expr.get_trace_variable(trace_expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_wrtmp_unop_def(self, wr_tmp, wr_data, code_location, trace_expr):

        new_expr = trace_expr.replace(wr_tmp, wr_data)
        # new_expr.get_trace_variable(trace_expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_wrtmp_load_def(self, wr_tmp, wr_data, code_location, trace_expr):

        sim_action = self.create_sim_action(wr_data, code_location)
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(wr_tmp, wr_data, re_sim_actions)
        # new_expr.get_trace_variable(trace_expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        # self._add_load_action(wr_tmp, code_location, trace_expr, new_expr)

        return [new_expr]

    def _find_constant_store_def(self):

        return []

    def _find_loop_increment_data(self, action, code_location, trace_expr):

        op_result = None
        wr_tmp, wr_data, wr_size = action[1], action[2], action[3]
        trace_ast = trace_expr.expr.ast

        print("find loop def: %s %s" % (code_location, trace_expr))
        print("action: %s" % (str(action)))

        binop = wr_data[0]
        opnds = wr_data[1]

        if binop in self.add_binops:
            is_increment = self._is_increment_element(wr_tmp, trace_ast)
            if not is_increment:
                return None

            opnd0 = opnds[0]
            opnd1 = opnds[1]
            if type(opnd0) is str and type(opnd1) is str:
                l.info("The loop increment offset is symbol at %s: %s" % (code_location, str(action)))
                opnd0_ast = claripy.BVS(opnd0, self.arch_bits, explicit_name=True)
                opnd1_ast = claripy.BVS(opnd1, self.arch_bits, explicit_name=True)
                sym_ast = claripy.BVS('i', self.arch_bits, explicit_name=True)
                op_result = opnd0_ast + sym_ast * opnd1_ast

            elif type(opnd1) is int and type(opnd0) is str:
                opnd0_ast = claripy.BVS(opnd0, self.arch_bits, explicit_name=True)
                opnd1_ast = claripy.BVV(opnd1, self.arch_bits)
                sym_ast = claripy.BVS('i', self.arch_bits, explicit_name=True)
                op_result = opnd0_ast + sym_ast * opnd1_ast

            elif type(opnd0) is int and type(opnd1) is str:
                opnd1_ast = claripy.BVS(opnd1, self.arch_bits, explicit_name=True)
                opnd0_ast = claripy.BVV(opnd0, self.arch_bits)
                sym_ast = claripy.BVS('i', self.arch_bits, explicit_name=True)
                op_result = opnd1_ast + sym_ast * opnd0_ast

        else:
            l.info("Now, not support the loop increment def %s: %s" % (code_location, binop))

        return op_result

    def _is_increment_element(self, wr_tmp, trace_ast):

        for child_ast in trace_ast.recursive_children_asts:
            if child_ast.op in self.add_ops:
                child_opnd0 = child_ast.args[0]
                child_opnd1 = child_ast.args[1]

                if (child_opnd0.op == 'BVS' and wr_tmp in child_opnd0.variables):
                    return True

                elif (child_opnd1.op == 'BVS' and wr_tmp in child_opnd1.variables):
                    return True
        return False

    def _loop_constant_increment_with_add(self, wr_tmp, inc_tmp, inc_offset, trace_expr):

        inc_data_ast, inc_offset_ast = None, None
        trace_ast = trace_expr.expr.ast

        for child_ast in trace_ast.recursive_children_asts:
            if child_ast.op in self.add_ops:
                child_opnd0 = child_ast.args[0]
                child_opnd1 = child_ast.args[1]

                if (child_opnd1.concrete and child_opnd1.args[0] == inc_offset and (child_opnd0.op == 'BVS' or self._is_increment_element(child_opnd0)) and wr_tmp in child_opnd0.variables):
                    inc_data_ast = child_opnd0
                    inc_offset = child_opnd1
                    break

                elif (child_opnd0.concrete and child_opnd0.args[0] == inc_offset and (child_opnd1.op == 'BVS' or child_opnd1.op in self.add_ops) and wr_tmp in child_opnd1.variables):
                    inc_data_ast = child_opnd1
                    inc_offset = child_opnd0
                    break

        if inc_data_ast is None or inc_offset is None:
            return

        print("In loop find: %s %s" % (inc_data_ast, inc_offset))

    def _create_increment_data(self, wr_data_info, wr_size):
        binop = wr_data_info[0]
        opnds = wr_data_info[1][0]
        inc_sym, inc_offset = None, None
        inc_data = None

        if 'Add' in binop:
            for opnd in opnds:
                if type(opnd) is int:
                    inc_offset = opnd
                elif type(opnd) is str:
                    inc_sym = opnd

            if inc_sym and inc_offset:
                sym_ast = claripy.BVS(inc_sym, wr_size, explicit_name=True)
                i = claripy.BVS('i', wr_size, explicit_name=True)
                inc_data = sym_ast + i * inc_offset

        elif 'Sub' in binop:
            for opnd in opnds:
                if type(opnd) is int:
                    inc_offset = opnd
                elif type(opnd) is str:
                    inc_sym = opnd

            if inc_sym and inc_offset:
                sym_ast = claripy.BVS(inc_sym, wr_size, explicit_name=True)
                i = claripy.BVS('i', wr_size, explicit_name=True)
                inc_data = sym_ast - i * inc_offset

        return inc_data

    def _kill_reg_defined(self, reg_name, trace_expr, code_location, killed_exprs):
        """
        In forward trace, the reg could be redefined.
        One: load(rax+0x8), and put(rax) = rbx, then expr load(rax+0x8) should be killed.
        two: load(rax+rdi), and put(rax) = rbx, then reg rax is killed, but we should reserve the expr and copy it.
        """
        sp_name = 'r%d' % (self.sp_offset)
        # print("    %s %s" % (reg_name, trace_expr.trace_vars))
        if reg_name != sp_name and reg_name in trace_expr.expr.trace_vars:
            killed_exprs.append(trace_expr)
            if len(trace_expr.expr.trace_vars) >= 2:
                new_expr = trace_expr.deep_copy()
                new_expr.expr.trace_vars.remove(reg_name)
                new_expr.expr.killed_vars.add(reg_name)
                # new_expr.expr.location = code_location
                new_expr.index = code_location.stmt_idx
                return new_expr

    def check_block_killed_define(self, block, killed_alias_ids, flow_dir):
        block_addr = block.addr
        for expr in block.done_exprs:
            expr_addr = expr.location.block_addr
            if expr_addr == block_addr:
                self._check_expr_defined(expr, forward_exprs)

    def _check_expr_redefined(self, block_expr, forward_exprs):
        for forward_expr in forward_exprs:
            if forward_expr.is_ast_equal(block_expr):
                self.killed_alias_ids.add(forward_expr.alias_id)

    def find_alias_variable(self, state, irsb, trace_vars, alias, index=0):
        pass

    def _search_store_tmp(self, irsb, stmt, code_location, sp_tmp):
        """
        Find a tmp's definition by backward trace. Check whether the tmp variable is related to stack.
        There are two cases, e.g.
            t8 = Get(rsp)
            -------------
            t9 = Add(t8, 0x24)
        :return a ast variable or None
        """
        # dst_addr = None
        store_addr_tmp = stmt.addr.tmp
        stmts = irsb.statements
        current_idx = code_location.stmt_idx
        for idx in range(current_idx-1, -1, -1):
            pre_stmt = stmts[idx]
            if (isinstance(pre_stmt, pyvex.stmt.WrTmp) and
                    not isinstance(pre_stmt.data, pyvex.expr.ITE)):
                if pre_stmt.tmp == store_addr_tmp:
                    translate_stmt(pre_stmt, self.state)
                    dst_addr = self.state.scratch.tmp_expr(pre_stmt.tmp)
                    sp_tmp_name = 't%d' % (sp_tmp)
                    if sp_tmp_name in dst_addr.variables:
                        return dst_addr
                    break
        return None

    def _find_reg_load_tmp_define(self, irsb, stmt, code_location, load_info):
        """
        Find a load addr tmp's definition by backward trace.
        Check whether the tmp variable is related to register.
        There are four cases, e.g.
            t8 = Get(rbp) or Put(rbp) = t8
            -------------
            t9 = Add(t8, 0x24)
            t12 = LDle(t9) or t12 = LDle(t8)
        :return true if find the store else false
        """
        find_reg, find_offset = None, None
        search_reg = None
        trace_tmp = stmt.data.addr.tmp
        stmts = irsb.statements
        current_idx = code_location.stmt_idx

        for idx in range(current_idx-1, -1, -1):
            pre_stmt = stmts[idx]
            if isinstance(pre_stmt, pyvex.stmt.WrTmp):
                if pre_stmt.tmp != trace_tmp:
                    continue

                if isinstance(pre_stmt.data, pyvex.expr.Get):
                    get_reg_name = 'r%d' % (pre_stmt.data.offset)
                    if find_offset is not None:
                        if get_reg_name == search_reg:
                            find_reg = get_reg_name

                    else:
                        if get_reg_name in load_info:
                            offset_info = load_info[get_reg_name]
                            if 0 in offset_info.keys():
                                find_reg = get_reg_name
                                find_offset = 0

                    break

                if find_offset is None:
                    if (isinstance(pre_stmt.data, pyvex.expr.Binop) and
                            pre_stmt.data.op in self.add_binops):

                        offset, tmp = None, None
                        for child_expr in pre_stmt.data.args:
                            if isinstance(child_expr, pyvex.expr.Const):
                                offset = child_expr.con.value
                            elif isinstance(child_expr, pyvex.expr.RdTmp):
                                tmp = child_expr.tmp

                        # print("Find binop with %s %s" % (tmp, offset))
                        if offset is None or tmp is None:
                            break

                        for reg_name, offset_info in load_info.items():
                            # print("DEBUG offset %d" % (offset))
                            # print(offset_info.keys())
                            if offset in offset_info.keys():
                                search_reg = reg_name
                                find_offset = offset
                                break

                        if find_offset is not None:
                            trace_tmp = tmp
                        else:
                            break

                    else:
                        # l.info("Now we don't support the stmt %s" % (pre_stmt))
                        break

                else:
                    break

            elif isinstance(pre_stmt, pyvex.stmt.Put):
                put_reg_name = 'r%d' % (pre_stmt.offset)
                if put_reg_name in load_info:
                    offset_info = load_info[put_reg_name]
                    # print("find put: %s" % (pre_stmt))
                    # print("trace tmp %s" % (trace_tmp))
                    # print(put_reg_name, search_reg)

                    if (isinstance(pre_stmt.data, pyvex.expr.RdTmp) and
                            pre_stmt.data.tmp == trace_tmp):
                        # print("Find Yes!!!")
                        if find_offset is None:
                            if 0 in offset_info.keys():
                                find_reg = put_reg_name
                                find_offset = 0
                        elif put_reg_name == search_reg:
                            # if find_offset in offset_info.keys():
                            find_reg = put_reg_name

                        break

        # print("Find: reg %s, offset %s" % (find_reg, find_offset))
        if find_reg and find_offset is not None:
            return (find_reg, find_offset)
        else:
            return None

    def _find_register_load_use(self, irsb, stmt, expr, code_location):
        """
        t4 = Get(rsi)
        t2 = LDle(t4)
        """
        symbols = set()

        # case 1: only trace the 'bp'or 'sp' register
        bp_sym = 'r%d' % (self.proj.arch.bp_offset)
        symbols.add(bp_sym)
        sp_sym = 'r%d' % (self.sp_offset)
        symbols.add(sp_sym)

        # case 2: trace the register in expr
        # TODO

        load_info = find_load_with_symbols(expr.expr.ast, symbols)
        # print("load info: %s" % (load_info))
        if len(load_info) == 0:
            return None

        find_result = self._find_reg_load_tmp_define(irsb, stmt, code_location, load_info)

        if find_result is None:
            return None

        load_ptr = load_info[find_result[0]][find_result[1]]
        print("Find reg load: %s %s" % (stmt, load_ptr))

        var = 't%d' % (stmt.tmp)
        wrtmp = claripy.BVS(var, self.arch_bits, explicit_name=True)

        new_expr = expr.replace(load_ptr, wrtmp)
        new_expr.get_trace_variable(expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx

        return new_expr


    def _find_load_value(self, irsb, stmt, expr, code_location):
        """
        Trace the data in a mem, for example:
            t12 = LDle(t30), <BV64 t30>: <BV64 0x401670>
            then we trace the t12.
        """
        wrtmp = stmt.tmp
        load_addr_tmp = stmt.data.addr.tmp
        load_addr_sym = 't%d' % (load_addr_tmp)
        if load_addr_sym not in expr.expr.trace_vars:
            return None

        load_addr = expr.expr.value
        if isinstance(load_addr, int):
            load_addr = claripy.BVV(load_addr, self.arch_bits)

        elif load_addr.symbolic:
            l.info("The expr's value is symbolic, do it future!" % (expr))
            return None

        self.state.scratch.store_tmp(load_addr_tmp, load_addr)
        translate_stmt(stmt, self.state)
        load_value = self.state.scratch.tmp_expr(wrtmp)
        # print("Find load value: %s" % (load_value))

        trace_ast = claripy.BVS('t%d' % (wrtmp), load_value.size(), explicit_name=True)

        new_expr = expr.deep_copy()
        new_expr.expr.ast = trace_ast
        new_expr.expr.value = load_value
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.get_trace_variable()
        new_expr.index = code_location.stmt_idx
        return new_expr

    def _find_load_use(self, irsb, stmt, trace_expr, code_location, sp_tmp):
        """
        t10 = LDle(t12)
        """
        new_expr = None
        # print("DEBUG: find_load_use %s" % (stmt))
        # print("expr %s" % (trace_expr))

        if isinstance(stmt.data.addr, pyvex.expr.RdTmp):
            # Fisrt case: the expr is <BV64 t30>: <BV64 0x401670>.
            if trace_expr.expr.ast.op == 'BVS':
                new_expr = self._find_load_value(irsb, stmt, trace_expr, code_location)

            # Second case: find register load.
            else:
                new_expr = self._find_register_load_use(irsb, stmt, trace_expr, code_location)

        else:
            # Second case: find constant (.bss, .data) load.
            l.info("%s will be done in future!" % (stmt))
            self._find_constant_load_use()

        return new_expr

    def _find_store_use(self, irsb, stmt, code_location, trace_expr, sp_tmp):
        """
        For the IR "STle(t19) = t9", the tmp t9 is used, could be replaced with 'Load(t19)'
        :param stmt:
        :param trace_expr:
        """
        use_flag = False
        if code_location in trace_expr.expr.store_location:
            return None

        if (isinstance(stmt.data, pyvex.expr.RdTmp) and
                't%d' % stmt.data.tmp in trace_expr.expr.trace_vars):
            use_flag = True

        if use_flag and isinstance(stmt.addr, pyvex.expr.RdTmp):
            _dir = 'N'
            dst_var = 't%d' % (stmt.addr.tmp)
            src_var = 't%d' % (stmt.data.tmp)

            if sp_tmp is None:
                dst_addr = claripy.BVS(dst_var, self.arch_bits, explicit_name=True)

            else:
                if stmt.addr.tmp == sp_tmp:
                    _dir = 'F'
                    sp_reg_name = 'r%d' % self.sp_offset
                    dst_addr = claripy.BVS(sp_reg_name, self.arch_bits, explicit_name=True)

                else:
                    dst_addr = self._search_store_tmp(irsb, stmt, code_location, sp_tmp)
                    if dst_addr is not None:
                        _dir = 'F'
                        sp_reg_name = 'r%d' % self.sp_offset
                        sp_tmp_name = 't%d' % sp_tmp
                        sp_tmp_data = claripy.BVS(sp_tmp_name, self.arch_bits, explicit_name=True)
                        sp_reg_data = claripy.BVS(sp_reg_name, self.arch_bits, explicit_name=True)
                        dst_addr = dst_addr.replace(sp_tmp_data, sp_reg_data)

                    else:
                        dst_addr = claripy.BVS(dst_var, self.arch_bits, explicit_name=True)

            dst_data = claripy.Load(dst_addr, self.arch_bits)
            new_expr = trace_expr.replace(src_var, dst_data)
            new_expr.get_trace_variable(trace_expr.expr.killed_vars)
            new_expr.expr.store_location.append(code_location)
            new_expr.expr.trace_dir = _dir
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            return new_expr

    def _find_wrtmp_use(self, stmt, trace_expr, code_location):
        """
        There are three case for writing a tmp
        First: t21 = Add64(t19,0x0000000000000008)
        Second: t2 = GET:I64(rbx)
        Third: t20 = LDle:I64(t18)
        We only think about the first and second case. the third case (TODO)
        """
        use_flag = False
        comparison_ops = ['Iop_CmpEQ64']

        if isinstance(stmt.data, pyvex.expr.Binop):
            _op = stmt.data.op # TODO
            # if _op in comparison_ops:
            #     return None

            for child_expr in stmt.data.child_expressions:
                if (isinstance(child_expr, pyvex.expr.RdTmp) and
                        't%d' % child_expr.tmp in trace_expr.expr.trace_vars):
                    use_flag = True
                    src_var = 't%d' % (child_expr.tmp)
                    self._initialize_execute_variable(child_expr.tmp, 't', trace_expr)
                    break

        elif (isinstance(stmt.data, pyvex.expr.Get) and
              stmt.data.offset != self.sp_offset and
              'r%d' % stmt.data.offset in trace_expr.expr.trace_vars):
            use_flag = True
            src_var = 'r%d' % (stmt.data.offset)
            self._initialize_execute_variable(stmt.data.offset, 'r', trace_expr)

        if use_flag:
            # print("Find wrtmp use %s" % (stmt))
            translate_stmt(stmt, self.state)
            dst_var = 't%d' % (stmt.tmp)
            src_data = self.state.scratch.tmp_expr(stmt.tmp)
            dst_data = claripy.BVS(dst_var, src_data.size(), explicit_name=True)
            # print("Test: expr %s, src %s, dst %s" % (trace_expr, src_var, dst_data))
            new_expr = trace_expr.replace(src_var, dst_data)
            new_expr.get_trace_variable(trace_expr.expr.killed_vars)
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            if src_data.op == 'BVV':
                new_expr.expr.value = src_data
            return new_expr

    def _find_wrtmp_use_without_binop(self, stmt, trace_expr, code_location):
        """
        e.g.Load(r24 + 0x48)
            t8 = Get(r24)
        Update: Load(t8 + 0x48)
        """
        use_flag = False

        if (isinstance(stmt.data, pyvex.expr.Get) and
            stmt.data.offset != self.sp_offset and
            'r%d' % stmt.data.offset in trace_expr.expr.trace_vars):
            use_flag = True

        if use_flag:
            # print("Find wrtmp use %s" % (stmt))
            translate_stmt(stmt, self.state)
            dst_var = 't%d' % (stmt.tmp)
            src_var = 'r%d' % (stmt.data.offset)
            new_expr = trace_expr.replace(src_var, dst_var)
            new_expr.get_trace_variable(trace_expr.expr.killed_vars)
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            return new_expr

    def _find_put_use(self, stmt, trace_expr, code_location):
        """
        For example expr Load(t24)
        Put(rax) = t24, replace t24 with rax.
        """
        if stmt.offset >= self.max_offset:
            return None

        use_flag = False
        if (isinstance(stmt.data, pyvex.expr.RdTmp) and
            't%d' % stmt.data.tmp in trace_expr.expr.trace_vars):
            use_flag = True
            src_var = 't%d' % stmt.data.tmp
            self._initialize_execute_variable(stmt.data.tmp, 't', trace_expr)

        if use_flag:
            # print("Find put use %s" % (stmt))
            translate_stmt(stmt, self.state)
            dst_var = 'r%d' % (stmt.offset)
            new_expr = trace_expr.replace(src_var, dst_var)
            new_expr.get_trace_variable(trace_expr.expr.killed_vars)
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            return new_expr

    def _find_tmp_use(self, state, stmt, trace_var):
        use_flag = False
        dst_var, data = None, None

        if isinstance(stmt.data, pyvex.expr.Binop):
            for child_expr in stmt.data.child_expressions:
                if (isinstance(child_expr, pyvex.expr.RdTmp) and
                    't%d' % child_expr.tmp == trace_var):
                    use_flag = True

        elif (isinstance(stmt.data, pyvex.expr.RdTmp) and
              't%d' % stmt.data.tmp == trace_var):
            use_flag = True

        if use_flag:
            # print("Find use %s" % (stmt))
            translate_stmt(stmt, state)
            if isinstance(stmt, pyvex.stmt.WrTmp):
                dst_var = 't%d' % (stmt.tmp)
                data = state.scratch.tmp_expr(stmt.tmp)

            elif isinstance(stmt, pyvex.stmt.Put):
                dst_var = 'r%d' % (stmt.offset)
                data = state.registers.load(stmt.offset)

            elif isinstance(stmt, pyvex.stmt.Store):
                if isinstance(stmt.addr, pyvex.expr.RdTmp):
                    dst_var = 't%d' % (stmt.addr.tmp)
                    data = state.scratch.tmp_expr(stmt.data.tmp)
                    v = claripy.BVS(dst_var, state.arch.bits, explicit_name=True)
                    dst_data = claripy.Load(v, data.size())

        return dst_var, data

    def _find_reg_use(self, state, stmt, trace_var):
        use_flag = False
        dst_var, data = None, None

        if (isinstance(stmt.data, pyvex.expr.Get) and
            'r%d' % stmt.data.offset == trace_var):
            use_flag = True

        if use_flag:
            # print("Find reg use %s" % (stmt))
            translate_stmt(stmt, state)
            if isinstance(stmt, pyvex.stmt.WrTmp):
                dst_var = 't%d' % (stmt.tmp)
                data = state.scratch.tmp_expr(stmt.tmp)

        return dst_var, data

    def _find_stack_use(self, state, stmt, trace_var):
        pass

    def get_esp_tmp(self, irsb):
        icount = 0
        for stmt in irsb.statements:
            if isinstance(stmt, pyvex.IRStmt.IMark):
                icount += 1
                if icount == irsb.instructions and irsb.jumpkind == 'Ijk_Call':
                    break
            if (isinstance(stmt, pyvex.stmt.WrTmp) and
                isinstance(stmt.data, pyvex.expr.Get)):
                reg_offset = stmt.data.offset
                if reg_offset == self.sp_offset:
                    return stmt.tmp

    def get_stack_size_and_tmp(self, irsb):
        inss = []
        sp_tmp = None
        icount = 0
        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv

        for stmt in irsb.statements:
            if isinstance(stmt, pyvex.IRStmt.IMark):
                icount += 1
                ins = []
                if icount == irsb.instructions and irsb.jumpkind == 'Ijk_Call':
                    break
            ins.append(stmt)
            if isinstance(stmt, pyvex.stmt.Put):
                if stmt.offset == self.sp_offset:
                    inss.extend(ins)
                    if isinstance(stmt.data, pyvex.expr.RdTmp):
                        sp_tmp = stmt.data.tmp
        for stmt in inss:
            translate_stmt(stmt, self.state)
        sp = self.state.registers.load(self.sp_offset)
        # TODO
        new_sp = self.state.solver.BVS('r48', self.arch_bits, explicit_name=True) - sp
        return sp_tmp, self.state.solver.simplify(new_sp)

    def get_callsite_target(self, block):
        l.debug("callsite %s target" % (block))
        irsb = block.irsb
        if isinstance(irsb.next, pyvex.expr.Const):
            target_addr = irsb.next.con.value
            target_addr = self.parse_thunk_jmp_target(target_addr)
        else:
            target_addr = None
        return target_addr

    def parse_thunk_jmp_target(self, addr):
        """
        Some functions are thunk, only has one instruction. e.g.
        jmp cs:0ff_7E3A48
        """
        l.debug("thunk jmp %x" % (addr))
        irsb = self.state.block(addr).vex
        if len(irsb.statements) == 2:
            s1 = irsb.statements[1]
            if (type(s1) is pyvex.stmt.WrTmp and
                    type(s1.data) is pyvex.expr.Load and
                    type(s1.data.addr) is pyvex.expr.Const):
                load_addr = s1.data.addr.con.value
                target_addr = self.state.memory.load(load_addr, endness='Iend_LE')
                if target_addr.concrete:
                    return self.state.solver.eval_one(target_addr)
        return addr

    def get_constraint(self, block):
        # print("\nLoop block %s get constraints" % (block))
        irsb = block.irsb
        # irsb.pp()
        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv

        constraint = None
        stmts = irsb.statements
        for i in range(len(stmts)-1, -1, -1):
            stmt = stmts[i]
            if stmt.tag is 'Ist_IMark':
                continue

            if type(stmt) is pyvex.stmt.WrTmp and type(stmt.data) is pyvex.expr.Binop:
                wrtmp = stmt.tmp
                _op = stmt.data.op
                if 'Cmp' in _op:
                    # last_cmp_op = _op
                    translate_stmt(stmt, self.state)
                    constraint = self.state.scratch.tmp_expr(wrtmp)
                    break

        return constraint

    def parse_bool_condition(self, bool_con):
        cc_deps = []
        if len(bool_con.args) == 2:
            cc_dep1 = bool_con.args[0]
            cc_dep2 = bool_con.args[1]
            cc_deps.append((cc_dep1, cc_dep2))

        else:
            l.info("The bool expr %s have not two args, do it future!" % (bool_con))

        return cc_deps

    def trace_constraint_dep(self, block, con_exprs, sp_tmp):
        bb = block.shallow_copy()
        self.backward_data_trace(bb, con_exprs, sp_tmp)

    def get_constraint_bak(self, block):
        print("\nLoop block %s get constraints" % (block))
        irsb = block.irsb
        # irsb.pp()
        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv
        for stmt in irsb.statements:
            translate_stmt(stmt, self.state)
            # if type(stmt) is pyvex.stmt.WrTmp and type(stmt.data) is pyvex.expr.Binop:
                # data = self.state.scratch.tmp_expr(stmt.tmp)
                # print("%s get %s" % (stmt, data))
        cc_dep1 = self.state.registers.load('cc_dep1')
        cc_dep2 = self.state.registers.load('cc_dep2')
        print("get constraints %s %s" % (cc_dep1, cc_dep2))
        return cc_dep1, cc_dep2

    def get_constraint_copy(self, block):
        print("\nLoop block %s get constraints" % (block))
        irsb = block.irsb
        # irsb.pp()
        self.state.scratch.temps = {}
        self.state.scratch.tyenv = irsb.tyenv

        last_cmp_op = None
        cmp_dep1, cmp_dep2 = None, None
        constraint = None

        stmts = irsb.statements
        for i in range(len(stmts)-1, -1, -1):
            stmt = stmts[i]
            if stmt.tag is 'Ist_IMark':
                continue

            if last_cmp_op and cmp_dep1 and cmp_dep2:
                break

            if type(stmt) is pyvex.stmt.WrTmp and type(stmt.data) is pyvex.expr.Binop:
                wrtmp = stmt.tmp
                _op = stmt.data.op
                if 'Cmp' in _op:
                    last_cmp_op = _op
                    translate_stmt(stmt, self.state)
                    constraint = self.state.scratch.tmp_expr(wrtmp)
                    break

            elif type(stmt) is pyvex.stmt.Put:
                if stmt.offset == self.cc_dep1_offset:
                    if type(stmt.data) is pyvex.expr.RdTmp:
                        cmp_dep1 = stmt.data.tmp
                    elif type(stmt.data) is pyvex.expr.Const:
                        cmp_dep1 = stmt.data.con.value

                if stmt.offset == self.cc_dep2_offset:
                    if type(stmt.data) is pyvex.expr.RdTmp:
                        cmp_dep2 = stmt.data.tmp
                    elif type(stmt.data) is pyvex.expr.Const:
                        cmp_dep2 = stmt.data.con.value

        print("constraints: %s %s %s" % (last_cmp_op, cmp_dep1, cmp_dep2))
        if constraint is not None:
            print("con: %s" % (constraint))
        return cmp_dep1, cmp_dep2

    # TODO
    def simplify_expr(self, expr):
        """
        Simplify a claripy ast
        """
        return
        simply_asts = []
        for child_ast in expr.expr.ast.recursive_children_asts:
            # print(child_ast)
            simplify_flag = False
            if child_ast.op in self.simplify_ops:
                if len(child_ast.args) >= 3:
                    simplify_flag = True

                elif len(child_ast.args) == 2:
                    if child_ast.args[0].op in self.simplify_ops:
                        simplify_flag = True
                    elif child_ast.args[1].op in self.simplify_ops:
                        simplify_flag = True

                if simplify_flag:
                    simple_ast = self.state.simplify(child_ast)
                    if simple_ast.__hash__() != child_ast.__hash__():
                        simply_asts.append((child_ast, simple_ast))
                        break

        # print("simplify:\n %s" % (simply_asts))
        if len(simply_asts):
            # print("simpily before %s" % (expr))
            new_ast = expr.expr.ast
            for child_ast, simple_ast in simply_asts:
                new_ast = new_ast.replace(child_ast, simple_ast)
            expr.expr.ast = new_ast
            expr.get_trace_variable(expr.expr.killed_vars)
            # print("The simplify expr %s" % (expr))

    def convert_shift_operators(self, data):
        if len(data.args) != 2:
            l.info("The data %s has complex operators" % (data))
            return data

        new_data = data
        arg_1 = data.args[0]
        arg_2 = data.args[1]
        if arg_2.concrete:
            shift_count = arg_2.args[0]
            if shift_count <= 15:
                value = 2**shift_count
                value_ast = claripy.BVV(value, self.arch_bits)
                new_data = arg_1 * value_ast
            else:
                l.info("The shift count > 15, we igonre %s!" % (data))
        else:
            l.info("The shift is symbolc, simplify %s future!" % (data))
        return new_data

    def _update_sims(self, trace_expr):
        old_sims = trace_expr.expr.sims
        new_sims = {}
        symbols = trace_expr.get_trace_symbols()

        for sym in symbols:
            if sym not in old_sims:
                if 'r' in sym:
                    new_sims[sym] = Sim()

                else:
                    new_sims[sym] = None

            else:
                new_sims[sym] = old_sims[sym]

        trace_expr.expr.sims = new_sims

    def get_user_trace_data(self, block, user_location):
        """
        :param block: a cfg block
        :param user_location: a CodeLocation, which is defined by user for data tracing.
        """
        irsb = block.irsb
        # irsb.pp()
        statements = irsb.statements
        stmt = statements[user_location.stmt_idx]
        # print(stmt)

        if type(stmt) is pyvex.stmt.Store:
            addr_tmp = 't%d' % (stmt.addr.tmp)
            addr_data = claripy.BVS(addr_tmp, self.arch_bits, explicit_name=True)
            trace_data = claripy.Store(addr_data, self.arch_bits)
            return trace_data

        elif hasattr(stmt, 'data') and isinstance(stmt.data, pyvex.expr.RdTmp):
            tmp = stmt.data.tmp
            trace_data = claripy.BVS('t%d' % (tmp), self.arch_bits, explicit_name=True)
            return trace_data

    def create_sim_action(self, action_data, def_loc):
        all_deref_info = get_all_deref_info(action_data)
        deref_info = all_deref_info[0]

        name, binop, data = deref_info[0], deref_info[1], deref_info[2]
        new_sim_action = SimAction(name, binop, data)
        new_sim_action.def_locs.add(def_loc)

        return new_sim_action
