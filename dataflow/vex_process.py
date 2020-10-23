#!/usr/bin/env python

import pyvex
import claripy
import networkx
from collections import defaultdict
from pyvex.const import get_type_size

from .binary_info import BinaryInfo
from .irop import translate
from .variable_expression import VarExpr, TraceExpr, SimAction, Sim
# from .vex.statements import translate_stmt
from .parse_ast import *
from .code_location import CodeLocation
from .errors import NoSupportVEXExpr, NoSupportType
from .global_config import basic_types, arch_info
from .variable_type import *


import logging
l = logging.getLogger("vex_process")
l.setLevel('INFO')


choose_register = True

choose_action_types = ['w', 'wo', 'p', 'wu', 'wn']


class Action(object):

    def __init__(self, action_type, code_location, dst, src, var_size):

        self.action_type = action_type
        self.code_location = code_location
        self.dst = dst
        self.src = src
        self.var_size = var_size

        self.dst_alias = None
        self.src_alias = None
        self.addr_value = None
        self.value = None

        self.argument = None

        # Label the definition's right src type (S, G, H, I, etc.)
        self.src_type = None
        # Label the store/load addr's type (S, G, H, I, etc.)
        self.addr_type = None
        # Label the variable's data type (int-immediate, ptr, char)
        self.var_type = None

        # Record alias source code_location.
        self.src_locs = None
        self.dst_locs = None

        # Record loop block inc variable info.
        self.inc_flag = 0
        self.inc_base = None
        self.inc_offset = None

        # Record loop link load instruction.
        self.link_flag = 0

    def __repr__(self):
        rep = "<\n Action (%s - %d - %s)\n dst: %s\n src: %s\n dst_alias: %s\n src_alias: %s\n"\
            % (self.code_location, self.var_size, self.action_type,\
               self.dst, self.src, self.dst_alias, self.src_alias)
        if type(self.addr_value) is int:
            rep += " addr_value: %x\n" % (self.addr_value)
        elif type(self.addr_value) is list:
            rep += " addr_value: %s\n" % (['%x' % v for v in self.addr_value])

        if type(self.value) is int:
            rep += " value: %x\n" % (self.value)
        elif type(self.value) is list:
            rep += " value: %s\n" % (['%x' % v for v in self.value])
        rep += " addr_type: %s, src_type: %s, var_type: %s\n" % (self.addr_type, self.src_type, self.var_type)
        rep += ">"
        return rep


    def copy(self):
        new_action = Action(self.action_type, self.code_location, self.dst, self.src, self.var_size)
        new_action.dst_alias = self.dst_alias
        new_action.src_alias = self.src_alias
        new_action.addr_value = self.addr_value
        new_action.value = self.value

        new_action.src_type = self.src_type
        new_action.addr_type = self.addr_type
        new_action.var_type = self.var_type

        new_action.src_locs = self.src_locs
        new_action.dst_locs = self.dst_locs

        new_action.inc_flag = self.inc_flag
        new_action.inc_base = self.inc_base
        new_action.inc_offset = self.inc_offset
        new_action.link_flag = self.link_flag

        return new_action

    def merge(self, other):
        """
        Merge two actions. Now mainly think about merge values
        """
        if self.value == other.value:
            return self

        # print("old-value: %s" % (self.value))
        # print("new-value: %s" % (other.value))
        new_values = []
        if type(self.value) is int:
            new_values.append(self.value)
        elif type(self.value) is list:
            new_values.extend(self.value)

        if type(other.value) is int:
            new_values.append(other.value)
        elif type(other.value) is list:
            new_values.extend(other.value)

        if len(new_values):
            new_action = self.copy()
            new_values = list(set(new_values))
            if len(new_values) == 1:
                new_action.value = new_values[0]
            else:
                new_action.value = new_values
            # print("rrr-> %s %s" % (self.code_location, new_values))
            # print("new-action: %s" % (new_action))
            return new_action
        else:
            return self

    def get_dst_type(self):
        if self.src_value:
            if type(self.src_value) is int:
                value = self.src_value
            else:
                value = self.src_value[0]

            pe = get_mem_permission(value)
            if pe == 'imm':
                return 'I'
            elif pe == 'stack':
                return 'S'
            else:
                return 'G'
        return 'N'

    def get_addr_type(self):
        pass

    def get_concrete_src_type(self, value):
        if not isinstance(value, int) or value is None:
            return None

        lable = get_value_label(value)
        return lable


class LiveSims(object):

    def __init__(self, name, stype):

        self.name = name
        self.stype = stype

    def __eq__(self, other):
        return type(other) is LiveSims and self.name == other.name

    def __hash__(self):
        return hash(self.name)


class EngineVEX(BinaryInfo):
    """
    Parse the IR vex statements.
    """

    def __init__(self, project):

        super(EngineVEX, self).__init__(project)

        self.insignificant_symbol = BVS('o')
        # self.state = self.proj.factory.blank_state()
        # self.solver = claripy.Solver()

    def _get_branch_conditoin(self, block, stmt, live_defs):

        target = 0
        guard = None
        dst_tag = stmt.dst.tag
        if 'Ico' in dst_tag:
            target = stmt.dst.value

        if target and hasattr(stmt, 'guard') and isinstance(stmt.guard, pyvex.expr.RdTmp):
            guard_tmp = 't%d' % stmt.guard.tmp
            guard_at = live_defs[guard_tmp]
            guard_alias = guard_at.src_alias if guard_at.src_alias else guard_at.src
            # block.irsb.pp()
            # print("Get-guard-%x" % (block.addr))
            # print("guard: %s" % (str(guard_alias)))
            # print("guard_at: %s" % (guard_at))

            if guard_alias is None:
                return

            guard_ast = self.calculate_binop_stmt_v2(guard_alias)

            if guard_at.action_type == 'wn':
                true_guard = guard_ast == 0
                false_guard = guard_ast != 0

            else:
                true_guard = guard_ast != 0
                false_guard = guard_ast == 0

            # print("ture- %s false- %s" % (true_guard, false_guard))
            slt_guard = None
            op1, op2 = guard_alias[1]
            if ((op2 == 0 or op2 == 1) and
                    type(op1) is str and 't' in op1):
                op1_at = live_defs[op1]
                if op1_at.action_type == 'wo':
                    op1_alias = op1_at.src_alias if op1_at.src_alias else op1_at.src
                    binop = op1_alias[0]
                    if 'Cmp' in binop:
                        slt_guard = self.calculate_binop_stmt_v2(op1_alias)

            if slt_guard is not None:
                cmpop = true_guard.op
                if '_' in cmpop:
                    guard_op = cmpop[2:4]
                else:
                    guard_op = self.get_claripy_operation(cmpop)

                # print("mips-slt: %s" % (slt_guard))
                if op2 == 0 and guard_op == 'eq':
                    true_guard = slt_guard == 0
                    false_guard = slt_guard != 0
                elif op2 == 0 and guard_op != 'eq':
                    true_guard = slt_guard != 0
                    false_guard = slt_guard == 0
                elif op2 == 1 and guard_op == 'eq':
                    true_guard = slt_guard != 0
                    false_guard = slt_guard == 0
                elif op2 == 1 and guard_op != 'eq':
                    true_guard = slt_guard == 0
                    false_guard = slt_guard != 0

                # true_guard = slt_guard != 0
                # false_guard = slt_guard == 0

            # print("guard-ast: %s ture- %s false- %s" % (guard_ast, true_guard, false_guard))
            for succ_block in block.successors:
                if succ_block.addr == target:
                    succ_block.guard[block.addr] = true_guard
                    # print("succ-block %s has %s" % (succ_block, true_guard))

                else:
                    succ_block.guard[block.addr] = false_guard
                    # print("succ-block %s has %s" % (succ_block, false_guard))

    def _addr_tmp_with_binop(self, addr_tmp, tmp_alias):
        alias = tmp_alias[addr_tmp]

        for data in alias:
            if type(data) is tuple:
                binop = data[0]

                if 'Add' in binop or 'Sub' in binop:
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

    def _judge_base_offset(self, opnds, live_defs):
        """
        Judge the txx = Add(base, offset), which is base and offset.
        """
        opnd_0, opnd_1 = opnds[0][0], opnds[1][0]
        value0_type, value1_type = None, None

        if type(opnd_0) is str:
            opnd0_info = live_defs[opnd_0]
            if opnd0_info[0] == 'w':
                opnd_0 = opnd0_info[2]

        if type(opnd_1) is str:
            opnd1_info = live_defs[opnd_1]
            if opnd1_info[0] == 'w':
                opnd_1 = opnd1_info[2]

        if type(opnd_0) is int:
            value0_type = get_mem_permission(opnd_0)
        if type(opnd_1) is int:
            value1_type = get_mem_permission(opnd_1)

        if value0_type and value1_type:
            result = (opnd_0+opnd_1, 0)
        elif value1_type:
            result = (opnd_0, opnd_1) if value1_type == 'imm' else (opnd_1, opnd_0)
        elif value0_type:
            result = (opnd_1, opnd_0) if value0_type == 'imm' else (opnd_0, opnd_1)
        else:
            result = (opnd_0, opnd_1)

        return result

    def _judge_base_offset_v2(self, opnds, opnds_size, opnds_type):
        """
        Judge the txx = Add(base, offset), which is base and offset.
        """
        opnd_0, opnd_1 = opnds[0], opnds[1]
        o0_size, o1_size = opnds_size[0], opnds_size[1]
        value0_type, value1_type = opnds_type

        # if type(opnd_0) is int:
        #     value0_type = get_mem_permission(opnd_0)
        # if type(opnd_1) is int:
        #     value1_type = get_mem_permission(opnd_1)

        if value1_type:
            if value1_type and value1_type != 'ptr':
                base_offset = (opnd_0, opnd_1)
                r_size = (o0_size, o1_size)
                r_type = (value0_type, value1_type)
            else:
                base_offset = (opnd_1, opnd_0)
                r_size = (o1_size, o0_size)
                r_type = (value1_type, value0_type)

        elif value0_type:
            if value0_type and value0_type != 'ptr':
                base_offset = (opnd_1, opnd_0)
                r_size = (o1_size, o0_size)
                r_type = (value1_type, value0_type)
            else:
                base_offset = (opnd_0, opnd_1)
                r_size = (o0_size, o1_size)
                r_type = (value0_type, value1_type)
        else:
            base_offset = (opnd_0, opnd_1)
            r_size = (o0_size, o1_size)
            r_type = (value0_type, value1_type)

        return base_offset, r_size, r_type

    def _get_src_type_with_binop(self, opnds, live_defs):
        opnd_types = set()
        for opnd in opnds:
            opnd_type = live_defs[opnd].src_type if opnd in live_defs else 'I'
            opnd_type = opnd_type if opnd_type else 'N'
            opnd_types.add(opnd_type)

        if not opnd_types:
            return 'N'
        elif 'S' in opnd_types:
            return 'S'
        elif 'G' in opnd_types:
            return 'G'
        else:
            r_type = ''
            for opnd_type in opnd_types:
                r_type += opnd_type
            return r_type

    def _get_stack_def_offset(self, addr):
        """
        Get the stack def offset, e.g. STle(rsp + 0x40) = xxx.
        """
        stack_offset = addr[1][1] if type(addr) is tuple else 0 if 'r' in addr else 'N'
        return stack_offset

    def calculate_binop(self, op, args, args_size):
        """
        Only args all concret, we calculate its result.
        """
        s_args = []
        for opnd, opnd_size in zip(args, args_size):
            if type(opnd) is int:
                s_arg = BVV(opnd, opnd_size)
                s_args.append(s_arg)
            else:
                return None

        # print("psu-debug: op %s, s_args %s" % (op, s_args))
        result = translate(self.state, op, s_args)
        # print("psu-debug: get binop result %s" % (result))
        return result.args[0]

    def calculate_binop_v2(self, op, args, args_size, live_defs):
        """
        Only args all concret, we calculate its result.
        """
        s_args = []
        for opnd in args:
            if (opnd in live_defs and live_defs[opnd].action_type in ['w']
                    and type(live_defs[opnd].value) is int):
                s_args.append(live_defs[opnd].value)
            else:
                s_args.append(opnd)

        result = self.calculate_binop(op, s_args, args_size)
        return result

    def calculate_binop_v3(self, op, args, args_size, live_defs):
        """
        Only args all concret, we calculate its result.
        """

        def get_opnd_values(opnd, live_defs):
            if opnd not in live_defs:
                return [opnd]

            opnd_at = live_defs[opnd]
            opnd_values = []
            if type(opnd_at.value) is int:
                opnd_values.append(opnd_at.value)
                return opnd_values
            elif type(opnd_at.value) is list:
                for v in opnd_at.value:
                    opnd_values.append(v)
                return opnd_values
            return [opnd]

        results = []

        if len(args) != 2:
            result = self.calculate_binop_v2(op, args, args_size, live_defs)
            if result:
                results.append(result)
        else:
            s0_args = get_opnd_values(args[0], live_defs)
            s1_args = get_opnd_values(args[1], live_defs)

            for i in s0_args:
                for j in s1_args:
                    s_args = (i, j)
                    r = self.calculate_binop(op, s_args, args_size)
                    if r:
                        results.append(r)

        return results

    # def calculate_binop_stmt(self, op, args):
    #     """
    #     Calculate the binop stmtatement with angr.vex
    #     """
    #     s_args = []
    #     for opnd, opnd_size in args:
    #         s_arg = BVS(opnd, opnd_size) if type(opnd) is str else BVV(opnd, opnd_size)
    #         s_args.append(s_arg)
    #     # print("psu-debug: op %s, s_args %s" % (op, s_args))

    #     # self.state.scratch.tyenv = block.irsb.tyenv
    #     # tyenv = block.irsb.tyenv
    #     result = translate(self.state, op, s_args)
    #     # print("psu-debug: get binop result %s" % (result))
    #     return result

    # Kai code!
    def calculate_simple_binop(self, binop_opnds):
        datas = []
        op, opnds, opnds_size = binop_opnds[0], binop_opnds[1], binop_opnds[2]
        for opnd, size in zip(opnds, opnds_size):
            data = BVV(opnd, size) if type(opnd) is int else BVS(opnd, size)
            datas.append(data)

        if op == '+':
            result = datas[0] + datas[1]
        elif op == '-':
            result = datas[0] - datas[1]

        return result

    def calculate_complex_binop(self, binop_opnds):
        """
        Calculate the binop stmtatement with angr.vex
        """
        s_args = []
        op, opnds, opnds_size, _ = binop_opnds
        for opnd, opnd_size in zip(opnds, opnds_size):
            s_arg = BVS(opnd, opnd_size) if type(opnd) is str else BVV(opnd, opnd_size)
            s_args.append(s_arg)

        result = translate(self.state, op, s_args)
        return result

    def calculate_binop_stmt_v2(self, binop_opnds):
        """
        Calculate the binop stmtatement with angr.vex
        """
        if binop_opnds[0] in ['+', '-']:
            return self.calculate_simple_binop(binop_opnds)
        else:
            return self.calculate_complex_binop(binop_opnds)

    def read_rodata(self, addr, size, endness):
        """
        Read data from rodata.
        """
        value = None
        if addr == 0:
            return None

        # pe = get_mem_permission(addr)
        # if pe not in ['bss', 'stack']:
        flag = readable_address(addr)
        if flag:
            size_bytes = size // self.proj.arch.byte_width
            read_data = self.state.memory.load(addr, size_bytes, endness=endness)
            # print("data: %s" % (read_data))
            if read_data.op == 'BVV':
                value = read_data.args[0]
        return value

    def translate_loadg_expr(self, vex_expr):
        if vex_expr.tag is 'Iex_Const':
            return vex_expr.con.value

        elif vex_expr.tag is 'Iex_RdTmp':
            return 't%d' % (vex_expr.tmp)

        else:
            raise NoSupportVEXExpr

    def size_bytes(self, ty):
        if ty is None:
            raise Exception("The type cannot be None!")
        s = get_type_size(ty)
        if s % self.proj.arch.byte_width != 0:
            raise Exception("EngineVEX.size_bytes() called for a non-byte size!")
        return s // self.proj.arch.byte_width

    def _reset_var_value(self, block, var, var_value, live_defs):
        """
        The var's value is concrete (solve constraint), set the live_defs.
        """
        if 'r' in var:
            f_reg_alias = block.f_reg_alias
            # print("Var %s == 0" % (var))
            # print("F-reg-alias: %s" % (f_reg_alias))
            if var in f_reg_alias:
                for alias, i in f_reg_alias[var]:
                    alias_at = live_defs[alias]
                    new_at = alias_at.copy()
                    new_at.value = var_value
                    new_at.var_type = basic_types['default']
                    live_defs[alias] = new_at

        elif 't' in var:
            tmp_alias = block.tmp_alias
            # print("Var %s == 0" % (var))
            # print("Tmp-alias: %s" % (tmp_alias))
            if var in tmp_alias:
                for alias in tmp_alias[var]:
                    alias_at = live_defs[alias]
                    new_at = alias_at.copy()
                    new_at.value = var_value
                    new_at.var_type = basic_types['default']
                    live_defs[alias] = new_at

    def _solve_branch_guard(self, block, guard, live_defs):
        """
        Solve branch constraint.
        """
        var, var_value = None, None
        if guard.op == '__eq__':
            opnd1, opnd2 = guard.args
            # if opnd1.op == 'BVS' and opnd2.op == 'BVV' and opnd2.args[0] == 0:
            if opnd1.op == 'BVS' and opnd2.op == 'BVV':
                var = opnd1.args[0]
                var_value = opnd2.args[0]

        if var and var_value:
            # print("Find guard var: %s == %s" % (var, var_value))
            live_defs = live_defs.copy()
            self._reset_var_value(block, var, var_value, live_defs)
        return live_defs

    def transfer_live_definitions(self, block):
        """
        Transfer block's live_defs to successors blocks.
        """
        live_defs = block.live_defs
        for succ_block in block.successors:

            if succ_block.guard and block.addr in succ_block.guard:
                guard = succ_block.guard[block.addr]
                # print("Block %s -> %s has guard %s" % (block, succ_block, guard))
                new_defs = self._solve_branch_guard(block, guard, live_defs)
            else:
                new_defs = live_defs

            self._merge_live_definitions(succ_block, new_defs)

    def _merge_live_definitions(self, block, input_defs):
        """
        Merge the live definitions between block.live_defs and live_defs.
        """
        live_defs = block.live_defs
        if len(live_defs) == 0:
            for dst, action in input_defs.items():
                if type(dst) is str and 'r' not in dst:
                    continue
                live_defs[dst] = action

        else:
            for dst, action in input_defs.items():
                if type(dst) is str and 'r' not in dst:
                    continue

                if dst in live_defs:
                    old_action = live_defs[dst]
                    if old_action.code_location.block_addr != block.addr:
                        new_action = old_action.merge(action)
                        live_defs[dst] = new_action

                else:
                    live_defs[dst] = action

    def process_mips_swr_instruction(self, block, stmts, index, vex_ins_num):
        """
        In MIPS, the 'swr or swl' instruction is complex while parse irsb vex.
        Then simplify the 'swr' instruction.
           126 | ------ IMark(0x4140c4, 4, 0) ------
           127 | t173 = And32(t67,0x000000ff)
           128 | t172 = 32to8(t173)
           129 | t178 = Shr32(t67,0x08)
           130 | t177 = And32(t178,0x000000ff)
           131 | t176 = 32to8(t177)
           132 | t182 = Shr32(t67,0x10)
           133 | t181 = And32(t182,0x000000ff)
           134 | t180 = 32to8(t181)
           135 | t186 = Shr32(t67,0x18)
           136 | t185 = And32(t186,0x000000ff)
           137 | t184 = 32to8(t185)
           138 | t188 = Add32(t92,0x00000004)
           139 | t47 = And32(t188,0xfffffffc)
           140 | t48 = And32(t188,0x00000003)
           141 | t191 = CmpEQ32(t48,0x00000000)
           142 | t190 = ITE(t191,0x00000002,0x00000003)
           143 | t193 = CmpEQ32(t48,0x00000003)
           144 | t192 = ITE(t193,0x00000000,0x00000001)
           145 | t194 = Add32(t47,0x00000003)
           146 | STle(t194) = t184
           147 | t195 = Add32(t47,t190)
           148 | STle(t195) = t180
           149 | t196 = Add32(t188,t192)
           150 | STle(t196) = t176
           151 | STle(t188) = t172
        """
        st_stmt = None
        store_ins = 0
        last_st_index = None
        live_defs = block.live_defs
        ins_start = index - vex_ins_num
        # block.irsb.pp()

        for i in range(ins_start, index):
            stmt = stmts[i]
            # print(" --> %d %s" % (i, stmt))
            if isinstance(stmt, pyvex.stmt.Store):
                store_ins += 1
                last_st_index = i
                st_stmt = stmt

        if store_ins != 4:
            return

        # s_addr = 't%d' % (st_stmt.addr.tmp)
        # s_data = 't%d' % (st_stmt.data.tmp)
        # addr_at = live_defs[s_addr]
        # data_at = live_defs[s_data]
        # print("addr is:%s" % (addr_at))
        # print("store data is:%s" % (data_at))

        last_st_location = CodeLocation(block.addr, last_st_index)
        last_st_at = block.actions[last_st_location]
        # print("last-store(old): %s" % (last_st_at))
        st_data_alias = last_st_at.src_alias
        if type(st_data_alias) is tuple and 'And' in st_data_alias[0]:
            true_src = st_data_alias[1][0]
            last_st_at.src = true_src
            true_at = live_defs[true_src]
            if true_at.action_type in choose_action_types:
                last_st_at.src_alias = true_at.src_alias if true_at.src_alias else true_at.src
            else:
                last_st_at.src_alias = true_src
            last_st_at.var_size = arch_info['bits']
            last_st_at.var_type = None
        # print("last-store(new): %s" % (last_st_at))

    def process_mips_lwr_instruction(self, block, stmts, index, vex_ins_num):
        """
        In MIPS, the 'lwr or lwl' instruction is complex while parse irsb vex.
        Then simplify the 'lwr' instruction.
           19 | t33 = Add32(t21,0x00000012)
           20 | t9 = And32(t33,0xfffffffc)
           21 | t10 = And32(t33,0x00000003)
           22 | t37 = Shl32(t10,0x03)
           23 | t36 = 32to8(t37)
           24 | t38 = LDle:I32(t9)
           25 | t35 = Shr32(t38,t36)
           26 | t43 = Shl32(t10,0x03)
           27 | t42 = 32to8(t43)
           28 | t41 = Shr32(0xffffffff,t42)
           29 | t40 = Not32(t41)
           30 | t39 = And32(t32,t40)
           31 | t45 = Or32(t39,t35)
           32 | PUT(t9) = t45
        """
        ld_stmt, add_stmt, or_stmt = None, None, None
        live_defs = block.live_defs
        ins_start = index - vex_ins_num

        for i in range(ins_start, index):
            stmt = stmts[i]
            # print("lwr-ins %d %s" % (i, stmt))
            if isinstance(stmt, pyvex.stmt.WrTmp):
                if isinstance(stmt.data, pyvex.expr.Load):
                    if ld_stmt is None:
                        ld_stmt = stmt
                    else:
                        l.debug("Not a lwr instruction %s" % (block))
                        return
                elif isinstance(stmt.data, pyvex.expr.Binop):
                    binop = stmt.data.op
                    if 'Or' in binop:
                        if or_stmt is None:
                            or_stmt = stmt
                        else:
                            l.debug("Not a lwr instruction %s" % (block))
                            return

                    if 'Add' in binop:
                        if add_stmt is None:
                            add_stmt = stmt
                        else:
                            l.debug("Not a lwr instruction %s" % (block))
                            return

        if ld_stmt is None or add_stmt is None or or_stmt is None:
            return

        last_stmt = stmts[index-1]

        ld_dst = 't%d' % ld_stmt.tmp
        ld_at = live_defs[ld_dst]
        # print("lwr-load-action: %s" % (ld_at))
        add_dst = 't%d' % add_stmt.tmp
        add_at = live_defs[add_dst]
        # print("lwr-add-action: %s" % (add_at))
        lwr_dst = 't%d' % or_stmt.tmp
        lwr_at = live_defs[lwr_dst]
        # print("lwr-wrtmp-action: %s" % (lwr_at))

        ld_at.src = add_dst
        ld_at.src_alias = add_at.src_alias
        ld_at.dst = lwr_dst
        live_defs[lwr_dst] = ld_at

        lwr_at.action_type = 'wl'
        lwr_at.src = add_dst
        lwr_at.src_alias = add_at.src_alias
        lwr_at.var_type = None

        if isinstance(last_stmt, pyvex.stmt.Put) and isinstance(last_stmt.data, pyvex.expr.RdTmp):
            put_src = 't%d' % (last_stmt.data.tmp)
            if put_src == lwr_dst:
                put_dst = 'r%d' % last_stmt.offset
                put_at = live_defs[put_dst]
                put_at.src_alias = None
                put_at.var_type = None
                # print("lwr-put-action: %s" % (put_at))

    def process_mips_movz_instruction(self, block, stmts, index):
        """
        In MIPS-64, the 'movz' instruction is complex while parse irsb vex.
        Then simplify the 'movz' instruction.
            25 | t31 = And64(t13,t26)
            26 | t33 = And64(t7,t22)
            27 | t30 = Add64(t33,t31)
            28 | PUT(s0) = t30
        """
        # print("Process-mips-movz in %s" % (block))
        stmt1 = stmts[index-4]
        stmt2 = stmts[index-3]
        stmt3 = stmts[index-2]
        stmt4 = stmts[index-1]
        # ins1.pp()
        # ins2.pp()
        # ins3.pp()
        # ins4.pp()

        if (isinstance(stmt1, pyvex.stmt.WrTmp) and
                isinstance(stmt1.data, pyvex.expr.Binop) and
                isinstance(stmt2, pyvex.stmt.WrTmp) and
                isinstance(stmt2.data, pyvex.expr.Binop) and
                isinstance(stmt3, pyvex.stmt.WrTmp) and
                isinstance(stmt3.data, pyvex.expr.Binop) and
                isinstance(stmt4, pyvex.stmt.Put) and
                'And' in stmt1.data.op and
                'And' in stmt2.data.op and
                'Add' in stmt3.data.op):
            # print("Haha, found movz!")
            child0_expr = stmt2.data.child_expressions[0]
            if isinstance(child0_expr, pyvex.expr.RdTmp):
                wr_src = 't%d' % (child0_expr.tmp)
                wr_dst = 't%d' % (stmt3.tmp)
                block.live_defs[wr_dst] = block.live_defs[wr_src]
                # print("correct-xx : %s %s" % (wr_dst, block.live_defs[wr_src]))

            elif isinstance(child0_expr, pyvex.expr.Const):
                wr_src = child0_expr.con.value
                wr_dst = 't%d' % (stmt3.tmp)
                wr_old_at = block.live_defs[wr_dst]
                wr_old_at.src = wr_src
                wr_old_at.src_alias = None
                wr_old_at.action_type = 'w'

            put_dst = 'r%d' % stmt4.offset
            # print("movz %s %s" % (put_dst, wr_src))
            code_location = CodeLocation(block.addr, index-1)
            old_at = block.actions.get(code_location)
            if old_at is None:
                return
            # print("old-action: %s" % (old_at))
            if type(wr_src) is str:
                src_at = block.live_defs[wr_src]
                old_at.src = wr_src
                if src_at.action_type in choose_action_types:
                    old_at.src_alias = src_at.src_alias if src_at.src_alias else src_at.src
                else:
                    old_at.src_alias = src_at.dst
            else:
                old_at.src = wr_src
            # print("old-action (new): %s" % (old_at))

    def execute_block_irsb_v4(self, function, block, function_reg_defs, function_stack_defs, arguments):
        irsb = block.irsb
        if irsb is None:
            return

        # irsb.pp()

        block_addr = block.addr
        # loop_flag = block.is_loop

        block_actions = block.actions
        block_code_locations = block.code_locations
        live_defs = block.live_defs
        live_uses = block.live_uses
        reg_defs = block.reg_defs

        tyenv = irsb.tyenv
        stmts = irsb.statements

        count = 0
        last_ins = False
        call_flag = False
        if block.node_type in ['Call', 'Extern']:
            call_flag = True
            instructions = irsb.instructions

        special_ins_flag, mips_lwr_flag = 0, 0
        vex_ins_start = 0
        ins_addr = None
        for index, stmt in enumerate(stmts):
            if stmt.tag is 'Ist_IMark':
                ins_addr = stmt.addr
                vex_ins_num = index - vex_ins_start
                # print("xxx-vex-num: %d %d" % (vex_ins_num, special_ins_flag))
                if self.arch_bits == 64 and vex_ins_num == 11 and special_ins_flag == 4:
                    self.process_mips_movz_instruction(block, stmts, index)

                elif 'MIPS' in self.proj.arch.name:
                    if 8 <= mips_lwr_flag <= 11:
                        # print("mips_lwr_flag: %x %d" % (ins_addr, mips_lwr_flag))
                        self.process_mips_lwr_instruction(block, stmts, index, vex_ins_num)
                    elif 13 <= mips_lwr_flag <= 15:
                        # print("mips_lwr_flag: %x %d" % (ins_addr, mips_lwr_flag))
                        self.process_mips_swr_instruction(block, stmts, index, vex_ins_num)

                special_ins_flag = 0
                mips_lwr_flag = 0
                vex_ins_start = index

            elif stmt.tag is 'Ist_Exit':
                # The block will exit.
                # print("Exit: %s-%x" % (stmt, block_addr))
                self._get_branch_conditoin(block, stmt, live_defs)

                if 'MIPS' not in self.proj.arch.name:
                    break

            code_location = CodeLocation(block_addr, index, ins_addr=ins_addr)
            # print("\nstmt in %s %s" % (code_location, stmt))

            # Ignore the Ijk_Call irsb's last store vex.
            if call_flag:
                if stmt.tag is 'Ist_IMark':
                    count += 1
                    if count == instructions:
                        last_ins = True

                if last_ins and isinstance(stmt, pyvex.stmt.Store):
                    continue

            # l.info("stmt in %s" % (code_location))
            action = self._pre_process_statement_v4(function, block, stmt, code_location, tyenv, reg_defs, live_defs, live_uses, function_reg_defs, function_stack_defs, arguments)

            if action:
                if action.action_type == 'wo':
                    binop = action.src[0]
                    # print("%s %s" % (code_location, binop))
                    if 'Cmp' in binop:
                        special_ins_flag += 1
                    elif 'And' in binop:
                        special_ins_flag += 1
                        mips_lwr_flag += 1
                    elif 'Or' in binop or 'Sh' in binop:
                        mips_lwr_flag += 1
                elif action.action_type in ['wl', 's']:
                    mips_lwr_flag += 1

                # print("action: %s %s" % (code_location, str(action)))
                block_actions[code_location] = action
                block_code_locations.append(code_location)
                # print("add location: %s" % (code_location))

        if block.node_type in ['Call', 'Extern']:
            reg_defs[self.ret_name] = (CodeLocation(block_addr,len(instructions)), 'ret')

        self._summary_register_def_info(block, live_defs, reg_defs)

        # print("\npsu-debug: block %s\n" % (block))
        # for v, d_info in live_defs.items():
        #     print("%s : %s" % (v, str(d_info)))

    def _pre_process_statement_v4(self, function, block, stmt, code_location, tyenv, reg_defs, live_defs, live_uses, function_reg_defs, function_stack_defs, arguments):
        """
        pre process a stmt, and get the stmt's info.
        """
        at = None

        # print("psu-debug: %s %s %s" % (code_location, stmt, stmt.tag))

        if isinstance(stmt, pyvex.stmt.Store):

            stmt_data = stmt.data
            st_size = stmt_data.result_size(tyenv)

            # STle(t2)
            if isinstance(stmt.addr, pyvex.expr.RdTmp):
                s_addr = 't%d' % (stmt.addr.tmp)

            # STle(0xabcdef)
            elif isinstance(stmt.addr, pyvex.expr.Const):
                s_addr = stmt.addr.con.value

            else:
                l.debug("Not support the stmt: %s" % (stmt))
                return None

            # STle(t2) = t3 or STle(0x46ed58) = t3
            if isinstance(stmt_data, pyvex.expr.RdTmp):
                s_data = 't%d' % (stmt_data.tmp)

            # STle(t2) = 0x45 or STle(0x46ed58) = 0x7543bd
            elif isinstance(stmt_data, pyvex.expr.Const):
                s_data = stmt_data.con.value

            else:
                l.debug("Not support the stmt: %s" % (stmt))
                return None

            at = Action('s', code_location, s_addr, s_data, st_size)
            if type(s_addr) is str:
                addr_at = live_defs[s_addr]
                addr_at.var_type = 'ptr'
                if addr_at.action_type in choose_action_types:
                    at.dst_alias = addr_at.src_alias if addr_at.src_alias else addr_at.src
                else:
                    at.dst_alias = addr_at.dst
                at.dst_locs = addr_at.code_location.stmt_idx
                at.addr_value = addr_at.value
                at.addr_type = addr_at.src_type
                at.dst = addr_at.dst

            else:
                at.addr_value = s_addr
                at.addr_type = 'G'

            if type(s_data) is str:
                data_at = live_defs[s_data]
                if data_at.action_type in choose_action_types:
                    at.src_alias = data_at.src_alias if data_at.src_alias else data_at.src
                else:
                    at.src_alias = data_at.dst
                at.src_locs = data_at.code_location.stmt_idx
                at.src = data_at.dst
                at.value = data_at.value
                at.src_type = data_at.src_type
                at.src = data_at.dst
                if data_at.var_type:
                    at.var_type = data_at.var_type

                if at.addr_type == 'S':
                    if at.src_type == 'A':
                        at.argument = data_at.argument
                        if type(at.addr_value) is int:
                            live_defs[at.addr_value] = data_at

                    # elif type(data_at.value) is int and data_at.src_type != 'S' and data_at.value > 0 and type(at.addr_value) is int:
                    elif type(data_at.value) is int and data_at.value > 0 and type(at.addr_value) is int:
                        live_defs[at.addr_value] = data_at

            else:
                at.value = s_data
                at.src_type = at.get_concrete_src_type(s_data)
                if at.addr_type == 'S' and s_data > 0 and type(at.addr_value) is int:
                    live_defs[at.addr_value] = at

            if st_size == 8:
                at.var_type = basic_types[8]
            elif st_size == 16:
                at.var_type = basic_types[16]

            # print("\n+++++++++++++++\n%s\n" % (at))

        elif isinstance(stmt, pyvex.stmt.WrTmp):

            dst = 't%d' % (stmt.tmp)
            stmt_data = stmt.data
            wr_size = stmt_data.result_size(tyenv)
            # print("WrTmp-stmt: %s %s" % (stmt, stmt_data))

            # t4 = LDle(t5) or t4 = LDle(0x46ed58)
            if isinstance(stmt_data, pyvex.expr.Load):
                wr_type = 'wl'
                read_data = None
                load_addr = stmt_data.addr

                if isinstance(load_addr, pyvex.expr.RdTmp):
                    l_addr = 't%d' % (load_addr.tmp)
                    addr_at = live_defs[l_addr]
                    l_addr = addr_at.dst
                    at = Action('wl', code_location, dst, l_addr, wr_size)
                    addr_at.var_type = 'ptr'
                    addr_alias = addr_at.src_alias if addr_at.src_alias else addr_at.src
                    if addr_at.action_type in choose_action_types:
                        if type(addr_alias) is tuple:
                            at.src_alias = set_opnds_type(addr_alias, 'ptr')
                        else:
                            at.src_alias = addr_alias
                    else:
                        at.src_alias = addr_at.dst
                    at.src_locs = addr_at.code_location.stmt_idx
                    at.addr_type = addr_at.src_type
                    at.addr_value = addr_at.value

                    if wr_size == 8:
                        at.var_type = basic_types[8]
                    elif wr_size == 16:
                        at.var_type = basic_types[16]

                    if type(at.addr_value) is int:
                        if get_value_label(at.addr_value) == 'G':
                            block.global_addrs.add(at.addr_value)
                            function.global_addrs.add(at.addr_value)
                            # print(" -->Gaddr: %s 0x%x" % (code_location, at.addr_value))
                        read_data = self.read_rodata(at.addr_value, wr_size, stmt_data.end)
                        # print("Read-data: %x %s" % (at.addr_value, read_data))
                        if read_data:
                            at.value = read_data
                            at.src_type = at.get_concrete_src_type(read_data)
                            if at.src_type == 'G':
                                block.global_addrs.add(at.value)
                                function.global_addrs.add(at.value)
                                # print(" -->Gaddr: %s 0x%x" % (code_location, at.value))

                        elif at.addr_type == 'S':
                            arg_sym = self.judge_stack_argument(at.addr_value)
                            if arg_sym:
                                if arg_sym not in arguments:
                                    arguments.append(arg_sym)
                                    # print("Add stack-arg %s %s" % (code_location, arg_sym))
                                at.src_alias = arg_sym
                                at.src_type = 'A'
                                at.argument = arg_sym

                            if at.addr_value in live_defs:
                                ld_at = live_defs[at.addr_value]
                                at.argument = ld_at.argument
                                if type(ld_at.value) is int and ld_at.value in function.concrete_inc_addrs:
                                    pass
                                else:
                                    at.value = ld_at.value
                                    at.src_type = at.get_concrete_src_type(at.value) if ld_at.src_type is None else ld_at.src_type

                    # elif type(at.addr_value) is list:
                    #     values = []
                    #     for addr_v in at.addr_value:
                    #         read_data = self.read_rodata(addr_v, wr_size, stmt_data.end)
                    #         if read_data:
                    #             values.append(read_data)
                    #     if values:
                    #         at.src_type = at.get_concrete_src_type(values[0])
                    #         if len(values) == 1:
                    #             at.value = values[0]
                    #         else:
                    #             at.value = values

                elif isinstance(load_addr, pyvex.expr.Const):
                    l_addr = load_addr.con.value
                    at = Action('wl', code_location, dst, l_addr, wr_size)
                    at.addr_type = 'G'
                    at.addr_value = l_addr
                    if get_value_label(l_addr) == 'G':
                        block.global_addrs.add(l_addr)
                        function.global_addrs.add(l_addr)
                        # print(" -->Gaddr: %s 0x%x" % (code_location, l_addr))
                    read_data = self.read_rodata(l_addr, wr_size, stmt_data.end)
                    if read_data:
                        at.value = read_data
                        at.var_type = get_concrete_type(read_data, wr_size)
                        at.src_type = at.get_concrete_src_type(read_data)
                        if at.src_type == 'G':
                            block.global_addrs.add(at.value)
                            function.global_addrs.add(at.value)
                            # print(" -->Gaddr: %s 0x%x" % (code_location, at.value))

                else:
                    l.debug("Not support the stmt: %s" % (stmt))
                    return None

                live_defs[dst] = at
                # print("\n+++++++++++++++\n%s\n" % (at))

            # t4 = Add(t3, 0x20), t4 = Add(t3, t2)
            elif isinstance(stmt_data, pyvex.expr.Binop):
                wr_type = 'wo'
                binop = stmt_data.op
                opnds = []
                alias_info = {}
                opnds_size = []
                opnds_type = []
                src_locs = []

                # if 'Cmp' in binop:
                #     guard_flag = True

                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)
                        opnds_type.append(live_defs[opnd].var_type)
                        opnd_at = live_defs[opnd]
                        if opnd_at.action_type in ['w', 'p', 'wu', 'wn']:
                            # o_alias = opnd_at.src_alias if type(opnd_at.src_alias) is str else opnd_at.src
                            if type(opnd_at.src_alias) is str:
                                o_alias = opnd_at.src_alias
                            elif isinstance(opnd_at.src, (int, str)):
                                o_alias = opnd_at.src
                            else:
                                o_alias = opnd_at.dst

                            if o_alias == self.t9_name and type(opnd_at.value) is int:
                                o_alias = opnd_at.value
                            alias_info[opnd] = o_alias

                        else:
                            alias_info[opnd] = opnd_at.dst
                        src_locs.append(opnd_at.code_location.stmt_idx)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value
                        opnd = get_immediate_value(opnd)
                        if get_mem_permission(opnd) != 'imm':
                            opnds_type.append('ptr')
                        else:
                            opnds_type.append('int')
                        src_locs.append(0)

                    else:
                        raise Exception("Not support the stmt: %s" % (stmt))
                        return None

                    opnd_size = child_expr.result_size(tyenv)
                    opnd_size = opnd_size if opnd_size else self.arch_bits
                    opnds.append(opnd)
                    opnds_size.append(opnd_size)

                op = '+' if 'Add' in binop else '-' if 'Sub' in binop else binop
                src = (op, tuple(opnds), tuple(opnds_size), tuple(opnds_type))
                default_type = basic_types[wr_size]
                var_type = calculate_variable_type(op, opnds_type, default_type=default_type)
                at = Action(wr_type, code_location, dst, src, wr_size)
                at.var_type = var_type
                at.src_locs = src_locs

                try:
                    results = self.calculate_binop_v3(binop, opnds, opnds_size, live_defs)
                except:
                    results = []

                opnd_aliases = []
                if len(alias_info):
                    for opnd in opnds:
                        if opnd in alias_info:
                            opnd_aliases.append(alias_info[opnd])
                        else:
                            opnd_aliases.append(opnd)
                else:
                    opnd_aliases = opnds

                if op == '+' and len(opnd_aliases) == 2:
                    base_offset, r_size, r_type = self._judge_base_offset_v2(opnd_aliases, opnds_size, opnds_type)
                    at.src_alias = (op, base_offset, r_size, r_type)

                elif op == '-':
                    at.src_alias = (op, tuple(opnd_aliases), tuple(opnds_size), tuple(opnds_type))

                else:
                    at.src_alias = (binop, tuple(opnd_aliases), tuple(opnds_size), tuple(opnds_type))

                if len(results) == 1:
                    at.value = results[0]
                elif len(results) > 1:
                    at.value = results

                if type(at.value) is int:
                    at.src_type = at.get_concrete_src_type(at.value)
                    at.var_type = basic_types['default'] if get_mem_permission(at.value) == 'imm' else 'ptr'
                    if at.src_type == 'G':
                        block.global_addrs.add(at.value)
                        function.global_addrs.add(at.value)
                        # print(" -->Gaddr: %s 0x%x" % (code_location, at.value))

                live_defs[dst] = at

                # print("\n+++++++++++++++\n%s\n" % (at))

            # t4 = ITE(t1, t2, t3)
            elif isinstance(stmt_data, pyvex.expr.ITE):

                wr_type = 'wi'
                var_type = None

                opnds = []
                alias_opnds = []
                src_locs = []
                i = 0
                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)
                        opnd_at = live_defs[opnd]
                        if opnd_at.action_type in choose_action_types:
                            opnd_alias = opnd_at.src_alias if opnd_at.src_alias else opnd_at.src
                            alias_opnds.append(opnd_alias)
                        else:
                            alias_opnds.append(opnd)

                        if i > 0 and opnd_at.var_type:
                            var_type = opnd_at.var_type

                        src_locs.append(opnd_at.code_location.stmt_idx)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value
                        alias_opnds.append(opnd)
                        if opnd != 0:
                            var_type = self.get_concrete_type(opnd, wr_size)

                        src_locs.append(0)

                    else:
                        l.debug("Not support the stmt: %s" % (stmt))
                        return None

                    i = i + 1
                    opnds.append(opnd)

                src = tuple(opnds)
                at = Action('wi', code_location, dst, src, wr_size)
                at.src_alias = tuple(alias_opnds)
                at.src_locs = src_locs
                at.var_type = var_type

                # at.src_type = 'N' # TODO

                live_defs[dst] = at
                # print("\n+++++++++++++++\n%s\n" % (at))

            # t14 = 1Uto64(t15)
            elif isinstance(stmt_data, pyvex.expr.Unop):
                binop = stmt_data.op
                # print("Unop: %s" % (binop))

                opnds = []
                for child_expr in stmt_data.child_expressions:
                    if isinstance(child_expr, pyvex.expr.RdTmp):
                        opnd = 't%d' % (child_expr.tmp)

                    elif isinstance(child_expr, pyvex.expr.Const):
                        opnd = child_expr.con.value

                    else:
                        l.debug("Not support the stmt: %s" % (stmt))
                        return None

                    opnds.append(opnd)

                if len(opnds) != 1:
                    l.info("The Unop %s has two opnds" % (stmt))
                    raise Exception

                opnd_0 = opnds[0]
                if type(opnd_0) is str:
                    opnd_at = live_defs[opnd_0]
                    new_at = opnd_at.copy()
                    new_at.var_size = wr_size
                    new_at.var_type = basic_types[wr_size]
                    if 'Not' in binop:
                        new_at.action_type = 'wn'
                    live_defs[dst] = new_at

                    at = Action('wu', code_location, dst, new_at.dst, wr_size)
                    at.src_locs = new_at.code_location.stmt_idx
                    # print("\n+++++++++++++++\n%s\n" % (at))

                elif type(opnd_0) is int:
                    at = Action('wu', code_location, dst, opnd_0, wr_size)
                    at.value = opnd_0
                    at.src_type = 'I'
                    at.var_type = basic_types[wr_size]
                    live_defs[dst] = at

                    # print("\n+++++++++++++++\n%s\n" % (at))

            # t4 = Get(rdi) or t4 = t6
            else:
                wr_type = 'w'

                if isinstance(stmt_data, pyvex.expr.RdTmp):
                    src = 't%d' % (stmt_data.tmp)
                    live_defs[dst] = live_defs[src]

                elif isinstance(stmt_data, pyvex.expr.Get):
                    src = 'r%d' % (stmt_data.offset)
                    at = Action(wr_type, code_location, dst, src, wr_size)

                    if src in live_defs:
                        src_at = live_defs[src]
                        at.value = src_at.value
                        at.src_type = src_at.src_type
                        at.var_type = src_at.var_type
                        if src_at.code_location.block_addr == code_location.block_addr:
                            if src_at.action_type in choose_action_types:
                                at.src_alias = src_at.src_alias if src_at.src_alias else src_at.src
                            live_defs[dst] = src_at
                        else:
                            live_defs[dst] = at
                            at.src_locs = 0
                        at.argument = src_at.argument

                    elif src in self.argument_vars:
                        at.src_type = 'A'
                        at.src_locs = 0

                        loc = CodeLocation(block.addr, 0)
                        src_at = Action('p', loc, src, src, wr_size)
                        src_at.src_type = 'A'
                        src_at.src_locs = 0
                        src_at.argument = src
                        live_defs[src] = src_at

                        live_defs[dst] = at
                        if src not in arguments:
                            arguments.append(src)
                            # print("Add-argument: %s %s" % (block, src))

                        at.argument = src

                    else:
                        at.src_type = 'N'
                        live_defs[dst] = at

                        loc = CodeLocation(block.addr, 0)
                        src_at = Action('p', loc, src, src, wr_size)
                        live_defs[src] = src_at

                    # print("\n+++++++++++++++\n%s\n" % (at))

                elif isinstance(stmt_data, pyvex.expr.Const):
                    src = stmt_data.con.value
                    at = Action('p', code_location, dst, src, wr_size)
                    at.value = src
                    at.var_type = self.get_concrete_type(src, wr_size)
                    at.src_type = at.get_concrete_src_type(src)
                    if at.src_type == 'G':
                        block.global_addrs.add(at.value)
                        function.global_addrs.add(at.value)
                        # print(" -->Gaddr: %s 0x%x" % (code_location, at.value))

                    live_defs[dst] = at

                else:
                    l.debug("Not support the stmt: %s %s\n" % (code_location, stmt))
                    at = Action('none', code_location, dst, None, wr_size)
                    live_defs[dst] = at

        elif isinstance(stmt, pyvex.stmt.Put):

            if choose_register and stmt.offset in self.ignore_regs:
                return None

            dst = 'r%d' % (stmt.offset)
            stmt_data = stmt.data
            put_size = stmt_data.result_size(tyenv)

            if isinstance(stmt_data, pyvex.expr.RdTmp):
                src = 't%d' % (stmt_data.tmp)
                at = Action('p', code_location, dst, src, put_size)

                # if src not in live_defs:
                #     at = Action('none', code_location, dst, src, put_size)
                #     live_defs[dst] = at
                #     l.error("Not found put tmp: %s %s\n" % (code_location, stmt))
                #     return

                src_at = live_defs[src]
                if src_at.action_type in choose_action_types:
                    at.src_alias = src_at.src_alias if src_at.src_alias else src_at.src
                else:
                    at.src_alias = src_at.dst
                    src = src_at.dst

                at.src = src_at.dst
                at.src_locs = src_at.code_location.stmt_idx
                at.value = src_at.value
                at.src_type = src_at.src_type
                at.var_type = src_at.var_type
                at.argument = src_at.argument

                live_defs[dst] = at

                # print("\n+++++++++++++++\n%s\n" % (at))

                reg_defs[dst] = (code_location, src)

            elif isinstance(stmt_data, pyvex.expr.Const):
                src = stmt_data.con.value
                at = Action('p', code_location, dst, src, put_size)
                at.value = src
                at.var_type = get_concrete_type(src, put_size)
                at.src_type = at.get_concrete_src_type(src)

                live_defs[dst] = at
                reg_defs[dst] = (code_location, src)

                # print("\n+++++++++++++++\n%s\n" % (at))

            else:
                l.debug("Not support the stmt: %s" % (stmt))
                return None

        # t35 = if (t80) ILGop_Ident32(LDle(t45)) else t27
        elif stmt.tag is 'Ist_LoadG':
            dst = 't%d' % (stmt.dst)
            l_addr = self.translate_loadg_expr(stmt.addr)
            alt = self.translate_loadg_expr(stmt.alt)
            guard = self.translate_loadg_expr(stmt.guard)
            read_type, converted_type = stmt.cvt_types
            read_size, converted_size = get_type_size(read_type), get_type_size(converted_type)
            alt_size = stmt.alt.result_size(tyenv)

            src_locs = []
            at = Action('lg', code_location, dst, None, converted_size)
            at.src_locs = src_locs

            src_aliases = []
            guard_at = live_defs[guard]
            guard_alias = guard_at.src_alias if guard_at.src_alias else guard_at.src
            src_aliases.append(guard_alias)
            src_locs.append(guard_at.code_location.stmt_idx)

            if type(l_addr) is str:
                addr_at = live_defs[l_addr]
                l_addr = addr_at.dst
                if addr_at.action_type in choose_action_types:
                    src_alias = addr_at.src_alias if addr_at.src_alias else addr_at.src
                    src_aliases.append(src_alias)
                else:
                    src_aliases.append(addr_at.dst)
                src_locs.append(addr_at.code_location.stmt_idx)
                at.addr_value = addr_at.value
                at.addr_type = addr_at.src_type
                self._execute_action_load_value(at, read_size, stmt.end)

            elif type(l_addr) is int:
                src_aliases.append(l_addr)
                src_locs.append(0)
                at.addr_value = l_addr
                at.addr_type = 'G'
                if get_value_label(l_addr) == 'G':
                    block.global_addrs.add(l_addr)
                    function.global_addrs.add(l_addr)
                    # print(" -->Gaddr: %s 0x%x" % (code_location, l_addr))
                read_data = self.read_rodata(l_addr, read_size, stmt.end)
                if read_data:
                    at.value = read_data
                    if get_value_label(read_data) == 'G':
                        block.global_addrs.add(at.value)
                        function.global_addrs.add(at.value)
                        # print(" -->Gaddr: %s 0x%x" % (code_location, at.value))
                else:
                    at.src_type = '*G'

            if type(alt) is str:
                alt_at = live_defs[alt]
                alt = alt_at.dst
                if alt_at.action_type in choose_action_types:
                    alt_alias = alt_at.src_alias if alt_at.src_alias else alt_at.src
                    src_aliases.append(alt_alias)
                else:
                    src_aliases.append(alt_at.dst)
                src_locs.append(alt_at.code_location.stmt_idx)
                # alt_value = alt_at.value

            elif type(alt) is int:
                src_aliases.append(alt)
                src_locs.append(0)
                # alt_value = alt

            # if type(alt_value) is int:
            #     if type(at.value) is int:
            #         at.value = [at.value, alt_value]
            #     elif type(at.value) is list:
            #         at.value.append(alt_value)
            #     else:
            #         at.value = alt_value

            # elif type(alt_value) is list:
            #     if type(at.value) is int:
            #         at.value = [at.value]
            #         at.value.extend(alt_value)
            #     elif type(at.value) is list:
            #         at.value.extend(alt_value)
            #     else:
            #         at.value = alt_value

            at.src = ((guard, l_addr, alt), (1, read_size, alt_size))
            at.src_alias = (tuple(src_aliases), (1, read_size, alt_size))

            live_defs[dst] = at
            # print("\n+++++++++++++++\n%s\n" % (at))

        # if (t82) STle(t68) = t35
        elif stmt.tag is 'Ist_StoreG':
            guard = self.translate_loadg_expr(stmt.guard)

            stmt_data = stmt.data
            st_size = stmt_data.result_size(tyenv)

            # STleg(t2)
            if isinstance(stmt.addr, pyvex.expr.RdTmp):
                s_addr = 't%d' % (stmt.addr.tmp)

            # STle(0xabcdef)
            elif isinstance(stmt.addr, pyvex.expr.Const):
                s_addr = stmt.addr.con.value

            else:
                l.debug("Not support the stmt: %s" % (stmt))
                return None

            # STle(t2) = t3 or STle(0x46ed58) = t3
            if isinstance(stmt_data, pyvex.expr.RdTmp):
                s_data = 't%d' % (stmt_data.tmp)

            # STle(t2) = 0x45 or STle(0x46ed58) = 0x7543bd
            elif isinstance(stmt_data, pyvex.expr.Const):
                s_data = stmt_data.con.value

            else:
                l.debug("Not support the stmt: %s" % (stmt))
                return None

            at = Action('sg', code_location, s_addr, (guard, s_data), st_size)
            if type(s_addr) is str:
                addr_at = live_defs[s_addr]
                addr_at.var_type = 'ptr'
                if addr_at.action_type in choose_action_types:
                    at.dst_alias = addr_at.src_alias if addr_at.src_alias else addr_at.src
                else:
                    at.dst_alias = addr_at.dst
                at.dst_locs = addr_at.code_location.stmt_idx
                at.addr_value = addr_at.value
                at.addr_type = addr_at.src_type
                at.dst = addr_at.dst

            else:
                at.addr_value = s_addr
                at.addr_type = 'G'

            at.src_locs = []
            guard_at = live_defs[guard]
            guard_alias = guard_at.src_alias if guard_at.src_alias else guard_at.src
            at.src_locs.append(guard_at.code_location.stmt_idx)

            s_data_alias = s_data
            if type(s_data) is str:
                data_at = live_defs[s_data]
                if data_at.action_type in choose_action_types:
                    s_data_alias = data_at.src_alias if data_at.src_alias else data_at.src
                else:
                    s_data_alias = data_at.dst
                at.src_locs.append(data_at.code_location.stmt_idx)
                at.value = data_at.value
                at.src_type = data_at.src_type
                at.src = data_at.dst
                if data_at.var_type:
                    at.var_type = data_at.var_type

            else:
                at.value = s_data
                # at.src_type = at.get_concrete_src_type(s_data)
                at.src_locs.append(0)

            at.src_alias = (guard_alias, s_data_alias)

            # print("\n+++++++++++++++\n%s\n" % (at))

        else:
            l.debug("Not support: %s %s %s" % (code_location, stmt, stmt.tag))
            if hasattr(stmt, 'tmp'):
                dst = 't%d' %(stmt.tmp)
                at = Action('none', code_location, dst, None, None)
                live_defs[dst] = at
            elif hasattr(stmt, 'result'):
                dst = 't%d' %(stmt.result)
                at = Action('none', code_location, dst, None, None)
                live_defs[dst] = at
            return None

        return at

    def _calculate_stack_pointer(self, opnds):
        opnd_0, opnd_1 = opnds[0][0], opnds[1][0]
        if type(opnd_0) is int and type(opnd_1) is int:
            return opnd_0 + opnd_1
        else:
            return None

    # Kai code!
    def _summary_register_def_info(self, block, live_defs, reg_defs):

        tmp_alias = block.tmp_alias
        b_reg_alias, f_reg_alias = block.b_reg_alias, block.f_reg_alias

        put_alias = {}
        put_info = {}
        put_concret_info = {}

        for d_var, (loc, t) in reg_defs.items():
            if type(t) is int:
                if get_mem_permission(t) != 'imm':
                    if t not in put_concret_info:
                        put_concret_info[t] = set()
                    put_concret_info[t].add(d_var)
                continue
            # if type(t) is int: continue

            u_at = live_defs[t]
            t_sc = u_at.code_location.stmt_idx
            if t_sc not in put_alias:
                put_alias[t_sc] = set()

            put_alias[t_sc].add(d_var)
            put_alias[t_sc].add(t)
            use_src = u_at.src
            if u_at.action_type == 'w' and type(use_src) is str and 'r' in use_src:
                if use_src not in f_reg_alias:
                    f_reg_alias[use_src] = set()
                f_reg_alias[use_src].add((d_var, loc.stmt_idx))

                if use_src not in reg_defs:
                    if d_var not in b_reg_alias:
                        b_reg_alias[d_var] = set()
                    b_reg_alias[d_var].add(use_src)

            put_info[d_var] = t_sc

        for t_sc, aliases in put_alias.items():
            for tmp in aliases:
                if 't' in tmp:
                    tmp_alias[tmp] = set([s for s in aliases if 'r' in s])

        for p_reg, t_sc in put_info.items():
            aliases = put_alias[t_sc]
            al = [s for s in aliases if 'r' in s and p_reg != s]
            if al:
                if p_reg not in b_reg_alias:
                    b_reg_alias[p_reg] = set(al)
                else:
                    for r in al:
                        b_reg_alias[p_reg].add(r)

        for use_reg, dst_info in f_reg_alias.items():
            for d_reg, i in dst_info:
                if use_reg in reg_defs:
                    if reg_defs[use_reg][0].stmt_idx < i:
                        if use_reg not in b_reg_alias:
                            b_reg_alias[use_reg] = set()
                        b_reg_alias[use_reg].add(d_reg)
                else:
                    if use_reg not in b_reg_alias:
                        b_reg_alias[use_reg] = set()
                    b_reg_alias[use_reg].add(d_reg)

        for value, put_regs in put_concret_info.items():
            if len(put_regs) < 2:
                continue
            for put_reg in put_regs:
                for reg_alias in put_regs:
                    if put_reg != reg_alias:
                        if put_reg not in b_reg_alias:
                            b_reg_alias[put_reg] = set()
                        b_reg_alias[put_reg].add(reg_alias)

        # print("%s has tmp_alias: %s\n b_reg_alias: %s\n f_reg_alias: %s\n" % (block, tmp_alias, b_reg_alias, f_reg_alias))

    def _execute_action_load_value(self, action, read_size, endness):
        """
        While action.addr_value is int, read memory data from addr_value.
        """
        if type(action.addr_value) is int:
            read_data = self.read_rodata(action.addr_value, read_size, endness)
            if read_data:
                action.value = read_data
                action.src_type = action.get_concrete_src_type(read_data)

        elif type(action.addr_value) is list:
            values = []
            for addr_v in action.addr_value:
                read_data = self.read_rodata(addr_v, read_size, endness)
                if read_data:
                    values.append(read_data)
            if values:
                action.src_type = action.get_concrete_src_type(values[0])
                if len(values) == 1:
                    action.value = values[0]
                else:
                    action.value = values

    def judge_stack_argument(self, stack_addr):
        """
        Judge the stack_addr is save the argument.
        """
        bs = self.proj.arch.bytes
        if stack_addr >= self.base_stack:
            # print("base_stack: %x, curr_stack: %x" % (self.base_stack, stack_addr))
            offset = stack_addr - self.base_stack
            if (offset % bs) == 0:
                return 's%d' % (offset // bs)

    def judge_constraints_satisfiable(self, constraints):
        """
        Judge the constraints is satisfiable
        """
        return self.solver.satisfiable(constraints)

    def get_concrete_type(self, value, size):
        """
        Get concret value's data type (char, int, long, ptr etc.)
        """
        if get_mem_permission(value) != 'imm':
            return 'ptr'
        else:
            return basic_types[size]

    def _calculate_type_with_add(self, op1_type, op2_type):
        pass

    def get_type_with_binop(self, opnds_info, live_defs):
        """
        Calculate the opnds_info's type result.
        """
        opnds_type = []
        op, opnds, opnds_size = opnds_info[0], opnds_info[1], opnds_info[2]
        for i, opnd in enumerate(opnds):
            if type(opnd) is str:
                opnds_type.append(live_defs[opnd].var_type)
            else:
                vtype = self.get_concrete_type(opnd, opnds_size[i])
                opnds_type.append(vtype)

        result_type = self.calculate_variable_type(op, opnds_type)
        return result_type

    def calculate_variable_type(self, op, opnds_type, default_type=None):
        """
        Calculate a variable's type by the binop (add, sub, mul, etc.)
        """
        if len(opnds_type) != 2:
            raise Exception("Should consider the opnds more than two!")

        opnd1_type, opnd2_type = opnds_type
        var_type = None
        if op == '+':
            if opnd1_type == 'ptr' or opnd2_type == 'ptr':
                var_type = 'ptr'

            elif opnd1_type and opnd2_type:
                var_type = opnd1_type
                # var_type = self._calculate_type_with_add(opnd1_type, opnd2_type)

        elif op == '-':
            if opnd1_type == 'ptr' and opnd2_type == 'ptr' or opnd2_type == 'ptr':
                var_type = basic_types[self.arch_bits]

            elif opnd1_type == 'ptr' and (opnd2_type and opnd2_type != 'ptr'):
                var_type = 'ptr'

            elif opnd1_type and opnd1_type != 'ptr':
                var_type = basic_types[self.arch_bits]

            elif opnd1_type and opnd2_type:
                var_type = opnd1_type
                # var_type = self._calculate_type_with_sub(opnd1_type, opnd2_type)

        else:
            var_type = default_type

        return var_type

    def infer_variable_type(self, live_defs, opnds_info, var_type):
        """
        Infer each variable's type in opnds according the variable type.
        """
        # print("Infer variable type: %s with %s" % (opnds_info, var_type))
        op, opnds, opnds_size, opnds_type = opnds_info[0], opnds_info[1], opnds_info[2], opnds_info[3]
        opnd1, opnd2 = opnds
        opnd1_type, opnd2_type = opnds_type

        if op == '+':
            if var_type == 'ptr':
                if type(opnd1) is str:
                    opnd1_at = live_defs[opnd1]
                    opnd1_type = opnd1_at.var_type
                else:
                    opnd1_type = self.get_concrete_type(opnd1, opnds_size[0])

                if type(opnd2) is str:
                    opnd2_at = live_defs[opnd2]
                    opnd2_type = opnd2_at.var_type
                else:
                    opnd2_type = self.get_concrete_type(opnd2, opnds_size[1])

                if opnd1_type is None and (opnd2_type and opnd2_type != 'ptr'):
                    opnd1_at.var_type = 'ptr'

                elif opnd2_type is None and (opnd1_type and opnd1_type != 'ptr'):
                    opnd2_at.var_type = 'ptr'

            else:
                if type(opnd1) is str:
                    opnd1_at = live_defs[opnd1]
                    if opnd1_at.var_type is None:
                        opnd1_at.var_type = basic_types[opnds_size[0]]
                if type(opnd2) is str:
                    opnd2_at = live_defs[opnd2]
                    if opnd2_at.var_type is None:
                        opnd2_at.var_type = basic_types[opnds_size[1]]

        elif op == '-':
            if var_type == 'ptr':
                pass

            else:
                if opnd1_type and opnd2_type is None:
                    if opnd1_type == 'ptr':
                        if type(opnd2) is str:
                            live_defs[opnd2].var_type = 'ptr'

                    else:
                        pass
                        # if type(opnd2) is str:
                        #     live_defs[opnd2].var_type = basic_types[opnds_size[1]]

                else:
                    pass # TODO

                if opnd1_type is None and opnd2_type:
                    if opnd2_type == 'ptr':
                        if type(opnd1) is str:
                            live_defs[opnd1].var_type = 'ptr'

                    else:
                        pass
                        # if type(opnd1) is str:
                        #     live_defs[opnd1].var_type = basic_types[opnds_size[0]]

                else:
                    pass # TODO

    def find_increment_addr_v2(self, block, addr_var):
        """
        Find increment store address in a single block.
        """
        flag = False
        live_defs = block.live_defs
        code_locations = block.code_locations
        ins_len = len(code_locations)
        trace_vars = {addr_var}

        for i in range(ins_len-1, -1, -1):
            code_location = code_locations[i]
            action = actions[code_location]
            action_type = action.action_type

            dst = action.dst
            if dst in trace_vars:
                trace_vars.remove(dst)
                if action_type == 'wo' and action.src_alias[0] == '+':
                    for opnd in action.src_alias[1]:
                        if type(opnd) is str:
                            trace_vars.add(opnd)
                elif action_type == 'wl':
                    pass

        return flag

    def find_increment_addr_no_loop(self, block, addr_var):
        if type(addr_var) is not str:
            return False

        # print("find-inc-addr: %s %s" % (block, addr_var))
        st_reg = None
        st_reg_index = 0
        if 't' in addr_var and addr_var in block.tmp_alias:
            for r in block.tmp_alias[addr_var]:
                st_reg = r
                st_reg_index = 10000
                break
        # block.irsb.pp()
        # flag = self.find_increment_addr_v2(self, block, addr_var)
        addr_alias = set()
        trace_vars = []
        addr_binops, addr_loads, addr_stores = [], [], []
        live_defs = block.live_defs
        addr_at = live_defs[addr_var]
        # print("addr_at: %s" % (addr_at))
        if addr_at.action_type == 'wo' and addr_at.src[0] == '+':
            opnds = addr_at.src_alias[1]
            trace_vars = [opnd for opnd in opnds if type(opnd) is str]
        elif addr_at.action_type == 'wl':
            trace_vars = [addr_var]
        elif addr_at.action_type == 'w' and type(addr_at.src) is str and 'r' in addr_at.src:
            st_reg = addr_at.src
            st_reg_index = addr_at.code_location.stmt_idx
        else:
            return False

        # print("trace-var: %s" % (trace_vars))
        for trace_var in trace_vars:
            at = live_defs[trace_var]
            if at.action_type == 'wl':
                addr_loads.append(at)

        code_locations = block.code_locations
        actions = block.actions
        for code_location in code_locations:
            action = actions[code_location]
            if action.action_type == 'wo' and action.src[0] == '+':
                op, opnds = action.src_alias[0], action.src_alias[1]
                for var in trace_vars:
                    if var in opnds:
                        addr_ptr = action.dst
                        addr_alias.add(addr_ptr)
                        addr_binops.append(action)

            elif action.action_type == 's':
                if action.src in addr_alias:
                    addr_stores.append(action)

        # print("addr-info: \n addr_binops: %s\n addr_loads: %s\n addr_stores: %s" % (addr_binops, addr_loads, addr_stores))
        if len(addr_loads) and len(addr_stores):
            for l_action in addr_loads:
                for s_action in addr_stores:
                    l_addr = l_action.src_alias if l_action.src_alias else l_action.src
                    s_addr = s_action.dst_alias if s_action.dst_alias else s_action.dst
                    if type(l_addr) is tuple and type(s_addr) is tuple:
                        if l_addr[1] == s_addr[1]:
                            return True
                        elif l_addr[1][1] == s_addr[1][1] and type(l_addr[1][0]) is str and type(s_addr[1][0]) is str:
                            l_at = live_defs[l_addr[1][0]]
                            s_at = live_defs[s_addr[1][0]]
                            if hash(l_at.src_alias) == hash(s_at.src_alias):
                                # print(l_at.src_alias, s_at.src_alias)
                                return True

                    elif type(l_addr) is str and type(s_addr) is str and l_addr == s_addr:
                        return True

        if st_reg:
            return self.find_increment_addr_loop_v2(block, st_reg, index=st_reg_index)
        return False

    def find_increment_addr_loop_v2(self, block, addr_reg, index=0):
        """
        In sotre(addr) = char, the addr is a reg.
        We find whether the reg has a increment with 1 (e.g. r4 = r4 + 1).
        """
        work_list = [block]
        count = 0
        while work_list:
            bb = work_list.pop()
            count += 1
            code_locations = bb.code_locations
            actions = bb.actions
            for code_location in code_locations:
                if code_location.stmt_idx < index:
                    continue
                action = actions[code_location]
                if action.action_type == 'wo' and action.src[0] == '+' and type(action.src_alias) is tuple:
                    opnd0, opnd1 = action.src_alias[1]
                    if opnd0 == addr_reg and opnd1 == 1:
                        return True
                elif action.action_type == 'p' and action.dst == addr_reg:
                    return False
            for succ_bb in bb.successors:
                work_list.append(succ_bb)
            if count > 9:
                return False
            index = 0
        return False

    def _generate_ast_by_tmp_v2(self, block, tmp, tmp_asts, inc_actions):
        """
        Generate the tmp's alias expr by the live_defs.
        """
        # print("Generate-ast-by-tmp: %s %s" % (tmp, tmp_asts))
        live_defs = block.live_defs

        use_at = live_defs[tmp]
        action_type = use_at.action_type
        data_size = use_at.var_size

        asts = []
        if action_type == 'wo':
            binop_opnds = use_at.src_alias
            if use_at.inc_flag:
                inc_actions.append(use_at)

            elif binop_opnds[0] in ['+', '-']:
                if use_at.src_type == 'S' and type(use_at.value) is int:
                    ast = BVV(use_at.value)
                else:
                    ast = self.calculate_simple_binop(binop_opnds)
                asts.append(ast)
                tmp_asts[tmp] = ast

        elif action_type == 'w':
            use_data = use_at.src_alias if type(use_at.src_alias) is str else use_at.src
            ast = BVV(use_data, data_size) if type(use_data) is int else BVS(use_data, data_size)
            asts.append(ast)
            tmp_asts[tmp] = ast

        new_tmps = set()
        for tmp in map(lambda ast: [sym for sym in ast.variables if 't' in sym], asts):
            new_tmps |= set(tmp)

        for t in new_tmps:
            self._generate_ast_by_tmp_v2(block, t, tmp_asts, inc_actions)

    def _construct_ast_by_tmp_info(self, tmp, tmp_info):

        if tmp not in tmp_info:
            return None

        new_ast = tmp_info[tmp]

        while True:
            tmps = {}
            # print("construct-ast: %s" % (new_ast))
            for leaf_ast in new_ast.recursive_leaf_asts:
                if leaf_ast.op == 'BVS' and 't' in leaf_ast.args[0]:
                    tmp = leaf_ast.args[0]
                    tmps[tmp] = leaf_ast

            if len(tmps) == 0:
                return new_ast

            rep_datas = [(tmp_ast, tmp_info[tmp]) for tmp, tmp_ast in tmps.items() if tmp in tmp_info]
            if len(rep_datas) == 0:
                return new_ast

            new_ast = new_ast.replace(rep_datas[0][0], rep_datas[0][1])

    def _get_inc_actions(self, block, inc_actions):

        for loc, action in block.actions.items():
            if action.inc_flag:
                inc_actions.append(action)

    def find_increment_addr_loop(self, block, addr_var):
        """
        Find increment addr in loop.
        """
        # print("Find_inc_loop: %s %s" % (block, addr_var))
        tmp_asts, inc_actions = {}, []
        self._generate_ast_by_tmp_v2(block, addr_var, tmp_asts, inc_actions)
        addr_ast = self._construct_ast_by_tmp_info(addr_var, tmp_asts)
        # print("tmp-asts: %s, addr-ast: %s" % (tmp_asts, addr_ast))
        if addr_ast is None:
            addr_ast = BVS(addr_var)

        self._get_inc_actions(block, inc_actions)
        # print("inc-actions: %s" % (inc_actions))

        for action in inc_actions:
            dst = action.dst
            inc_base = action.inc_base
            # print(inc_base)
            if inc_base and inc_base[1] in addr_ast.variables:
                return inc_base[1], addr_ast

            elif dst in addr_ast.variables:
                return dst, addr_ast
        return None, None

    def find_equal_zero_guard(self, guard):
        """
        In branch, if rxx == 0, then get the rxx and set value with zero.
        """
        if guard.op == '__eq__':
            opnd1, opnd2 = guard.args
            if opnd1.op == 'BVS' and opnd2.op == 'BVV' and opnd2.args[0] == 0:
                return opnd1.args[0]

    def get_stack_sym_value(self, block, sym):

        live_defs = block.live_defs
        index = int(sym[1:], 10)
        sp_at = live_defs[self.sp_name]
        stack_ip = sp_at.value + index * self.arch_bytes

        if stack_ip in live_defs:
            stack_at = live_defs[stack_ip]
            # print("stack-at: %s" % (stack_at))

    def set_concret_contexts(self, callsite, function):
        """
        In forward trace, the callsite may set some arguments with concrete value.
        """
        # print("set-concret-context: %s -> %s" % (callsite, function))
        function.concret_contexts.clear()
        pre_block = list(callsite.predecessors)[0]
        live_defs = pre_block.live_defs
        for arg in function.arguments:
            # print("argument: %s" % (arg))
            if 'r' in arg and arg in live_defs:
                reg_at = live_defs[arg]
                # if type(reg_at.value) is int and reg_at.src_type == 'I':
                if type(reg_at.value) is int:
                    function.concret_contexts[arg] = reg_at.value
                    # print("Set- %s : %x" % (arg, reg_at.value))

            # elif 's' in arg:
            #     self.get_stack_sym_value(pre_block, arg)

    def get_claripy_operation(self, vex_binop):
        if 'LE' in vex_binop:
            return 'le'
        elif 'LT' in vex_binop:
            return 'lt'
        elif 'GE' in vex_binop:
            return 'ge'
        elif 'GT' in vex_binop:
            return 'gt'
        elif 'EQ' in vex_binop:
            return 'eq'
        elif 'NE' in vex_binop:
            return 'ne'
        else:
            return ''

    def reverse_cmp_binop(self, cmp_op):
        if cmp_op == 'le':
            return 'ge'
        elif cmp_op == 'lt':
            return 'gt'
        elif cmp_op == 'ge':
            return 'le'
        elif cmp_op == 'gt':
            return 'lt'
        elif cmp_op == 'eq':
            return 'eq'
        elif cmp_op == 'ne':
            return 'ne'
        else:
            return ''

    def get_var_guard_info(self, var, guard):
        info = None
        if (len(guard.args) == 2):
            cmpop = guard.op
            if '_' in cmpop:
                cmp_op = cmpop[2:4]
            else:
                cmp_op = self.get_claripy_operation(cmpop)

            if not cmp_op:
                return info

            opnd0, opnd1 = guard.args
            if (opnd0.op == 'BVS' and var == opnd0.args[0]):
                if opnd1.op in ['BVS', 'BVV']:
                    info = (cmp_op, var, opnd1.args[0])

            elif (opnd1.op == 'BVS' and var == opnd1.args[0]):
                if opnd0.op in ['BVS', 'BVV']:
                    cmp_op = self.reverse_cmp_binop(cmp_op)
                    info = (cmp_op, var, opnd0.args[0])
        return info
