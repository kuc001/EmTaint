#!/usr/bin/env python

import pyvex
import claripy
import networkx
import itertools
from collections import defaultdict
from .variable_expression import VarExpr, TraceExpr, RecursiveExpr, SimAction, Sim
from .vex.statements import translate_stmt
from .code_location import CodeLocation
from .vex_process import EngineVEX

from .parse_ast import *
from .variable_type import *


import logging
l = logging.getLogger("accurate_data_flow")
l.setLevel('INFO')

#DEBUG
max_ast_lenght = 400
max_trace_exprs = 400
icall_check = True
# icall_check = False
# taint_check = True
taint_check = False

Taint_Offset = 0x64
symbolic_count = itertools.count(1)

choose_register = True
do_forward_store_redefine = True
do_forward_concrete_load = False

loop_inc_tmps_record = defaultdict(int)
loop_inc_locations = defaultdict(set)

backward_tmp_exprs = defaultdict(list)
function_store_defs = defaultdict(dict)
record_backward_exprs = defaultdict(list)
record_redef_exprs = defaultdict(list)
record_remaining_exprs = defaultdict(list)
record_redef_labels = set()

record_binop_symbols = {}


class AccurateDataFlow(EngineVEX):
    def __init__(self, project, icall_check=False, taint_check=False):

        super(AccurateDataFlow, self).__init__(project)

        self.icall_check = icall_check
        self.taint_check = taint_check

        self.backward_store_records = set()

    # Kai code!
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


    def create_recursive_expr(self, trace_expr, base_ast, offset_ast):
        recursive_expr = RecursiveExpr(trace_expr.expr.copy(),
                                        index=trace_expr.index,
                                        base=base_ast,
                                        offset=offset_ast)

        position = recursive_expr.get_recursive_base_positon()
        recursive_expr.position = position
        print("Recursive: %s" % (recursive_expr))
        return recursive_expr

    def _check_sim_action(self, action, trace_expr):
        """
        Active or kill sim_action's live by the trace_dir and def location.
        """
        trace_dir = trace_expr.expr.trace_dir
        action_type, code_location = action.action_type, action.code_location

        if action_type == 's' and trace_dir == 'B':
            trace_expr.expr.kill_store_action_by_loc(code_location)

        elif action_type == 'wl' and trace_dir == 'F':
            trace_expr.expr.kill_load_action_by_loc(code_location)

    def _kill_exprs(self, block_exprs, trace_exprs, killed_exprs):
        for kill_expr in killed_exprs:
            try:
                trace_exprs.remove(kill_expr)
            except ValueError:
                pass
            try:
                block_exprs.remove(kill_expr)
            except ValueError:
                pass

    # Kai code!
    def _update_store_addr_with_alias(self, st_addr, st_addr_exprs, code_location, trace_exprs):

        new_exprs = []
        for trace_expr in trace_exprs:
            for st_addr_expr in st_addr_exprs:
                new_expr = trace_expr.replace(st_addr, st_addr_expr.expr.ast, st_addr_expr.expr.sim_actions)
                new_expr.expr.location = code_location
                new_expr.index = code_location.stmt_idx
                new_expr.expr.trace_dir = 'F'
                new_exprs.append(new_expr)
        return new_exprs

    def _find_taint_constraint(self, block, wr_info, code_location, trace_expr):
        """
        Find taint constraint.
        """
        sims = trace_expr.expr.sims
        opnds = wr_info[1]
        if opnds[0] in sims:
            guard_var = opnds[1]

        elif opnds[1] in sims:
            guard_var = opnds[0]

        else:
            return

        ptr_id = trace_expr.expr.ptr_id
        print("Get-cons: %x %s" % (ptr_id, guard_var))
        block.taint_constraints[ptr_id] = guard_var

    def _get_load_action_ast(self, action, sim_types, is_loop=False):
        ld_data = None
        ld_size = action.var_size
        addr_type = action.addr_type
        ld_addr = action.src_alias if type(action.src_alias) is str else action.src

        if type(action.src) is int:
            ld_data = claripy.Load(BVV(action.src), ld_size)
            sim_types[action.src] = 'ptr'

        elif is_loop and addr_type != 'S' and type(ld_addr) is str:
            ld_data = claripy.Load(BVS(ld_addr), ld_size)
            sim_types[ld_addr] = 'ptr'

        else:
            # if type(action.value) is int:
            #     ld_data = BVV(action.value, ld_size)

            if type(action.addr_value) is int and addr_type == 'S':
                ld_data = claripy.Load(BVV(action.addr_value), ld_size)
                sim_types[action.addr_value] = 'ptr'
                if addr_type == 'S':
                    arg_sym = self.judge_stack_argument(action.addr_value)
                    if arg_sym:
                        ld_data = BVS(arg_sym, ld_size)
                        sim_types[arg_sym] = 'ptr'

            elif type(ld_addr) is str:
                ld_data = claripy.Load(BVS(ld_addr), ld_size)
                sim_types[ld_addr] = 'ptr'

            # elif type(ld_addr) is tuple:
            #     addr_ast = self._calculate_simple_binop_v3(ld_addr)
            #     wr_data = claripy.Load(addr_ast, ld_size)
            #     sim_types = self._get_sim_type_v1(ld_addr, block.live_defs)

            else:
                raise Exception("Unknow ld_addr type %s" % (str(ld_addr)))

        if ld_data is None:
            raise Exception("Could not found load ast in %s" % (action))

        return ld_data

    def _get_loadg_action_ast(self, action, sim_types):
        ld_data = None
        ld_size = action.var_size
        opnds, opnds_alias = action.src[0], action.src_alias[0]
        ld_addr = opnds_alias[1] if type(opnds_alias[1]) is str else opnds[1]
        if type(action.value) is int:
            ld_data = BVV(action.value, ld_size)

        elif type(action.addr_value) is int:
            ld_data = claripy.Load(BVV(action.addr_value), ld_size)
            if action.addr_type == 'S':
                arg_sym = self.judge_stack_argument(action.addr_value)
                if arg_sym:
                    ld_data = BVS(arg_sym, ld_size)

        elif type(ld_addr) is str:
            ld_data = claripy.Load(BVS(ld_addr), ld_size)
            sim_types[ld_addr] = 'ptr'

        else:
            raise Exception("Unknow ld_addr type %s" % (str(ld_addr)))

        if ld_data is None:
            raise Exception("Could not found load ast in %s" % (action))

        return ld_data

    def _get_binop_action_ast(self, action, var_type):

        base_ast, offset_ast = None, None
        if action.inc_flag:
            binop_data, base_ast, offset_ast = self._get_increment_ast(action)

        else:
            if var_type and var_type != 'ptr':
                binop_data = self.get_binop_symbol(action.code_location)

            elif type(action.value) is int:
                binop_data = BVV(action.value, action.var_size)

            else:
                binop_data = self._get_binop_ast(action)

        return binop_data, base_ast, offset_ast

    def _get_binop_ast(self, action):

        data_info = action.src_alias if action.src_alias else action.src
        binop = data_info[0]

        if binop in self.ignore_binops:
            binop_data = self.insignificant_symbol
            return binop_data

        binop_data = self.calculate_binop_stmt_v2(data_info)

        if binop_data.op in self.shift_ops:
            binop_data= self.convert_shift_operators(binop_data)

        # print("get-binop: %s" % (binop_data))
        return binop_data

    def _get_increment_ast(self, action):
        """
        In loop, some variable with increment.
        """
        base_ast, offset_ast = None, None
        op = action.src_alias[0]
        if action.inc_flag == 1 and op in ['+', '-']:
            base, offset = action.inc_base[1], action.inc_offset[1]
            base_ast = BVS(base)
            if type(offset) is int:
                offset_ast = BVV(offset)
            else:
                offset_ast = self.get_binop_symbol(action.code_location)

            if op == '+':
                inc_data = base_ast + BVS('i') * offset_ast

            elif op == '-':
                inc_data = base_ast - BVS('i') * offset_ast

        else:
            inc_data = self._get_binop_ast(action)
            base_ast = inc_data

        return inc_data, base_ast, offset_ast

    def get_binop_symbol(self, code_location):
        """
        Get binop symbol ast from record_binop_symbols.
        """
        if code_location in record_binop_symbols:
            return record_binop_symbols[code_location]
        else:
            sym = BVS("o%d" % (next(symbolic_count)))
            record_binop_symbols[code_location] = sym
            return sym

    def _update_save_value(self, block, code_location, trace_exprs):
        """
        For the Vptr or Dptr, if the value is not 'BVS' or 'BVV', should trace the value in backward.
        """
        print("Test-update-save-value: %s" % (code_location))
        update_vars = set()
        for trace_expr in trace_exprs:
            value = trace_expr.expr.value

            if value is not None and value.op not in ['BVV', 'BVS']:
                update_vars |= get_trace_symbols(value)

        if len(update_vars) == 0:
            return []

        new_exprs = []
        trace_expr = trace_exprs[0]
        for var in update_vars:
            ast = trace_expr.expr.ast
            var_type = get_sim_type(block, var)
            new_expr = trace_expr.replace(ast, var, rep_type=var_type, base_ptr=var)
            new_expr.expr.value = BVS(var, ast.size())
            new_expr.expr.data_type = 'tmp'
            new_expr.expr.trace_dir = 'B'
            new_expr.expr.pattern = 'OB'
            new_expr.expr.source = code_location
            new_expr.expr.alias_id = code_location.__hash__()
            new_expr.expr.flag = 0x400
            new_expr.index = 0 if 'r' in var else code_location.stmt_idx
            print("should backward-update: %s\n get-new: %s" % (var, new_expr))
            new_exprs.append(new_expr)

        return new_exprs

    # Kai code!
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
            addr_ast = self._calculate_simple_binop_v1(st_addr[1])
            # addr_ast = claripy.BVS(st_addr[0], self.arch_bits, explicit_name=True)
            # offset = claripy.BVV(st_addr[1], self.arch_bits)
            # addr_ast = ptr + offset

        else:
            return []

        dst_data = claripy.Store(addr_ast, st_size)
        sim_action = self.create_sim_action(dst_data, code_location)
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(st_data, dst_data, re_sim_actions=re_sim_actions)
        new_expr.expr.store_location.append(code_location)
        new_expr.expr.location = code_location
        # new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_store_use_v1(self, action, data, trace_expr):

        code_location = action.code_location
        if code_location in trace_expr.expr.store_location:
            return []

        sim = trace_expr.expr.sims[data]
        var_type = sim.var_type if sim.var_type else action.var_type

        if not sim.live or (var_type and var_type != 'ptr'):
            return []

        addr_value = action.addr_value

        sim_types = None
        if type(addr_value) is int:
            addr_ast = BVV(addr_value)
            sim_types = {addr_value: 'ptr'}

        elif type(action.dst) is str:
            s_addr = action.dst_alias if type(action.dst_alias) is str else action.dst
            addr_ast = BVS(s_addr)
            sim_types = {s_addr: 'ptr'}

        else:
            return []

        dst_data = claripy.Store(addr_ast, action.var_size)
        sim_action = self.create_sim_action(dst_data, code_location, var_type=var_type)
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(data, dst_data, re_sim_actions=re_sim_actions, rep_info=sim_types)
        new_expr.expr.store_location.append(code_location)
        # new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if action.addr_type == 'S':
            new_expr.expr.trace_dir = 'F'

        elif action.addr_type == 'G' and trace_expr.expr.data_type == 'Aptr':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    def _find_store_use_v3(self, block, action, data_alias, trace_expr):

        code_location = action.code_location
        if code_location in trace_expr.expr.store_location:
            return []

        var_type = action.var_type if action.var_type else get_type_with_binop(block, data_alias)
        if var_type and var_type != 'ptr':
            return []

        s_data, offset = self._find_binop_data_in_sim_actions(trace_expr.expr.sim_actions, data_alias)
        if s_data is None:
            return []

        addr_value = action.addr_value
        sim_types = None
        if type(addr_value) is int:
            addr_ast = BVV(addr_value)
            sim_types = {addr_value: 'ptr'}

        elif type(action.dst) is str:
            s_addr = action.dst_alias if type(action.dst_alias) is str else action.dst
            addr_ast = BVS(s_addr)
            sim_types = {s_addr: 'ptr'}

        else:
            return []

        dst_data = claripy.Store(addr_ast, action.var_size)
        sim_action = self.create_sim_action(dst_data, code_location, var_type=var_type)
        re_sim_actions = {0: sim_action}
        dst_data = dst_data + offset if offset else dst_data
        new_expr = trace_expr.replace(s_data, dst_data, re_sim_actions=re_sim_actions, rep_info=sim_types)
        new_expr.expr.store_location.append(code_location)
        # new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if action.addr_type == 'S':
            new_expr.expr.trace_dir = 'F'

        return [new_expr]

    def _find_store_use_v3_bak(self, action, addr_alias, data_alias, var_type, trace_expr, live_defs):

        addr_value = action.addr_value
        code_location = action.code_location

        # TODO for the embedded store instructions.
        if code_location in trace_expr.expr.store_location:
            return []

        s_data = self._find_binop_data_in_sim_actions(trace_expr.expr.sim_actions, data_alias)
        if s_data is None:
            return []

        sim_types = None
        if type(addr_value) is int:
            addr_ast = BVV(addr_value)

        if type(addr_alias) is str:
            addr_ast = BVS(addr_alias)
            sim_types = {addr_alias: 'ptr'}

        elif type(addr_alias) is tuple:
            addr_ast = self._calculate_simple_binop_v3(addr_alias)
            sim_types = self._get_sim_type_v1(addr_alias, live_defs)

        else:
            return []

        dst_data = claripy.Store(addr_ast, action.var_size)
        sim_action = self.create_sim_action(dst_data, code_location, var_type=var_type)
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(s_data, dst_data, re_sim_actions=re_sim_actions, rep_info=sim_types)
        new_expr.expr.store_location.append(code_location)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if action.addr_type == 'S':
            new_expr.expr.trace_dir = 'F'

        return [new_expr]

    def _find_store_use_v4(self, action, addr_alias, value, trace_expr, live_defs):

        addr_value = action.addr_value
        code_location = action.code_location
        # print("use-v4: %s %s" % (trace_expr, trace_expr.expr.store_location))

        # TODO for the embedded store instructions.
        if code_location in trace_expr.expr.store_location:
            return []

        sim_types = None
        if type(addr_value) is int:
            addr_ast = BVV(addr_value)

        elif type(addr_alias) is str:
            addr_ast = BVS(addr_alias)
            sim_types = {addr_alias: 'ptr'}

        elif type(addr_alias) is tuple:
            addr_ast = self._calculate_simple_binop_v3(addr_alias)
            sim_types = self._get_sim_type_v1(addr_alias, live_defs)

        else:
            return []

        sub_ast = BVV(value)

        dst_data = claripy.Store(addr_ast, action.var_size)
        sim_action = self.create_sim_action(dst_data, code_location, var_type='ptr')
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(sub_ast, dst_data, re_sim_actions=re_sim_actions, rep_info=sim_types)
        new_expr.expr.store_location.append(code_location)
        new_expr.index = code_location.stmt_idx

        if action.addr_type == 'S':
            new_expr.expr.trace_dir = 'F'

        return [new_expr]

    def _find_char_store(self, block, action, s_data, code_location, trace_expr):
        """
        In forward, the taint char store in memory. If the store addr has increment, there is a string copy.
        """

        def simplify_inc_ast(inc_base, ast, block):
            var_type = get_sim_type(block, inc_base)
            print("xx-type: %s" % (var_type))
            if var_type and var_type != 'ptr':
                inc_ast = BVS(inc_base)
                zero = BVV(0)
                new_ast = ast.replace(inc_ast, zero)
                return new_ast
            else:
                return ast

        flag = False
        trace_ast = trace_expr.expr.ast
        trace_dir = None
        s_addr = action.dst

        if type(s_addr) is int:
            return []

        if not block.is_loop:
            flag = self.find_increment_addr_no_loop(block, s_addr)
            if not flag:
                return []
            addr_ast = self._generate_ast(action.dst)

        else:
            inc_base, addr_ast = self.find_increment_addr_loop(block, s_addr)
            print("Y- %s %s" % (inc_base, addr_ast))
            if inc_base:
                flag = True
                addr_ast = simplify_inc_ast(inc_base, addr_ast, block)
            else:
                addr_ast = self._generate_ast(action.dst)

        print("find increment : %s" % (flag))

        new_expr = trace_expr.replace(trace_ast, addr_ast, rep_type='ptr')
        new_expr.expr.var_type = 'ptr'
        new_expr.index = code_location.stmt_idx

        # 0x200 lable the trace_expr is taint with char but not string copy.
        if not flag:
            new_expr.expr.flag |= 0x200
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    def _find_binop_data_in_sim_actions(self, sim_actions, binop_opnds):
        # print("find-store-binop: ")
        op, opnds = binop_opnds[0], binop_opnds[1]
        for sim_action in sim_actions.values():
            name = sim_action.name
            if sim_action.binop == op and sim_action.live:
                if name == opnds:
                    return sim_action.action_data.args[0], 0

                elif name[0] == opnds[0] and type(name[1]) is int and type(opnds[1]) is int and (name[1]-opnds[1]) == 0x4:
                    return sim_action.action_data.args[0], name[1]-opnds[1]
        return None, None

    # Kai code!
    def _find_constant_store_use(self):
        return []

    def _find_argument_ptr_def_v1(self, addr_var, data_alias, var_type, var_size, code_location, trace_expr):
        new_exprs = []
        trace_ast = trace_expr.expr.ast
        var = trace_ast.args[0]

        if var == addr_var:
            store_ast = self._generate_ast_by_store(addr_var, var_size)
            data_ast = self._generate_ast(data_alias, var_size)
            new_expr = trace_expr.replace(trace_ast, data_ast, rep_type=var_type)

            value = store_ast.replace(trace_ast, trace_expr.expr.value)
            new_expr.expr.value = value
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        return new_exprs

    def _find_argument_ptr_def_v2(self, addr_info, data_alias, var_type, var_size, code_location, trace_expr):
        new_exprs = []
        trace_ast = trace_expr.expr.ast
        var = trace_ast.args[0]
        opnds = addr_info[1]

        if var in opnds:
            store_ast = self._generate_ast_by_store(addr_info, var_size)
            data_ast = self._generate_ast(data_alias, var_size)
            new_expr = trace_expr.replace(trace_ast, data_ast, rep_type=var_type)

            value = store_ast.replace(trace_ast, trace_expr.expr.value)
            new_expr.expr.value = value
            # new_expr.expr.trace_dir = 'B'
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        return new_exprs

    # Kai code!
    def _find_pointer_field_define(self, st_addr, st_data, st_size, code_location, trace_expr):

        value = trace_expr.expr.value

        # ignore store int
        if value is None or type(st_data) is int:
            return []

        new_expr = trace_expr.replace(st_addr, st_data)
        new_value = claripy.Store(value, st_size)
        new_expr.expr.value = new_value
        new_expr.expr.trace_dir = 'B'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_expr.expr.pattern = 'OB'

        return [new_expr]

    # Kai code!
    def _find_store_redefine_v1(self, addr_value, code_location, trace_expr):
        sim_actions = trace_expr.expr.sim_actions
        for i, sim_action in sim_actions.items():
            if sim_action.re_store_def(addr_value, 0, code_location):
                return True

    # Kai code!
    def _find_store_redefine_v2(self, addr_values, trace_expr):
        pass

    # Kai code!
    def _find_store_redefine_v3(self, addr, code_location, trace_expr):
        sim_actions = trace_expr.expr.sim_actions
        for i, sim_action in sim_actions.items():
            if sim_action.re_store_def(addr, 0, code_location):
                return True

    # Kai code!
    def _find_store_redefine_v4(self, addr_info, code_location, trace_expr):
        sim_actions = trace_expr.expr.sim_actions
        for i, sim_action in sim_actions.items():
            base, offset = addr_info[1]
            binop = addr_info[0]
            if sim_action.re_store_def(base, offset, code_location, binop=binop):
                return True

    # Kai code!
    def _find_put_use2(self, reg_name, put_data, code_location, trace_expr, trace_dir=None):

        new_expr = trace_expr.replace(put_data, reg_name)
        new_expr.expr.trace_dir = trace_dir
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_put_use_v1(self, reg_name, put_data, code_location, trace_expr, trace_dir):

        ast = BVV(put_data)
        new_expr = trace_expr.replace(ast, reg_name, sub_type='ptr')
        new_expr.expr.trace_dir = trace_dir
        new_expr.index = code_location.stmt_idx
        # new_expr.expr.location = code_location

        new_expr.expr.sims[reg_name].index = code_location.stmt_idx

        return new_expr

    # Kai code!
    def _find_wrtmp_use2(self, wr_tmp, wr_data, var_type, code_location, trace_expr):

        new_expr = trace_expr.replace(wr_data, wr_tmp, rep_type=var_type)
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_load_alias(self, ld_addr, code_location, trace_expr):
        """
        Check if the trace_expr contain a load alias?
        e.g. Load(Load(rax + 0x8) + 0x20) with load lias 't4 = LDle(rax + 0x8)'
        """
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        # l_offset = self._get_vex_ls_offset(ld_addrs)
        # print("l_offset: %s %s" % (code_location, l_offset))

        if type(ld_addr) is tuple:
            addr_tmp = ld_addr[0]
            addr_info = ld_addr[1]
        else:
            addr_tmp = ld_addr
            addr_info = None

        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            action_data = sim_action.action_data

            if name and name[0] and action_data.op == 'Load':
                binop = sim_action.binop
                def_locs = sim_action.def_locs

                if ((addr_info and addr_info[0] == binop and addr_info[1] == name or
                        name[1] == 0 and name[0] == addr_tmp) and code_location not in def_locs):
                    load_ptrs.append(action_data)

        return load_ptrs

    # Kai code!
    def _find_register_load_use2(self, wr_tmp, ld_addr, code_location, trace_expr):

        sim_actions = trace_expr.expr.sim_actions
        # print("f_find_load: %s %s" % (trace_expr, sim_actions))

        if len(sim_actions) == 0:
            return []

        # for index, sim_action in sim_actions.items():
        #     print("%d %s" % (index, sim_action))

        # l_offset = self._get_vex_ls_offset(ld_addrs)
        # print("l_offset: %s %s" % (code_location, l_offset))

        if type(ld_addr) is tuple:
            ld_addr_tmp = ld_addr[0]
            ld_addr_info = ld_addr[1]

        else:
            ld_addr_tmp = ld_addr
            ld_addr_info = None

        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            action_data = sim_action.action_data

            if name:
                binop = sim_action.binop
                def_locs = sim_action.def_locs

                if code_location in def_locs:
                    continue
                # print("binop %s name %s" % (binop, name))
                # print("ld_addr %s" % (str(ld_addr_info)))

                if name[1] == 0 and name[0] == ld_addr_tmp:
                    load_ptrs.append(action_data)

                elif ld_addr_info and binop == ld_addr_info[0] and name == ld_addr_info[1]:
                    load_ptrs.append(action_data)

        # print("load-ptrs: %s" % (load_ptrs))
        if len(load_ptrs) == 0:
            return []

        elif len(load_ptrs) > 1:
            l.info("There are two load expr could be update in %s %s" % (code_location, trace_expr))

        load_ptr = load_ptrs[0]

        new_expr = trace_expr.replace(load_ptr, wr_tmp)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx
        # print("f-load-new %s" % (new_expr))

        return [new_expr]

    # Kai code!
    def _find_load_use_v1(self, action, addr_value, code_location, trace_expr):

        print("load-use-v1: %s" % (trace_expr))
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        ls_actions = []
        for index, sim_action in sim_actions.items():
            if sim_action.load_use(addr_value, 0, code_location):
                ls_actions.append(sim_action)

        # print("load-ptrs: %s" % (load_ptrs))
        if len(ls_actions) == 0:
            return []

        elif len(ls_actions) > 1:
            l.info("There are two load expr could be update in %s %s" % (code_location, trace_expr))
            raise Exception

        ls_action = ls_actions[0]
        new_expr = trace_expr.replace(ls_action.action_data, action.dst, sub_type=ls_action.var_type)
        # new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx
        # print("f-load-new %s" % (new_expr))

        return [new_expr]

    # Kai code!
    def _find_load_use_v2(self):
        return []

    # Kai code!
    def _find_load_use_v3(self, wr_tmp, opnd_info, var_type, code_location, trace_expr):

        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        op, opnds = opnd_info[0], opnd_info[1]

        ls_actions = []
        for index, sim_action in sim_actions.items():
            # print("%d %s %s" % (index, sim_action, sim_action.name))
            if sim_action.load_use(opnds[0], opnds[1], code_location, binop=op, var_type=var_type):
                ls_actions.append(sim_action)

        # print(ls_actions)
        if len(ls_actions) == 0:
            return []

        elif len(ls_actions) > 1:
            l.info("There are two load expr could be update in %s %s" % (code_location, trace_expr))
            raise Exception

        ls_action = ls_actions[0]
        var_type = ls_action.var_type if ls_action.var_type else var_type

        new_expr = trace_expr.replace(ls_action.action_data, wr_tmp, rep_type=var_type)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_load_use_v4(self, action, addr_sym, var_type, code_location, trace_expr):
        sim_actions = trace_expr.expr.sim_actions
        # print("find_load_use_v4: %s" % (sim_actions))

        if len(sim_actions) == 0:
            return []

        ls_actions = []
        for index, sim_action in sim_actions.items():
            if sim_action.load_use(addr_sym, 0, code_location, var_type=var_type):
                ls_actions.append(sim_action)

        if len(ls_actions) == 0:
            return []

        elif len(ls_actions) > 1:
            l.info("There are two load expr could be update in %s %s" % (code_location, trace_expr))
            raise Exception

        ls_action = ls_actions[0]
        load_ptr = ls_action.action_data
        var_type = var_type if var_type else ls_action.var_type
        new_expr = trace_expr.replace(load_ptr, action.dst, rep_type=var_type)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = 'F'
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    def _find_load_value_v1(self):
        return []

    def _find_load_value_v2(self):
        return []

    # Kai code!
    def _find_load_value_v3(self, wr_tmp, addr_alias, var_type, var_size, code_location, trace_expr):
        """
        In forward, find the load(ptr), the trace_ast.op is BVS
        """
        new_exprs = []
        value = trace_expr.expr.value
        if value is None:
            return new_exprs

        trace_ast = trace_expr.expr.ast
        trace_sims = trace_expr.expr.sims
        if trace_ast.op != 'BVS':
            return []

        if type(addr_alias) is tuple:
            op, opnds = addr_alias[0], addr_alias[1]
            base, offset = opnds
        else:
            op, base = '+', addr_alias

        if base not in trace_sims:
            return []

        base_type = trace_sims[base].var_type
        if base_type is None or base_type == 'ptr':
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=var_type)
            new_expr.expr.trace_dir = 'F'
            new_expr.index = code_location.stmt_idx

            load_ast = self._generate_ast_by_load(addr_alias, var_size)
            # print("xu: %s" % (trace_expr))
            # print("xax %s %s %s" % (load_ast, base, trace_expr.expr.value))
            new_expr.expr.value = load_ast.replace(trace_ast, trace_expr.expr.value)
            new_exprs.append(new_expr)

        return new_exprs

    # Kai code!
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
        new_expr.expr.initial_sims()

        return [new_expr]

    # Kai code!
    def _find_constant_load_use(self):
        # TODO
        pass

    # Kai code!
    def _find_wrtmp_use_with_binop(self, wr_tmp, opnd, value, code_location, trace_expr):

        new_expr = trace_expr.replace(opnd, wr_tmp)
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_expr.expr.value = value

        return [new_expr]

    # Kai code!
    def _find_store_alias_v1(self):
        pass

    # Kai code!
    def _find_store_alias_v2(self, st_addr_info, st_data_alias, code_location, trace_expr):
        """
        For the b-expr, case "STle(t2)=rax+0x20", find whether b-expr contain alias "rax+0x20"
        """

        new_expr = None

        def check_binop_alias(op, op_data, op_offset, sim_actions):

            for sim_action in sim_actions.values():
                if (sim_action.name and
                        sim_action.action_data.op == 'Load' and
                        sim_action.name[0] == op_data and
                        sim_action.name[1] == op_offset and
                        sim_action.binop == op):
                    return True, sim_action.action_data.args[0]

            return False, None

        op, op_data, op_offset = st_data_alias[0], st_data_alias[1][0], st_data_alias[1][1]
        sim_actions = trace_expr.expr.sim_actions
        is_alias, alias_data = check_binop_alias(op, op_data, op_offset, sim_actions)

        if not is_alias:
            return None

        # st_data = self._calculate_simple_binop_v1(st_data_alias)
        print("find-store-ptr-alias-true: %s" % (code_location))
        if type(st_addr_info) is tuple:
            st_addr = self._calculate_simple_binop_v1(st_addr_info[1])
        elif type(st_addr_info) is str:
            st_addr = BVS(st_addr_info)
        else:
            return None

        # print("addr %s, save %s" % (v_addr, st_data))
        st_ast = claripy.Store(st_addr, self.arch_bits)
        sim_action = self.create_sim_action(st_ast, code_location)
        re_sim_actions = {0: sim_action}
        new_expr = trace_expr.replace(alias_data, st_ast, re_sim_actions)
        new_expr.expr.trace_dir = 'F'
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx
        new_expr.expr.bw_loc = code_location
        new_expr.expr.flag |= 0x40
        print("trace alias-v2: %s" % (new_expr))

        return new_expr

    # Kai code!
    def _find_store_ptr_alias_in_backward(self, st_addr, st_data_info, code_location, trace_expr):

        new_expr = None

        def check_binop_alias(op, op_data, op_offset, sim_actions):

            for sim_action in sim_actions.values():
                if (sim_action.name and
                        sim_action.action_data.op == 'Load' and
                        sim_action.name[0] == op_data and
                        sim_action.name[1] == op_offset and
                        sim_action.binop == op):
                    return True

            return False

        op, op_data, op_offset = st_data_info[0], st_data_info[1][0], st_data_info[1][1]
        sim_actions = trace_expr.expr.sim_actions
        is_alias = check_binop_alias(op, op_data, op_offset, sim_actions)

        if not is_alias:
            return None

        v_addr = None
        st_data = self._calculate_simple_binop_v1(st_data_info)
        print("find-store-ptr-alias-true: %s" % (code_location))
        if type(st_addr) is tuple:
            st_addr_tmp = st_addr[0]
            st_addr_info = st_addr[1]
            v_addr = self._calculate_simple_binop_v1(st_addr_info)

        if v_addr is None:
            return None

        print("addr %s, save %s" % (v_addr, st_data))
        st_ast = claripy.Store(v_addr, self.arch_bits)
        new_expr = self.create_new_trace_expr(st_ast, value=st_data, pattern='SBF', data_type='sDef', trace_dir='F', code_location=code_location)
        sim_action = self.create_sim_action(st_ast, code_location)
        new_expr.expr.sim_actions[0] = sim_action
        print("trace alias: %s" % (new_expr))

        return new_expr

    # Kai code!
    def _find_binop_alias_in_backward(self, op, wr_tmp, op_data, op_offset, code_location, trace_expr):

        new_expr = None

        def check_binop_alias(op_data, op_offset, sim_actions):

            for sim_action in sim_actions.values():
                if (sim_action.action_data.op == 'Load' and sim_action.name[0] == op_data and sim_action.name[1] == op_offset):
                    if sim_action.binop == '+' and 'Add' in op:
                        return True

                    elif sim_action.binop == '-' and 'Sub' in op:
                        return True

            return False

        # print("binop_alias: %s %s" % (wr_tmp, opnds))

        sim_actions = trace_expr.expr.sim_actions
        binop_alias = check_binop_alias(op_data, op_offset, sim_actions)

        if binop_alias:
            print("find-binop-alias-true: %s" % (code_location))

        return new_expr

    # Kai code!
    def _find_wrtmp_with_binop_alias(self, wr_tmp, opnd_info, var_type, code_location, trace_expr):

        new_expr = None

        def check_binop_alias(op, opnds, sim_actions):
            binop_alias = None

            for sim_action in sim_actions.values():
                action_data = sim_action.action_data
                if action_data.op == 'Store' and sim_action.binop == op:
                    if sim_action.name == opnds:
                        binop_alias = action_data.args[0]

                    elif sim_action.name:
                        if (sim_action.name[0] == opnds[0] and
                                sim_action.name[1] == 'o'):
                            binop_alias = opnds[0]

            return binop_alias

        op, opnds = opnd_info[0], opnd_info[1]
        sim_actions = trace_expr.expr.sim_actions
        # for i, sim_action in sim_actions.items():
        #     print(i, sim_action.name, sim_action.action_data)

        binop_alias = check_binop_alias(op, opnds, sim_actions)
        var_type = 'ptr' if var_type is None else var_type

        if binop_alias is not None:
            # print("find binop_alias: %s" % (str(binop_alias)))
            new_expr = trace_expr.replace(binop_alias, wr_tmp, rep_type=var_type)
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx

        return new_expr

    def _find_sim_action_with_binop(self, opnd_info, trace_expr):
        sim_actions = trace_expr.expr.sim_actions
        op, opnds = opnd_info[0], opnd_info[1]

        for i, sim_action in sim_actions.items():
            sim_action_data = sim_action.action_data
            print(" %s %s" % (sim_action, str(sim_action.name)))

            if sim_action.var_type == 'ptr' and sim_action_data.args[0].op in offset_ops:
                find_data = find_ptr_taint_v4(opnd_info, sim_action_data.args[0])
                if find_data is not None:
                    return find_data

    def _find_binop_taint_v3(self, reg_name, opnd_info, code_location, trace_expr):
        """
        In forward, find the taint transfer in binop, e.g. (Add r3, r3, 5)
        """
        new_exprs = []
        sim_actions = trace_expr.expr.sim_actions
        trace_sims = trace_expr.expr.sims
        opnds, opnds_type = opnd_info[1], opnd_info[3]

        opnd0_type = opnds_type[0] if opnds_type[0] else trace_sims[opnds[0]].var_type
        print("find-binop-taint-v3, %s %s" % (opnds[0], opnd0_type))
        if opnd0_type != 'ptr':
            return new_exprs

        find_data = self._find_sim_action_with_binop(opnd_info, trace_expr)

        if find_data is None:
            return new_exprs

        print("xx-find: %s" % (find_data))
        new_expr = trace_expr.replace(find_data, reg_name, rep_type=opnd0_type)
        new_expr.index = code_location.stmt_idx
        new_expr.expr.trace_dir = 'F'
        new_exprs.append(new_expr)

        return new_exprs

    def _find_binop_taint_v4(self, reg_name, opnd_info, code_location, trace_expr):
        """
        In forward, find the taint transfer in binop, e.g. (Add r3, r3, 5)
        """
        new_exprs = []
        sim_actions = trace_expr.expr.sim_actions
        trace_sims = trace_expr.expr.sims
        op, opnds, opnds_type = opnd_info[0], opnd_info[1], opnd_info[3]

        opnd0_type = opnds_type[0] if opnds_type[0] else trace_sims[opnds[0]].var_type
        print("find-binop-taint-v4, %s %s" % (opnds[0], opnd0_type))
        if opnd0_type != 'ptr':
            return new_exprs

        binop_alias, offset = None, None
        for i, sim_action in sim_actions.items():
            binop_alias, offset = sim_action.get_binop_alias(op, opnds[0], opnds[1])
            if binop_alias is not None:
                break

        if binop_alias is None:
            return new_exprs

        replacement = BVS(reg_name) + BVV(offset)
        rep_info = {reg_name: opnd0_type}
        new_expr = trace_expr.replace(binop_alias, replacement, rep_type=opnd0_type, rep_info=rep_info)
        new_expr.index = code_location.stmt_idx
        new_expr.expr.trace_dir = 'F'
        new_exprs.append(new_expr)

        return new_exprs

    def _find_binop_taint(self, wr_tmp, opnd_info, opnd0_type, code_location, trace_expr):
        """
        In forward, find the taint transfer in binop, e.g. (Add r3, r3, 5)
        """
        new_exprs = []

        trace_ast = trace_expr.expr.ast
        trace_sims = trace_expr.expr.sims
        if find_ptr_taint_v2(opnd_info, trace_ast, trace_sims):
            print("Lucky, find tiant transfer to %s" % (wr_tmp))
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type='ptr')
            new_expr.index = code_location.stmt_idx
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    def _find_binop_taint_v2(self, wr_tmp, opnd_info, var_size, code_location, trace_expr):

        new_exprs = []

        trace_ast = trace_expr.expr.ast
        trace_sym = trace_ast.args[0]
        sim = trace_expr.expr.sims[trace_sym]

        if sim.live and trace_sym in opnd_info[1]:
            rep_type = basic_types[var_size]
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=rep_type)
            new_expr.index = code_location.stmt_idx
            new_expr.expr.var_type = rep_type
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    def _find_load_taint_v2(self, wr_tmp, addr_info, var_type, var_size, code_location, trace_expr):

        new_exprs = []
        trace_sims = trace_expr.expr.sims
        trace_ast = trace_expr.expr.ast

        if (find_ptr_taint_v2(addr_info, trace_ast, trace_sims) or
                (trace_ast.op == 'BVS' and trace_ast.args[0] in addr_info[1])):
            print("Lucky-v2!!!")
            rep_type = basic_types[var_size]
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=rep_type)
            new_expr.index = code_location.stmt_idx
            new_expr.expr.var_type = rep_type
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    def _find_load_taint_v3(self, wr_tmp, addr_value, var_type, var_size, code_location, trace_expr):

        new_exprs = []
        trace_sims = trace_expr.expr.sims
        trace_ast = trace_expr.expr.ast

        if find_ptr_taint_v3(addr_value, trace_ast, trace_sims):
            print("Lucky-v3!!!")
            rep_type = basic_types[var_size]
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=rep_type)
            new_expr.index = code_location.stmt_idx
            new_expr.expr.var_type = rep_type
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    def _find_load_taint_v4(self):
        pass

    def _find_load_taint_v1(self, wr_tmp, addr_var, var_type, var_size, code_location, trace_expr):

        print("find-load-taint-v1: %s" % (trace_expr))
        new_exprs = []

        trace_sims = trace_expr.expr.sims
        trace_ast = trace_expr.expr.ast

        if find_ptr_taint_v1(addr_var, trace_ast, trace_sims):
            print("Lucky!!!")
            rep_type = basic_types[var_size]
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=rep_type)
            new_expr.index = code_location.stmt_idx
            new_expr.expr.var_type = rep_type
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    def _find_binop_pointer_v1(self, wr_tmp, wr_info, var_type, code_location, trace_expr):
        """
        The trace_expr is pointer and ast.op is BVS and value.op is BVV.
        In forward trace, propagate data with binop.
        """
        op, opnds, opnds_size, opnds_type = wr_info[0], wr_info[1], wr_info[2], wr_info[3]
        # if type(opnds[1]) is not int:
        #     return []

        new_exprs = []
        trace_sims = trace_expr.expr.sims
        trace_ast = trace_expr.expr.ast
        var_type = var_type if var_type else trace_sims[opnds[0]].var_type

        if type(opnds[1]) is int:
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=var_type)
            value = trace_expr.expr.value + opnds[1]
            new_expr.expr.value = value
            new_expr.index = code_location.stmt_idx
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        else: # TODO add it or delete it ?
            new_expr = trace_expr.replace(trace_ast, wr_tmp, rep_type=var_type)
            value = trace_expr.expr.value + BVS(opnds[1], opnds_size[1])
            new_expr.expr.value = value
            new_expr.index = code_location.stmt_idx
            new_expr.expr.trace_dir = 'F'
            new_exprs.append(new_expr)

        return new_exprs

    # Kai code!
    def _kill_register_define(self, reg_name, code_location, trace_expr):

        sims = trace_expr.expr.sims
        live_count = [1 for sim in sims.values() if sim and sim.live]
        if len(live_count) <= 1:
            return None

        new_sim = Sim(live=False, def_loc=code_location)
        new_expr = trace_expr.deep_copy()
        new_sims = new_expr.expr.sims

        new_sims[reg_name] = new_sim

        return new_expr

    # Kai code!
    def kill_expr_by_reg_redefine(self, reg_name, code_location, trace_expr):
        """
        In forward, the put will kill the register live, maybe the trace expr will be killed and should be removed.
        If the trace expr has other load/store expr is live, will generate a new expr.
        """
        sims = trace_expr.expr.sims
        live_count = [1 for sim in sims.values() if sim and sim.live]
        if len(live_count) <= 1:
            return None

        var_type = sims[reg_name].var_type
        if var_type == 'ptr':
            return None

        new_sim = Sim(live=False, def_loc=code_location, var_type=var_type)
        new_expr = trace_expr.deep_copy()
        new_sims = new_expr.expr.sims
        new_sims[reg_name] = new_sim

        # Check the sim_actions whether should changed to false live.
        copy_actions = {}
        sim_actions = new_expr.expr.sim_actions
        for index, sim_action in sim_actions.items():
            if reg_name in sim_action.action_data.variables:
                new_action = sim_action.copy()
                new_action.live = False
                copy_actions[index] = new_action

        for index, new_action in copy_actions.items():
            sim_actions[index] = new_action

        return new_expr

    # Kai code!
    def _forward_store_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, the vex 'STle(t4) = t5'.
        """
        print("psu-debug:(store) block %s has %s" % (code_location, str(action)))

        new_forward_exprs = []
        addr_alias = action.dst_alias if action.dst_alias else action.dst
        addr_type, src_type, = action.addr_type, action.src_type
        var_size = action.var_size

        st_data_alias = action.src_alias
        st_data = st_data_alias if type(st_data_alias) is str else action.src
        st_value = action.value
        var_type = action.var_type

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            trace_expr.expr.active_store_action_by_loc(code_location)
            if trace_expr.index >= current_idx:
                continue

            pattern = trace_expr.expr.pattern
            data_type = trace_expr.expr.data_type
            trace_ast = trace_expr.expr.ast
            trace_sims = trace_expr.expr.sims

            # For the f-expr to find alise expr by STle(txx) = alias_ptr.
            if 'BF' in pattern and (var_type is None or var_type == 'ptr'):

                if type(st_value) is int:
                    if st_value in trace_sims:
                        new_alias = self._find_store_use_v4(action, addr_alias, st_value, trace_expr, block.live_defs)
                        new_forward_exprs.extend(new_alias)

                if st_data in trace_sims:
                    new_alias = self._find_store_use_v1(action, st_data, trace_expr)
                    new_forward_exprs.extend(new_alias)

                    if trace_ast.op == 'BVS' and data_type in ['Vptr', 'Dptr'] and len(new_alias):
                        new_exprs = self._update_save_value(block, code_location, new_alias)
                        new_forward_exprs.extend(new_exprs)

                if type(st_data_alias) is tuple and st_data_alias[1][0] in trace_sims:
                    new_alias = self._find_store_use_v3(block, action, st_data_alias, trace_expr)
                    new_forward_exprs.extend(new_alias)

                # Find argument ptrs definition.
                if data_type == 'Aptr' and trace_ast.op == 'BVS' and trace_expr.expr.value.op in ['BVS', 'Load']:
                    if type(addr_alias) is tuple and addr_alias[0] in ['+', '-']:
                        new_exprs = self._find_argument_ptr_def_v2(addr_alias, st_data, var_type, var_size, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

                    elif type(addr_alias) is str and addr_alias in trace_sims:
                        new_exprs = self._find_argument_ptr_def_v1(addr_alias, st_data, var_type, var_size, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

            elif data_type == 'Tdata' and var_type == 'char' and trace_expr.expr.var_type != 'ptr':
                if trace_ast.op == 'BVS' and st_data in trace_sims:
                    print("Find store char!")
                    new_exprs = self._find_char_store(block, action, st_data, code_location, trace_expr)
                    new_forward_exprs.extend(new_exprs)

            if len(trace_expr.expr.sim_actions):
                new_exprs = self._do_store_define(block, action, trace_expr, trace_dir='F')
                if new_exprs:
                    new_forward_exprs.extend(new_exprs)
                    killed_exprs.append(trace_expr)

                self._do_store_redefine(block, action, trace_expr, killed_exprs)

        self._kill_exprs(block.forward_exprs, forward_exprs, killed_exprs)

        return new_forward_exprs

    def _do_store_redefine(self, block, action, trace_expr, killed_exprs):
        """
        Find store re-define and kill the trace expr.
        """
        result = False
        trace_sims = trace_expr.expr.sims
        code_location = action.code_location
        st_addr = action.dst_alias if action.dst_alias else action.dst
        addr_value = action.addr_value

        if type(addr_value) is int:
            result = self._find_store_redefine_v1(addr_value, code_location, trace_expr)

        elif type(st_addr) is str and st_addr in trace_sims:
            result = self._find_store_redefine_v3(st_addr, code_location, trace_expr)

        elif type(st_addr) is tuple and st_addr[0] in ['+', '-']:
            if st_addr[1][0] in trace_sims:
                result = self._find_store_redefine_v4(st_addr, code_location, trace_expr)

            if action.dst in trace_sims:
                result = self._find_store_redefine_v3(action.dst, code_location, trace_expr)

        if result:
            killed_exprs.append(trace_expr)

    def _do_store_define(self, block, action, trace_expr, trace_dir=None):
        """
        Find store define.
        """
        st_addr = action.dst_alias if action.dst_alias else action.dst
        addr_value = action.addr_value

        if type(addr_value) is int:
            new_exprs = self._find_concrete_addr_store_def_v1(block, action, trace_expr)

        elif type(st_addr) is str:
            new_exprs = self._find_register_store_def_v1(block, action, st_addr, trace_expr)

        elif type(st_addr) is tuple:
            new_exprs = self._find_register_store_def_v2(block, action, st_addr, trace_expr)

        else:
            l.info("not support the type of %s" % (str(action)))
            new_exprs = None

        if new_exprs and 'F' not in trace_expr.expr.pattern and trace_dir == 'F':
            for new_expr in new_exprs:
                new_expr.expr.trace_dir = 'B'

        return new_exprs

    def _forward_loadg_stmt(self, block, action, code_location, forward_exprs):
        """
        Process LoadG stmt ('t9 = if (t32) ILGop_Ident32(LDle(t19)) else t2').
        """
        print("psu-debug-f %s" % (action))
        new_forward_exprs = []
        execute_stmt_flag = False

        wr_tmp, wr_size = action.dst, action.var_size
        wr_data = action.src_alias if action.src_alias else action.src
        ld_addr, ld_size = wr_data[0][1], wr_data[1][1]
        alt_data, alt_size = wr_data[0][2], wr_data[1][2]
        var_type = action.var_type

        guard = wr_data[0][0]
        guard_ast = self.calculate_binop_stmt_v2(guard)
        true_guard = guard_ast != 0
        false_guard = guard_ast == 0
        # print('LoadG %s %s %s' % (guard_ast, true_guard, false_guard))

        b_var1 = self.find_equal_zero_guard(true_guard)
        b_var2 = self.find_equal_zero_guard(false_guard)
        # print("Has equal zero: %s %s" % (b_var1, b_var2))

        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            curr_guard = trace_expr.guard
            true_satisfiable, false_satisfiable = True, True
            if curr_guard is not None:
                constraints = [true_guard, curr_guard]
                true_satisfiable = self.judge_constraints_satisfiable(constraints)

                constraints = [false_guard, curr_guard]
                false_satisfiable = self.judge_constraints_satisfiable(constraints)

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            pattern = trace_expr.expr.pattern

            if false_satisfiable and alt_data != b_var2:
                new_exprs = None
                if type(alt_data) is str and alt_data in trace_sims:
                    sim = trace_sims[alt_data]
                    var_type = sim.var_type if sim.var_type else action.var_type
                    new_exprs = self._find_wrtmp_use2(wr_tmp, alt_data, var_type, code_location, trace_expr)

                elif type(alt_data) is tuple:
                    pass

                if new_exprs:
                    for new_expr in new_exprs:
                        new_expr.guard = false_guard
                        new_forward_exprs.append(new_expr)

            if true_satisfiable:
                new_exprs = None
                if action.addr_value is int and action.src_type != 'A':
                    addr_value = action.addr_value
                    if type(addr_value) is int:
                        if (trace_ast.op == 'BVV' and addr_value == trace_ast.args[0]
                                and pattern in ['LBF', 'SLBF', 'SBF']):
                            new_exprs = self._find_load_value_v1()

                        else:
                            new_exprs = self._find_load_use_v1(action, addr_value, code_location, trace_expr)

                    elif type(addr_value) is list:
                        if (trace_ast.op == 'BVV' and trace_ast.args[0] in addr_value
                                and pattern in ['LBF', 'SLBF', 'SBF']):
                            new_exprs = self._find_load_value_v2()

                        else:
                            new_exprs = self._find_load_use_v2()

                else:
                    addr_alias = ld_addr
                    if type(addr_alias) is tuple and addr_alias[0] in ['+', '-']:
                        new_exprs = self._find_load_use_v3(wr_tmp, addr_alias, var_type, code_location, trace_expr)

                    elif type(addr_alias) is str:
                        if (trace_ast.op == 'BVS' and addr_alias in trace_expr.expr.sims
                                and pattern in ['LBF', 'SLBF', 'SBF']):
                            new_exprs = self._find_load_value_v3(wr_tmp, addr_alias, var_type, wr_size, code_location, trace_expr)

                        elif ld_size == self.arch_bits and addr_alias in trace_sims:
                            var_type = action.var_type if action.var_type else trace_sims[addr_alias].var_type
                            if 's' in addr_alias:
                                new_exprs = self._find_wrtmp_use2(wr_tmp, addr_alias, var_type, code_location, trace_expr)

                            else:
                                new_exprs = self._find_load_use_v4(action, addr_alias, var_type, code_location, trace_expr)

                if new_exprs:
                    for new_expr in new_exprs:
                        new_expr.guard = true_guard
                        # print("expr- %s has guard %s" % (new_expr, true_guard))
                        new_forward_exprs.append(new_expr)

        return new_forward_exprs

    # Kai code!
    def _forward_put_stmt(self, block, action, code_location, forward_exprs):

        print("psu-debug: %s" % (action))

        new_forward_exprs = []
        killed_exprs = []

        reg_name, put_data, put_size = action.dst, action.src, action.var_size
        put_alias = action.src_alias
        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            data_type = trace_expr.expr.data_type
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            sim_actions = trace_expr.expr.sim_actions

            if type(action.value) is int and action.value in trace_sims:
                new_expr = self._find_put_use_v1(reg_name, action.value, code_location, trace_expr, 'F')
                new_forward_exprs.append(new_expr)

            elif type(action.value) is list and action.value[0] in trace_sims:
                new_expr = self._find_put_use_v1(reg_name, action.value[0], code_location, trace_expr, 'F')
                new_forward_exprs.append(new_expr)

            elif data_type == 'Tdata' and type(put_alias) is tuple and len(sim_actions):
                op, opnds = put_alias[0], put_alias[1]
                if op in ['+', '-'] and opnds[0] in trace_sims:
                    if type(opnds[1]) is str and has_sym_o(trace_ast):
                        new_exprs = self._find_binop_taint_v3(reg_name, put_alias, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

                    elif type(opnds[1]) is int:
                        new_exprs = self._find_binop_taint_v4(reg_name, put_alias, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

            # In forward trace, the reg will be redefined.
            if reg_name in trace_sims and trace_sims[reg_name].live:
                killed_exprs.append(trace_expr)
                new_expr = self.kill_expr_by_reg_redefine(reg_name, code_location, trace_expr)
                print("psu-debug: kill reg %s\n new_expr: %s" % (reg_name, new_expr))

                if new_expr is not None:
                    new_forward_exprs.append(new_expr)
                else:
                    trace_expr.expr.flag |= 0x20

        # In the Ijk_Ret block, if the stack reg is redefined, clear the forward_exprs.
        if reg_name == self.sp_name and block.irsb:
            jumpkind = block.irsb.jumpkind

            if jumpkind == 'Ijk_Ret':
                forward_exprs.clear()

        self._kill_exprs(block.forward_exprs, forward_exprs, killed_exprs)

        return new_forward_exprs

    # Kai code!
    def _forward_wrtmp_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, IR " t4 = Get(rdi) " could trace from rdi to tmp t4.
        """

        new_forward_exprs = []
        return []

        wr_tmp, wr_data = action[1], action[2]

        if wr_data == 'r%d' % (self.sp_offset):
            return []

        current_idx = code_location.stmt_idx
        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            # if trace_expr.expr.pattern == 'OB':
            #     continue

            trace_sims = trace_expr.expr.sims

            if wr_data in trace_sims:

                sim = trace_sims[wr_data]
                if sim and not sim.live or code_location == sim.def_loc:
                    continue

                var_type = sim.var_type if sim.var_type else action.var_type
                new_exprs = self._find_wrtmp_use2(wr_tmp, wr_data, var_type, code_location, trace_expr)

                new_forward_exprs.extend(new_exprs)

        return new_forward_exprs

    # Kai code
    def _forward_wrtmp_load_stmt(self, block, action, code_location, forward_exprs):

        print("psu-debug: %s" % (action))
        wr_tmp, var_type = action.dst, action.var_type
        addr_alias = action.src_alias if action.src_alias else action.src
        var_size = action.var_size
        addr_value = action.addr_value

        new_forward_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            sim_actions = trace_expr.expr.sim_actions
            for sim_action in sim_actions.values():
                if code_location in sim_action.def_locs:
                    sim_action.live = False

            new_exprs = []
            pattern = trace_expr.expr.pattern
            trace_ast = trace_expr.expr.ast
            trace_sims = trace_expr.expr.sims
            data_type = trace_expr.expr.data_type

            if type(addr_alias) is str and 's' in addr_alias and addr_alias in trace_sims:
                # Trace the stack arguments.
                var_type = var_type if var_type else trace_sims[addr_alias].var_type
                new_exprs = self._find_wrtmp_use2(action.dst, addr_alias, var_type, code_location, trace_expr)

            elif len(sim_actions) == 0 and pattern in ['LBF', 'SLBF', 'SBF'] and (trace_ast.op in ['BVV', 'BVS'] or trace_ast.op in offset_ops):
                # The trace_expr not contain load or store operators.
                if type(addr_value) is int:
                    if data_type == 'Tdata':
                        new_exprs = self._find_load_taint_v3(wr_tmp, addr_value, var_type, var_size, code_location, trace_expr)

                    else:
                        new_exprs = self._find_load_value_v1()

                # else:
                if data_type == 'Tdata':
                    if type(addr_alias) is tuple and addr_alias[0] in ['+', '-']:
                        new_exprs = self._find_load_taint_v2(wr_tmp, addr_alias, var_type, var_size, code_location, trace_expr)

                    elif type(addr_alias) is str and addr_alias in trace_sims:
                        new_exprs = self._find_load_taint_v1(wr_tmp, addr_alias, var_type, var_size, code_location, trace_expr)

                else:
                    new_exprs = self._find_load_value_v3(wr_tmp, addr_alias, var_type, var_size, code_location, trace_expr)

            elif len(sim_actions):
                if addr_value:
                    if type(addr_value) is int:
                        new_exprs = self._find_load_use_v1(action, addr_value, code_location, trace_expr)

                    elif type(addr_value) is list:
                        new_exprs = self._find_load_use_v2()

                elif type(addr_alias) is tuple and addr_alias[0] in ['+', '-']:
                    new_exprs = self._find_load_use_v3(wr_tmp, addr_alias, var_type, code_location, trace_expr)

                elif type(addr_alias) is str and addr_alias in trace_sims:
                    new_exprs = self._find_load_use_v4(action, addr_alias, var_type, code_location, trace_expr)

            if new_exprs:
                new_forward_exprs.extend(new_exprs)

        return new_forward_exprs

    # Kai code!
    def _forward_wrtmp_binop_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, IR "t4 = Add(t5, 0x20)" could trace into tmp t4.
        """

        print("f-wrtmp_binop: %s" % (action))
        new_forward_exprs = []

        wr_tmp = action.dst
        wr_info = action.src_alias if action.src_alias else action.src
        op, opnds, opnds_type = wr_info[0], wr_info[1], wr_info[3]
        var_type, var_size = action.var_type, action.var_size

        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            trace_value = trace_expr.expr.value
            pattern = trace_expr.expr.pattern
            data_type = trace_expr.expr.data_type

            if data_type == 'Tdata':
                if trace_ast.op == 'BVS' and trace_expr.expr.var_type != 'ptr':
                    if 'Cmp' in op:
                        self._find_taint_constraint(block, wr_info, code_location, trace_expr)

                    else:
                        new_exprs = self._find_binop_taint_v2(wr_tmp, wr_info, var_size, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

                elif op in ['+'] and opnds[0] in trace_sims and len(trace_expr.expr.sim_actions) == 0:
                    # The trace_expr is taint and not contain load or store.
                    opnd0_sim = trace_sims[opnds[0]]
                    opnd0_type = opnd0_sim.var_type if opnd0_sim.var_type else opnds_type[0]
                    if opnd0_type is None or opnd0_type == 'ptr':
                        new_exprs = self._find_binop_taint(wr_tmp, wr_info, opnd0_type, code_location, trace_expr)
                        new_forward_exprs.extend(new_exprs)

            elif data_type in ['Vptr', 'Dptr']:
                if trace_ast.op == 'BVS' and (trace_value is not None and trace_value.op == 'BVV') and opnds[0] in trace_sims:
                    new_exprs = self._find_binop_pointer_v1(wr_tmp, wr_info, var_type, code_location, trace_expr)
                    new_forward_exprs.extend(new_exprs)

        return new_forward_exprs

    def _forward_wrtmp_ite_stmt(self, block, action, code_location, forward_exprs):
        """
        In forward, process ITE stmtament ('t54 = ITE(t53,t6,t23)').
        """
        print("psu-debug-f: %s" % (action))
        new_forward_exprs = []

        wr_tmp, wr_size = action.dst, action.var_size
        guard, data1_alias, data2_alias = action.src_alias
        data1 = action.src[1] if type(data1_alias) is tuple else data1_alias
        data2 = action.src[2] if type(data2_alias) is tuple else data2_alias

        guard_ast = self.calculate_binop_stmt_v2(guard)
        true_guard = guard_ast == 0
        false_guard = guard_ast != 0
        # print(guard_ast, true_guard, false_guard)

        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index > current_idx:
                continue

            curr_guard = trace_expr.guard
            trace_sims = trace_expr.expr.sims
            # print("WI: %s with %s" % (trace_expr, curr_guard))

            true_satisfiable, false_satisfiable = True, True

            if curr_guard is not None:
                constraints = [true_guard, curr_guard]
                true_satisfiable = self.judge_constraints_satisfiable(constraints)

                constraints = [false_guard, curr_guard]
                false_satisfiable = self.judge_constraints_satisfiable(constraints)

            print("true: %s %s" % (true_satisfiable, data1))
            if true_satisfiable and data1 in trace_sims:
                sim = trace_sims[data1]
                var_type = sim.var_type if sim.var_type else action.var_type
                # print("Ite-ture: %s %s" % (sim.live, var_type))
                if sim.live and (var_type == 'ptr' or var_type is None):
                    new_exprs = self._find_wrtmp_use2(wr_tmp, data1, var_type, code_location, trace_expr)

                    for new_expr in new_exprs:
                        new_expr.guard = true_guard
                        new_forward_exprs.append(new_expr)

            print("false: %s %s" % (false_satisfiable, data2))
            if false_satisfiable and data2 in trace_sims:
                sim = trace_sims[data2]
                var_type = sim.var_type if sim.var_type else action.var_type
                if sim.live and (var_type == 'ptr' or var_type is None):
                    new_exprs = self._find_wrtmp_use2(wr_tmp, data2, var_type, code_location, trace_expr)

                    for new_expr in new_exprs:
                        new_expr.guard = false_guard
                        new_forward_exprs.append(new_expr)

        return new_forward_exprs

    # Kai code!
    def update_put_alias_in_forward(self, block, trace_expr, update_type=None):
        """
        We update trace expr's tmp or reg with its alias reg while the trace_expr is forward.
        """
        tmp_alias, f_reg_alias = block.tmp_alias, block.f_reg_alias

        if len(tmp_alias) and (update_type is None or update_type == 'tmp'):
            new_exprs = self._forward_update_tmp_alias(trace_expr, tmp_alias)
            block.forward_exprs.extend(new_exprs)
            if len(new_exprs):
                print("psu-debug: get new exprs (1) %s" % (new_exprs))

        if len(f_reg_alias) and (update_type is None or update_type == 'reg'):
            new_exprs = self._forward_update_reg_alias(trace_expr, f_reg_alias)
            block.forward_exprs.extend(new_exprs)
            if len(new_exprs):
                print("psu-debug: get new exprs (2) %s" % (new_exprs))

    # Kai code!
    def update_put_alias_in_backward(self, block, trace_expr):
        """
        We update trace expr's reg with its alias reg and generate forward expr.
        """
        new_forward_exprs = []
        old_exprs = [trace_expr]

        live_defs = block.live_defs
        trace_sims = trace_expr.expr.sims

        # print("YYYY: %s %s" % (trace_expr, trace_expr.expr.data_type))

        if trace_expr.expr.data_type != 'Ret':
            for reg, sim in trace_sims.items():
                if type(reg) is str and reg in live_defs:
                    value = None
                    d_at = live_defs[reg]
                    if type(d_at.value) is int:
                        value = d_at.value

                    elif type(d_at.src) is int and d_at.code_location.block_addr == block.addr:
                        value = d_at.src

                    if value is not None:
                        new_forward_exprs.clear()
                        for t_expr in old_exprs:
                            new_expr = t_expr.replace(reg, value)
                            new_expr.expr.trace_dir = 'F'
                            new_forward_exprs.append(new_expr)
                        old_exprs = new_forward_exprs[:]

            if len(new_forward_exprs):
                block.forward_exprs.extend(new_forward_exprs)
                for new_expr in new_forward_exprs:
                    print("Add new forward (B1): %s" % (new_expr))
                new_forward_exprs.clear()

        b_reg_alias = block.b_reg_alias
        # print("b_alias: %s" % (b_reg_alias))
        if len(b_reg_alias) == 0:
            return

        special_alias_regs = []
        old_exprs = [trace_expr]
        re_regs = [reg for reg in b_reg_alias if reg in trace_sims and (trace_sims[reg].var_type == 'ptr' or trace_sims[reg].var_type is None)]

        while re_regs:
            r_reg = re_regs.pop()
            rep_type = trace_sims[r_reg].var_type
            new_forward_exprs.clear()
            for alias_reg in b_reg_alias[r_reg]:
                if alias_reg in re_regs:
                    special_alias_regs.append((r_reg, alias_reg))
                    continue

                if rep_type is None:
                    rep_type = block.live_defs[alias_reg].var_type

                for t_expr in old_exprs:
                    new_expr = t_expr.replace(r_reg, alias_reg, rep_type=rep_type)
                    new_expr.expr.trace_dir = 'F'
                    new_forward_exprs.append(new_expr)

            if len(new_forward_exprs):
                old_exprs = new_forward_exprs[:]

        for new_expr in new_forward_exprs:
            if new_expr.expr.data_type == 'Ret':
                trace_syms = new_expr.get_trace_symbols()
                if len(trace_syms):
                    block.forward_exprs.append(new_expr)

            else:
                block.forward_exprs.append(new_expr)
                print("Add new forward (B2): %s" % (new_expr))

    # Kai code!
    def _forward_execute_stmt(self, block, action, code_location, forward_exprs):
        action_type = action.action_type
        # print("f- %s %s" % (code_location, str(action)))

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

        elif action_type == 'wi':
            new_forward_exprs = self._forward_wrtmp_ite_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'sg':
            new_forward_exprs = self._forward_storeg_stmt(block, action, code_location, forward_exprs)

        elif action_type == 'lg':
            new_forward_exprs = self._forward_loadg_stmt(block, action, code_location, forward_exprs)

        elif action_type in ['wu',]:
            new_forward_exprs  =[]

        else:
            l.info("This action type %s is not support!" % (action_type))
            new_forward_exprs  =[]

        if len(new_forward_exprs):
            print("\nForward: %s" % (code_location))
            for new_expr in new_forward_exprs:
                print("new expr %s %s\n" % (new_expr, new_expr.expr.sims))

                for i, sim_action in new_expr.expr.sim_actions.items():
                    print("sim action: %d %s" % (i, sim_action))
                print("")

        return new_forward_exprs

    # Kai code!
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

        # DEBUG
        print("Forward trace:")
        for fe in forward_exprs:
            print("  %s 0x%x" % (fe, fe.expr.flag))
            for action in fe.expr.sim_actions.values():
                print("     -> %s %s" % (action, action.def_locs))
            # for var, sim in fe.expr.sims.items():
            #     print("  %s %s" % (var, sim))

            # DEBUG
            if len(str(fe.expr.ast)) > max_ast_lenght:
                print("DEBUG: fun- %s, %s" % (block.func_addr, block))
                debug

        if len(forward_exprs) > max_trace_exprs:
            print("DEBUG (exprs_len_max): fun- %s, %s" % (block.func_addr, block))
            debug
        print("")

        for trace_expr in forward_exprs:
            self.update_put_alias_in_forward(block, trace_expr)

        alive_exprs = []
        for code_location in code_locations:
            # print("location: %s" % (code_location))

            action = actions[code_location]

            new_forward_exprs = self._forward_execute_stmt(block, action, code_location, forward_exprs)

            if len(new_forward_exprs) == 0:
                continue

            for new_expr in new_forward_exprs:
                self._judge_trace_dir(new_expr)
                trace_dir = new_expr.expr.trace_dir

                if trace_dir == 'B':
                    if action.action_type == 's':
                        new_expr.expr.kill_store_action_by_loc(code_location)
                    block.backward_exprs.append(new_expr)
                    alive_exprs.append(new_expr)

                elif trace_dir == 'F':
                    forward_exprs.append(new_expr)
                    block.forward_exprs.append(new_expr)
                    self.update_put_alias_in_forward(block, new_expr)

                else:
                    new_expr.expr.trace_dir = 'F'
                    forward_exprs.append(new_expr)
                    block.forward_exprs.append(new_expr)
                    self.update_put_alias_in_forward(block, new_expr)

                    copy_expr = new_expr.make_backward_copy()
                    if action.action_type == 's':
                        copy_expr.expr.kill_store_action_by_loc(code_location)
                    block.backward_exprs.append(copy_expr)
                    alive_exprs.append(copy_expr)
                    # print("copy expr %s" % (copy_expr))

        # for trace_expr in forward_exprs:
        #     self.update_put_alias_in_forward(block, trace_expr)

        return alive_exprs

    # Kai code!
    def backward_data_trace2(self, block, backward_exprs):
        """
        Trace expr by travel a block's isrb from last stmt to first stmt.
        """

        alive_exprs = []
        self.state.scratch.tyenv = block.irsb.tyenv
        self.state.scratch.temps = {}

        code_locations = block.code_locations
        actions = block.actions
        live_defs = block.live_defs
        reg_defs = block.reg_defs
        ins_len = len(code_locations)

        self._backward_update_put_def(block, live_defs, backward_exprs, reg_defs, alive_exprs)

        # Debug
        print("Backward trace:")

        for b_expr in backward_exprs:
            print("  %s 0x%x" % (b_expr, b_expr.expr.flag))
            for action in b_expr.expr.sim_actions.values():
                print("     -> %s %s" % (action, action.def_locs))

            # DEBUG
            # if len(str(b_expr.expr.ast)) > max_ast_lenght:
            #     print("DEBUG (ast_len_max): fun- %s, %s" % (block.func_addr, block))
            #     debug

        if len(backward_exprs) > max_trace_exprs:
            print("DEBUG (exprs_len_max): fun- %s, %s" % (block.func_addr, block))
            debug
        print("")

        for i in range(ins_len-1, -1, -1):

            code_location = code_locations[i]
            action = actions[code_location]

            new_backward_exprs = self._backward_execute_stmt2(block, action, code_location, backward_exprs)

            for new_expr in new_backward_exprs:
                if block.is_loop:
                    new_expr.cycle_locs.append(code_location)
                else:
                    self.simplify_expr(new_expr)

                self._judge_trace_dir(new_expr)
                if new_expr.expr.trace_dir == 'F':
                    self._check_sim_action(action, new_expr)
                    new_expr.copy_sim_and_action()
                    block.forward_exprs.append(new_expr)
                    alive_exprs.append(new_expr)

                elif new_expr.expr.trace_dir == 'B':
                    self._check_sim_action(action, new_expr)
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                else:
                    new_expr.expr.trace_dir = 'B'
                    self._check_sim_action(action, new_expr)
                    backward_exprs.append(new_expr)
                    block.backward_exprs.append(new_expr)

                    if 'BF' in new_expr.expr.pattern:
                        copy_expr = new_expr.make_forward_copy()
                        self._check_sim_action(action, copy_expr)
                        block.forward_exprs.append(copy_expr)
                        alive_exprs.append(copy_expr)
                        # print("copy expr %s" % (copy_expr))

        return alive_exprs

    # Kai code!
    def _backward_execute_stmt2(self, block, action, code_location, backward_exprs):
        action_type = action.action_type

        if action_type == 's':
            new_backward_exprs = self._backward_store_stmt(block, action, code_location, backward_exprs)

        # elif action_type == 'p':
        #     new_backward_exprs = self._backward_put_stmt(block, action, code_location, backward_exprs)

        # elif action_type == 'w':
        #     new_backward_exprs = self._backward_wrtmp_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wo':
            new_backward_exprs = self._backward_wrtmp_binop_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wl':
            new_backward_exprs = self._backward_wrtmp_load_stmt(block, action, code_location, backward_exprs)

        # elif action_type == 'wu':
        #     new_backward_exprs = self._backward_wrtmp_unop_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'lg':
            new_backward_exprs = self._backward_loadg_stmt(block, action, code_location, backward_exprs)

        elif action_type == 'wi':
            new_backward_exprs = self._backward_wrtmp_ite_stmt(block, action, code_location, backward_exprs)

        elif action_type in ['p', 'w', 'wu']:
            return []

        else:
            l.info("This action type %s is not support!\n %s" % (action_type, action))
            new_backward_exprs = []

        if len(new_backward_exprs):
            print("\nBackward: %s" % (code_location))
            for new_expr in new_backward_exprs:
                print("new expr %s, flag: %x" % (new_expr, new_expr.expr.flag))

                for index, sim_action in new_expr.expr.sim_actions.items():
                    print("sim_action: %d %s" % (index, sim_action))
                print("")

        return new_backward_exprs

    # Kai code!
    def _calculate_simple_binop_v1(self, binop_opnds):
        datas = []
        op, opnds = binop_opnds[0], binop_opnds[1]
        # print("NOW-%s %s" % (op, str(opnds)))
        for opnd in opnds:
            data = BVV(opnd) if type(opnd) is int else BVS(opnd)
            datas.append(data)

        if op == '+':
            result = datas[0] + datas[1]
        elif op == '-':
            result = datas[0] -  datas[1]

        return result

    # Kai code!
    def _calculate_simple_binop_v2(self, binop_opnds, data_size):
        datas = []
        op, opnds = binop_opnds[0], binop_opnds[1]
        for opnd in opnds:
            data = BVV(opnd, data_size) if type(opnd) is int else BVS(opnd, data_size)
            datas.append(data)

        if op == '+':
            result = datas[0] + datas[1]
        elif op == '-':
            result = datas[0] -  datas[1]

        return result

    # Kai code!
    def _calculate_simple_binop_v3(self, binop_opnds):
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

    # Kai code!
    def _update_register_bak(self, block, def_regs, reg_defs, live_defs, trace_expr):

        # print("psu-debug: %s\nupdate_register %s %s %s" % (code_location, def_regs, reg_defs, live_defs))

        last_index = trace_expr.index
        new_expr = trace_expr
        live_regs = def_regs[:]
        while def_regs:
            reg, reg_type = def_regs.pop(0)
            use_at = live_defs[reg]

            loc, u_var = reg_defs[reg]
            index = loc.stmt_idx

            if (type(use_at.value) is int and not block.is_loop):
                u_var = use_at.value

            elif type(use_at.src) is int:
                u_var = use_at.src

            elif use_at.action_type in ['w', 'wu', 'p']:
                u_alias = use_at.src_alias if use_at.src_alias else use_at.src
                if type(u_alias) is str:
                    u_var = u_alias
                    index = use_at.src_locs

            if u_var in live_regs:
                def_regs.append((reg, reg_type))
                continue

            new_expr = self._update_register_in_expr(reg, u_var, reg_type, last_index, index, new_expr)

        return new_expr

    def _get_reg_ast(self, action, is_loop):

        if type(action.value) is int and action.src_type == 'S':
            data = BVV(action.value, action.var_size)

        elif type(action.src) is int:
            data = BVV(action.src, action.var_size)

        elif action.action_type in ['w', 'wu', 'p']:
            reg_alias = action.src_alias if type(action.src_alias) is str else action.src
            data = BVS(reg_alias, action.var_size)

        else:
            data = BVS(action.dst, action.var_size)

        return data

    # Kai code!
    def _update_register(self, block, update_regs, reg_defs, live_defs, trace_expr):

        def contain_repeat_reg(data, update_regs):
            for var in data.variables:
                if var in update_regs:
                    return True
            return False

        trace_flag = trace_expr.expr.flag
        new_expr = trace_expr
        live_regs = update_regs[:]

        while update_regs:
            reg, reg_type = update_regs.pop(0)
            use_at = live_defs[reg]
            base_ast, offset_ast, sim_types = None, None, None

            if type(use_at.src) is int:
                data = BVV(use_at.src, use_at.var_size)

            else:
                use_at = live_defs[use_at.src]
                if use_at.action_type == 'wo':
                    data, base_ast, offset_ast = self._get_binop_action_ast(use_at, reg_type)
                    opnds_info = use_at.src_alias if use_at.src_alias else use_at.src
                    sim_types = get_opnds_type(block, opnds_info, reg_type)

                else:
                    data = self._get_reg_ast(use_at, block.is_loop)

            if contain_repeat_reg(data, live_regs):
                def_regs.append((reg, reg_type))
                continue

            if use_at.inc_flag:
                if isinstance(new_expr, RecursiveExpr):
                    # print("Kai-Rec: %s %s\n base-offset: %s %s" % (trace_expr, trace_expr.base, base_ast, offset_ast))

                    if use_at.code_location in new_expr.inc_records:
                        return None

                    elif base_ast is not None:
                        if new_expr.is_update_base(reg) and self.taint_check:
                            new_expr = new_expr.replace(reg, base_ast, rep_type=reg_type)

                        elif new_expr.with_same_inc_info(base_ast, offset_ast):
                            new_expr = new_expr.replace(reg, base_ast, rep_type=reg_type)

                        else:
                            new_expr = new_expr.replace(reg, data, rep_type=reg_type, rep_info=sim_types)

                    else:
                        new_expr = new_expr.replace(reg, data, rep_type=reg_type, rep_info=sim_types)

                else:
                    if trace_flag & 0x200:
                        if reg_type and reg_type != 'ptr':
                            base_ptr = new_expr.expr.base_ptr
                            base_ast = BVS(base_ptr) if type(base_ptr) is str else BVV(base_ptr) if type(base_ptr) is int else base_ast
                            offset_ast = BVV(1)
                            binop_data = BVV(0)
                            n_expr = new_expr.replace(reg, binop_data, rep_type=reg_type)

                        elif reg_type == 'ptr':
                            n_expr = new_expr.replace(reg, base_ast, rep_type=reg_type)

                        else:
                            n_expr = new_expr.replace(reg, data, rep_info=sim_types)
                        n_expr.expr.flag &= 0xfdff

                    else:
                        n_expr = new_expr.replace(reg, data, rep_info=sim_types)
                    new_expr = self.create_recursive_expr(n_expr, base_ast, offset_ast)
                    new_expr.inc_records.append(use_at.code_location)

            else:
                new_expr = new_expr.replace(reg, data, rep_type=reg_type, rep_info=sim_types)

            for var, sim in new_expr.expr.sims.items():
                if var in data.variables and 'r' in var:
                    sim.index = 0

        new_expr.expr.trace_dir = 'B'
        new_expr.index = trace_expr.index

        return new_expr

    # Kai code!
    def _update_register_in_expr(self, d_reg, u_var, var_type, last_index, index, trace_expr):
        """
        update the register name 'rxx' in expr with reg's use var.
        :param u_var: maybe is rxx, txx or 0xabcd.
        """
        new_expr = trace_expr.replace(d_reg, u_var, rep_type=var_type)
        new_expr.expr.trace_dir = 'B'
        if u_var in new_expr.expr.sims and new_expr.expr.sims[u_var]:
            new_expr.expr.sims[u_var].index = index
            new_expr.expr.sims[u_var].var_type = trace_expr.expr.sims[d_reg].var_type
        new_expr.index = last_index

        return new_expr

    # Kai code!
    def _backward_update_put_def(self, block, live_defs, backward_exprs, reg_defs, alive_exprs):
        """
        update the register put def in backward.
        """
        new_exprs = []
        killed_exprs = []
        new_forward_exprs = []
        ins_len = len(block.irsb.statements)

        for trace_expr in backward_exprs:
            trace_sims = trace_expr.expr.sims
            index = trace_expr.index
            if index != ins_len:
                continue

            def_regs = []
            for name, sim in trace_sims.items():
                if type(name) is str and 'r' in name and sim.live and name in reg_defs:
                    if sim.index is None or sim.index > live_defs[name].code_location.stmt_idx:
                        reg_type = sim.var_type if sim.var_type else live_defs[name].var_type
                        def_regs.append((name, reg_type))

            if len(def_regs):
                new_expr = self._update_register(block, def_regs, reg_defs, live_defs, trace_expr)
                print("b-put-newexpr: %s" % (new_expr))
                killed_exprs.append(trace_expr)

                if new_expr is None:
                    continue

                new_exprs.append(new_expr)

                if trace_expr.expr.flag & 0x200 and (not new_expr.expr.flag & 0x200):
                    new_forward_exprs.append(new_expr)
                    print("Found loop copy %s" % (new_expr))

        for new_expr in new_exprs:
            backward_exprs.append(new_expr)
            block.backward_exprs.append(new_expr)

        for new_expr in new_forward_exprs:
            pass

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)
            block.backward_exprs.remove(kill_expr)

    # Kai code!
    def _forward_update_tmp_alias(self, trace_expr, tmp_alias):
        new_exprs = []
        trace_sims = trace_expr.expr.sims
        tmps = [tmp for tmp in tmp_alias if tmp in trace_sims]

        if len(tmps):
            new_exprs.append(trace_expr)

        while tmps:
            tmp = tmps.pop()
            tmp_exprs = []
            for alias_reg in tmp_alias[tmp]:
                for t_expr in new_exprs:
                    new_expr = t_expr.replace(tmp, alias_reg)
                    new_expr.expr.trace_dir = 'F'
                    tmp_exprs.append(new_expr)
            new_exprs = tmp_exprs

        # print("tmp-alias: %s" % (new_exprs))
        return new_exprs

    # Kai code!
    def _forward_update_reg_alias(self, trace_expr, reg_alias):
        """
        In forward analysis, we should update the reg with its alias register.
        For example, in a block, 'Put(r3) = r5', should update r5 with r3.
        """
        re_regs = []
        new_forward_exprs = []
        special_alias_regs = []
        trace_sims = trace_expr.expr.sims
        expr_var_type = trace_expr.expr.var_type
        for name, sim in trace_sims.items():
            if expr_var_type == 'ptr' and sim.var_type == 'ptr' or expr_var_type != 'ptr':
                if name in reg_alias:
                    re_regs.append((name, sim.index))

        old_exprs = [trace_expr]
        # print("forward_update_reg:\n  %s\n  with: %s" % (trace_expr, reg_alias))
        while re_regs:
            r_reg, index = re_regs.pop()
            for alias_reg, loc_i in reg_alias[r_reg]:
                if index and index >= loc_i:
                    continue

                if alias_reg in re_regs:
                    special_alias_regs.append((r_reg, alias_reg))
                    continue

                for t_expr in old_exprs:
                    new_expr = t_expr.replace(r_reg, alias_reg)
                    new_expr.expr.trace_dir = 'F'
                    new_forward_exprs.append(new_expr)
            old_exprs = new_forward_exprs[:]

        return new_forward_exprs

    # Kai code!
    def _check_and_update_remaining_exprs(self, block, code_location, redef_exprs, backward_exprs):
        """
        Check and update the remaining exprs which re-backward trace to find store definition.
        """
        new_backward_exprs = []
        killed_exprs = []
        for trace_expr in backward_exprs:
            flag = trace_expr.expr.flag
            # print("test-path: %s %s" % (block.addr, trace_expr.backward_path))
            if flag & 2 != 2:
                continue
            # TODO (loop addr not in backward_path ???)
            # if flag & 2 != 2 or block.addr not in trace_expr.backward_path:
            #     continue

            alias_id, bw_loc = trace_expr.expr.alias_id, trace_expr.expr.bw_loc
            for redef_expr in redef_exprs:
                if alias_id == redef_expr.expr.alias_id and bw_loc == redef_expr.expr.bw_loc:
                    new_backward_exprs.append(redef_expr)
                    killed_exprs.append(trace_expr)

        print("www-re-backward: %s" % (new_backward_exprs))
        print("kill-expr: %s" % (killed_exprs))
        for kill_expr in killed_exprs:
            if kill_expr in backward_exprs:
                backward_exprs.remove(kill_expr)
            if kill_expr in block.backward_exprs:
                block.backward_exprs.remove(kill_expr)

        return new_backward_exprs

    # Kai code!
    def _backward_check_store_def(self, block, store_defs, code_location, backward_exprs):
        """
        Check the complex struct field store definition.
        """
        new_backward_exprs = []
        killed_exprs = []
        remove_sources = set()
        store_ids = {}

        # claculate the store ast's struct id.
        for s_expr in store_defs:
            value = s_expr.expr.value
            if value is not None and value.op == 'Store':
                struct_id = calculate_ast_struct_id(value)
                store_ids[struct_id] = s_expr

        # print("store-struct: %s" % (store_ids))

        current_idx = code_location.stmt_idx
        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx and trace_expr.expr.flag & 2 != 2:
                continue

            if block.addr not in trace_expr.backward_path:
                continue

            sim_actions = trace_expr.expr.sim_actions
            # print("back-trace: %s %s %x" % (trace_expr.expr.source, trace_expr, trace_expr.expr.flag))
            # print("backward-path: %s" % (trace_expr.backward_path))

            for sim_action in sim_actions.values():
                action_data = sim_action.action_data
                if action_data is not None and action_data.op == 'Load':
                    struct_id = calculate_ast_struct_id(action_data)
                    # print("xdx: %s %s" % (struct_id, action_data))

                    if struct_id in store_ids:
                        s_expr = store_ids[struct_id]
                        store_value = s_expr.expr.ast
                        new_expr = trace_expr.replace(action_data, store_value)
                        new_expr.expr.location = code_location
                        new_expr.index = code_location.stmt_idx
                        new_expr.expr.trace_dir = 'B'
                        new_expr.expr.flag = (new_expr.expr.flag & 0xfd) | 0x80

                        new_backward_exprs.append(new_expr)
                        remove_sources.add(trace_expr.expr.source)
                        # killed_exprs.append(trace_expr)
                        break

        for trace_expr in backward_exprs[:]:
            s = trace_expr.expr.source
            if s in remove_sources:
                # print("remove-expr: %s %s" % (s, trace_expr))
                backward_exprs.remove(trace_expr)
                block.backward_exprs.remove(trace_expr)

        # for kill_expr in killed_exprs:
        #     backward_exprs.remove(kill_expr)
        #     try:
        #         block.backward_exprs.remove(kill_expr)
        #     except:
        #         l.debug("The expr %s has been removed from block.backward_exprs" % (kill_expr))

        return new_backward_exprs

    # Kai code!
    def _backward_store_stmt(self, block, action, code_location, backward_exprs):
        """
        How to process 'store' action in backward? Any store may change the variable.
        """
        print("psu-debug: %s" % (action))
        new_backward_exprs = []
        addr_type = action.addr_type
        var_size = action.var_size
        st_addr = action.dst_alias if action.dst_alias else action.dst

        st_data_alias = action.src_alias
        st_data = st_data_alias if type(st_data_alias) is str else action.src
        st_value = action.value
        var_type = action.var_type

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:

            if (trace_expr.index <= current_idx or
                    trace_expr.expr.flag & 2 == 2 or
                    block.is_loop and code_location in trace_expr.cycle_locs):
                continue

            pattern = trace_expr.expr.pattern
            data_type = trace_expr.expr.data_type
            trace_ast = trace_expr.expr.ast
            trace_sims = trace_expr.expr.sims

            if data_type == 'Aptr' and trace_expr.expr.value.op == 'Store' and trace_ast.op not in ['BVS']:
                pass

            # In backward, save a ptr to mem could create a alias for f-expr.
            elif ('BF' in pattern and addr_type != 'S' and var_size == self.arch_bits and trace_expr.do_store_alias()):

                if type(st_value) is int:
                    if st_value in trace_sims:
                        pass
                        # new_alias = self._find_store_use_v4(action, addr_alias, st_value, trace_expr, block.live_defs)
                        # new_forward_exprs.extend(new_alias)

                else:
                    if st_data in trace_sims:
                        new_alias = self._find_store_use_v1(action, st_data, trace_expr)
                        new_backward_exprs.extend(new_alias)

                    # if type(st_data_alias) is tuple and st_data_alias[1][0] in trace_sims:
                    #     new_alias = self._find_store_use_v3(action, st_addr, st_data_alias, var_type, trace_expr, block.live_defs)
                    #     new_backward_exprs.extend(new_alias)

            # In backward, for the case: STle(rbx + 0x20) = t3
            if len(trace_expr.expr.sim_actions):
                new_exprs = self._do_store_define(block, action, trace_expr, trace_dir='B')
                new_backward_exprs.extend(new_exprs)
                if new_exprs and addr_type == 'S':
                    killed_exprs.append(trace_expr)

        self._kill_exprs(block.backward_exprs, backward_exprs, killed_exprs)

        # print("xxx-%s" % (new_backward_exprs))
        return new_backward_exprs

    # Kai code!
    def _backward_put_stmt(self, block, action, code_location, backward_exprs):
        """
        In backward, IR "Put(rdi) = t4" could trace from rid to tmp t4.
        """
        new_backward_exprs = []

        reg_name, put_datas, put_size = action[1], action[2], action[3]
        put_data = put_datas[0] if type(put_datas) is tuple else put_datas

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            pattern = trace_expr.expr.pattern
            if trace_expr.index <= current_idx or trace_expr.expr.flag & 2 == 2 or pattern== 'OB':
                continue

            trace_sims = trace_expr.expr.sims
            if type(put_data) is str and put_data in trace_sims:
                new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='F')
                new_backward_exprs.extend(new_exprs)

        return new_backward_exprs

            # if reg_name == self.sp_name:

            #     if (type(put_data) is str and put_data in trace_sims):

            #         if pattern == 'OB':
            #             new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='B')

            #         else:
            #             new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='B')

            #         new_backward_exprs.extend(new_exprs)

            #         if len(new_exprs):
            #             killed_exprs.append(trace_expr)
            #             new_backward_exprs.extend(new_exprs)

            #             try:
            #                 block.backward_exprs.remove(trace_expr)
            #             except:
            #                 pass

            # else:

            #     if (pattern != 'OB' and type(put_data) is str and put_data in trace_sims):

            #         new_exprs = self._find_put_use2(reg_name, put_data, code_location, trace_expr, trace_dir='F')
            #         new_backward_exprs.extend(new_exprs)

            #     # print("trace_sims: %s" % (trace_sims))
            #     if reg_name in trace_sims:

            #         sim = trace_sims[reg_name]
            #         if not sim.live:

            #             if code_location == sim.def_loc:
            #                 sim.live = True

            #             continue

            #         new_exprs = self._find_put_def2(reg_name, put_data, put_size, code_location, trace_expr)

            #         if len(new_exprs):
            #             killed_exprs.append(trace_expr)
            #             new_backward_exprs.extend(new_exprs)

            #             try:
            #                 block.backward_exprs.remove(trace_expr)
            #             except:
            #                 pass

        # for kill_expr in killed_exprs:
            # backward_exprs.remove(kill_expr)

        # return new_backward_exprs

    # Kai code!
    def _backward_wrtmp_stmt(self, block, action, code_location, backward_exprs):
        """
        In backward, IR "t4 = Get(rdi) or t4 = t5"
        """

        new_backward_exprs = []

        wr_tmp, wr_data, wr_size = action[1], action[2], action[3]

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            if trace_expr.index <= current_idx or trace_expr.expr.flag & 2 == 2:
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

    # Kai code!
    def _backward_wrtmp_binop_stmt(self, block, action, code_location, backward_exprs):

        print("psu-debug: %s" % (action))
        new_backward_exprs = []
        execute_stmt_flag = False
        find_increment_flag = False

        wr_tmp, wr_size = action.dst, action.var_size
        wr_data = action.src_alias if action.src_alias else action.src
        binop = wr_data[0]
        var_type = action.var_type

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:

            if (trace_expr.index <= current_idx or
                    trace_expr.expr.flag & 2 == 2 or
                    block.is_loop and code_location in trace_expr.cycle_locs):
                continue

            trace_sims = trace_expr.expr.sims

            if wr_tmp in trace_sims:
                tmp_type = trace_sims[wr_tmp].var_type
                if tmp_type and var_type is None:
                    action.var_type = tmp_type
                    infer_variable_type(None, block, wr_data, tmp_type)

                new_exprs = self._find_wrtmp_binop_def(block, action, wr_data, tmp_type, trace_expr, killed_exprs)

                for new_expr in new_exprs:
                    if tmp_type and tmp_type != 'ptr' or ((new_expr.expr.flag >> 9) & 0x1 == 1):
                        new_expr.expr.trace_dir = 'B'

                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

            # TODO binop alias?

        self._kill_exprs(block.backward_exprs, backward_exprs, killed_exprs)

        return new_backward_exprs

    # Kai code!
    def _backward_wrtmp_load_stmt(self, block, action, code_location, backward_exprs):

        print("psu-debug: %s" % action)
        new_backward_exprs = []

        wr_tmp = action.dst
        ld_addr = action.src_alias if action.src_alias else action.src
        addr_value = action.addr_value
        var_type = action.var_type

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:
            if (trace_expr.index <= current_idx or
                    trace_expr.expr.flag & 2 == 2 or
                    block.is_loop and code_location in trace_expr.cycle_locs):
                continue

            pattern = trace_expr.expr.pattern
            trace_sims = trace_expr.expr.sims

            if wr_tmp in trace_sims:
                new_exprs = self._find_wrtmp_load_def_v1(block, action, trace_expr)
                if len(new_exprs):
                    killed_exprs.append(trace_expr)
                    new_backward_exprs.extend(new_exprs)

            # Find load use in backward.
            elif 'BF' in pattern and trace_expr.do_load_alias():
                if type(ld_addr) is tuple and ld_addr[0] in ['+', '-'] and ld_addr[1][0] in trace_sims:
                    new_exprs = self._find_load_use_v3(wr_tmp, ld_addr, var_type, code_location, trace_expr)
                    new_backward_exprs.extend(new_exprs)

                elif type(ld_addr) is str and ld_addr in trace_sims:
                    new_exprs = self._find_load_use_v4(action, ld_addr, var_type, code_location, trace_expr)
                    new_backward_exprs.extend(new_exprs)

                elif type(addr_value) is int and trace_expr.do_load_alias():
                    print("Do-load-alias-backward (concret_addr).")
                    new_exprs = self._find_load_use_v1(action, addr_value, code_location, trace_expr)
                    new_backward_exprs.extend(new_exprs)
                    # print("Found: %s" % (new_exprs))

        self._kill_exprs(block.backward_exprs, backward_exprs, killed_exprs)

        return new_backward_exprs

    # Kai code!
    def _backward_loadg_stmt(self, block, action, code_location, backward_exprs):
        """
        Process the pyvex.stmt.LoadG statement
        """
        print("LoadG stmt action: %s" % (action))
        new_backward_exprs = []
        execute_stmt_flag = False

        wr_tmp, wr_size = action.dst, action.var_size
        wr_data = action.src_alias if action.src_alias else action.src
        ld_addr, ld_size = wr_data[0][1], wr_data[1][1]
        alt_data, alt_size = wr_data[0][2], wr_data[1][2]

        guard = wr_data[0][0]
        guard_ast = self.calculate_binop_stmt_v2(guard)
        true_guard = guard_ast != 0
        false_guard = guard_ast == 0
        # print('LoadG %s %s' % (true_guard, false_guard))

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:

            if (trace_expr.index <= current_idx or
                    trace_expr.expr.flag & 2 == 2 or
                    block.is_loop and code_location in trace_expr.cycle_locs):
                continue

            # print("trace_expr: %s, has guard: %s" % (trace_expr, trace_expr.guard))
            curr_guard = trace_expr.guard
            trace_sims = trace_expr.expr.sims

            if wr_tmp in trace_sims:
                tmp_type = trace_sims[wr_tmp].var_type
                true_satisfiable, false_satisfiable = True, True

                if curr_guard is not None:
                    constraints = [true_guard, curr_guard]
                    true_satisfiable = self.judge_constraints_satisfiable(constraints)

                    constraints = [false_guard, curr_guard]
                    false_satisfiable = self.judge_constraints_satisfiable(constraints)

                if true_satisfiable:
                    new_exprs_1 = self._find_wrtmp_load_def_v2(block, action, trace_expr)

                    for new_expr in new_exprs_1:
                        if tmp_type and tmp_type != 'ptr':
                            new_expr.expr.trace_dir = 'B'
                        new_expr.guard = true_guard
                        new_backward_exprs.append(new_expr)

                if false_satisfiable:
                    if type(alt_data) is tuple:
                        if tmp_type:
                            self.infer_variable_type(block.live_defs, alt_data, tmp_type)
                        sim_types = self._get_sim_type_v1(alt_data, block.live_defs)
                        new_exprs_2 = self._find_wrtmp_def_v2(wr_tmp, alt_data, tmp_type, code_location, sim_types, trace_expr)
                    else:
                        new_exprs_2 = self._find_wrtmp_def_v1(wr_tmp, alt_data, wr_size, code_location, tmp_type, trace_expr)

                    for new_expr in new_exprs_2:
                        if tmp_type and tmp_type != 'ptr':
                            new_expr.expr.trace_dir = 'B'
                        new_expr.guard = false_guard
                        new_backward_exprs.append(new_expr)

                killed_exprs.append(trace_expr)

        self._kill_exprs(block.backward_exprs, backward_exprs, killed_exprs)

        return new_backward_exprs

    # Kai code!
    def _backward_wrtmp_ite_stmt(self, block, action, code_location, backward_exprs):
        """
        Process t3 = ITE(guard, t1, t2)
        """
        print("psu-debug: %s" % (action))
        new_backward_exprs = []

        wr_tmp, wr_size = action.dst, action.var_size
        guard, data1, data2 = action.src_alias

        guard_ast = self.calculate_binop_stmt_v2(guard)
        true_guard = guard_ast == 0
        false_guard = guard_ast != 0
        # print("ITE guard: %s %s" % (true_guard, false_guard))

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in backward_exprs:

            if (trace_expr.index <= current_idx or
                    trace_expr.expr.flag & 2 == 2 or
                    block.is_loop and code_location in trace_expr.cycle_locs):
                continue

            # print("trace_expr: %s, has guard: %s" % (trace_expr, trace_expr.guard))
            curr_guard = trace_expr.guard
            trace_sims = trace_expr.expr.sims

            # if trace_expr.guard is not None:
            #     constraints = [true_guard, trace_expr.guard]
            #     satisfiable = self.judge_constraints_satisfiable(constraints)

            if wr_tmp in trace_sims:
                tmp_type = trace_sims[wr_tmp].var_type
                tmp_type = tmp_type if tmp_type else action.var_type

                true_satisfiable, false_satisfiable = True, True
                if curr_guard is not None:
                    constraints = [true_guard, curr_guard]
                    true_satisfiable = self.judge_constraints_satisfiable(constraints)

                    constraints = [false_guard, curr_guard]
                    false_satisfiable = self.judge_constraints_satisfiable(constraints)

                if true_satisfiable:
                    if type(data1) is tuple:
                        if tmp_type:
                            self.infer_variable_type(block.live_defs, data1, tmp_type)
                        sim_types = self._get_sim_type_v1(data1, block.live_defs)
                        new_exprs_1 = self._find_wrtmp_def_v2(wr_tmp, data1, tmp_type, code_location, sim_types, trace_expr)
                    else:
                        new_exprs_1 = self._find_wrtmp_def_v1(wr_tmp, data1, wr_size, code_location, tmp_type, trace_expr)

                    for new_expr in new_exprs_1:
                        if tmp_type and tmp_type != 'ptr':
                            new_expr.expr.trace_dir = 'B'
                        new_expr.guard = true_guard
                        new_backward_exprs.append(new_expr)

                if false_satisfiable:
                    if type(data2) is tuple:
                        if tmp_type:
                            self.infer_variable_type(block.live_defs, data2, tmp_type)
                        sim_types = self._get_sim_type_v1(data2, block.live_defs)
                        new_exprs_2 = self._find_wrtmp_def_v2(wr_tmp, data2, tmp_type, code_location, sim_types, trace_expr)
                    else:
                        new_exprs_2 = self._find_wrtmp_def_v1(wr_tmp, data2, wr_size, code_location, tmp_type, trace_expr)

                    for new_expr in new_exprs_2:
                        if tmp_type and tmp_type != 'ptr':
                            new_expr.expr.trace_dir = 'B'
                        new_expr.guard = false_guard
                        new_backward_exprs.append(new_expr)

                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            backward_exprs.remove(kill_expr)
            block.backward_exprs.remove(kill_expr)

        return new_backward_exprs

    def _forward_storeg_stmt(self, block, action, code_location, forward_exprs):
        """
        Process storeg stmt ('if (t58) STle(t10) = t54').
        """
        print("psu-debug-f: %s" % (action))

        new_forward_exprs = []

        st_data_alias = action.src_alias[1]
        st_data = st_data_alias if type(st_data_alias) is str else action.src[1]
        st_value = action.value

        guard = action.src_alias[0]
        addr_alias = action.dst_alias if action.dst_alias else action.dst
        addr_type, src_type, var_type = action.addr_type, action.src_type, action.var_type

        guard_ast = self.calculate_binop_stmt_v2(guard)
        true_guard = guard_ast == 1
        # false_guard = guard_ast != 1
        # print(guard_ast, true_guard, false_guard)
        # return []

        killed_exprs = []
        current_idx = code_location.stmt_idx

        for trace_expr in forward_exprs:
            if trace_expr.index >= current_idx:
                continue

            curr_guard = trace_expr.guard
            satisfiable = True

            # print('kai', curr_guard, true_guard)
            if curr_guard is not None:
                constraints = [true_guard, curr_guard]
                satisfiable = self.judge_constraints_satisfiable(constraints)

            if not satisfiable:
                continue

            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            pattern = trace_expr.expr.pattern

            # For the f-expr to find alise expr by STle(txx) = alias_ptr.
            if 'BF' in pattern and (var_type is None or var_type == 'ptr'):
                if type(st_value) is int:
                    if st_value in trace_sims:
                        new_alias = self._find_store_use_v4(action, addr_alias, st_value, trace_expr, block.live_defs)
                        new_forward_exprs.extend(new_alias)

                else:
                    if st_data in trace_sims:
                        new_alias = self._find_store_use_v1(action, st_data, trace_expr)
                        new_forward_exprs.extend(new_alias)

                    # if type(st_data_alias) is tuple and st_data_alias[1][0] in trace_sims:
                    #     new_alias = self._find_store_use_v3(action, st_addr, st_data_alias, var_type, trace_expr, block.live_defs)
                    #     new_forward_exprs.extend(new_alias)

        self._kill_exprs(block.forward_exprs, forward_exprs, killed_exprs)

        return new_forward_exprs

    # Kai code!
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
            if trace_expr.index <= current_idx or trace_expr.expr.flag & 2 == 2:
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

    # Kai code!
    def _find_register_store_def_v1(self, block, action, st_addr, trace_expr):
        """
        The st_addr is str, e.g. ('txx' or 'rxx')
        """

        code_location = action.code_location
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        var_type = action.var_type
        st_data = action.src_alias if type(action.src_alias) is str else action.src
        st_value, st_size = action.value, action.var_size

        copy_actions = {}
        load_actions = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            if name is None:
                continue

            binop = sim_action.binop
            action_data = sim_action.action_data
            if name[1] == 0 and name[0] == st_addr and action_data.op == 'Load' and sim_action.live:
                load_actions.append(sim_action)
                copy_actions[index] = sim_action.copy()

        # for index, copy_action in copy_actions.items():
        #     print("kkk- %s %s %s" % (code_location, index, copy_action))
        #     sim_actions.pop(index)
        #     copy_action.live = False
        #     sim_actions[index] = copy_action

        if len(load_actions) == 0:
            return []

        load_ptr = load_actions[0].action_data
        if var_type is None:
            var_type = load_actions[0].var_type

        if type(action.src) is int:
            data_ast = BVV(action.src)

        elif not block.is_loop and type(st_value) is int:
            data_ast = BVV(st_value, st_size)

        elif type(st_data) is str:
            if var_type is None:
                var_type = get_sim_type(block, st_data)
            data_ast = BVS(st_data, st_size)

        else:
            return []

        new_expr = trace_expr.replace(load_ptr, data_ast, rep_type=var_type)
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_register_store_def_v2(self, block, action, addr_info, trace_expr):

        code_location = action.code_location
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        var_type = action.var_type
        st_value, st_size = action.value, action.var_size
        st_data = action.src_alias if type(action.src_alias) is str else action.src
        op, opnds = addr_info[0], addr_info[1]

        copy_actions = {}
        load_actions = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            if name is None:
                continue

            binop = sim_action.binop
            action_data = sim_action.action_data
            if action_data.op == 'Load' and sim_action.live and op == binop and name == opnds:
                load_actions.append(sim_action)
                copy_actions[index] = sim_action.copy()

        # for index, copy_action in copy_actions.items():
        #     print("kkk- %s %s %s" % (code_location, index, copy_action))
        #     sim_actions.pop(index)
        #     copy_action.live = False
        #     sim_actions[index] = copy_action

        if len(load_actions) == 0:
            return []

        elif len(load_actions) > 1:
            l.info("There are two load ptr should be update!")

        load_ptr = load_actions[0].action_data
        if var_type is None:
            var_type = load_actions[0].var_type

        if type(action.src) is int:
            data_ast = BVV(action.src)

        elif not block.is_loop and type(st_value) is int:
            data_ast = BVV(st_value, st_size)

        elif type(st_data) is str:
            if var_type is None:
                var_type = get_sim_type(block, st_data)
            data_ast = BVS(st_data, st_size)

        else:
            return []

        new_expr = trace_expr.replace(load_ptr, data_ast, rep_type=var_type)
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_concrete_addr_store_def_v1(self, block, action, trace_expr):
        """
        The store addr is concrete.
        """
        code_location = action.code_location
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        var_type = action.var_type
        st_value, st_size = action.value, action.var_size
        st_data = action.src_alias if type(action.src_alias) is str else action.src
        addr_value = action.addr_value

        copy_actions = {}
        load_actions = []
        for index, sim_action in sim_actions.items():
            # print("sim_action: %s" % (sim_action))
            name = sim_action.name
            if name is None:
                continue

            binop = sim_action.binop
            action_data = sim_action.action_data
            if name[1] == 0 and name[0] == addr_value and action_data.op == 'Load' and sim_action.live:
                load_actions.append(sim_action)
                copy_actions[index] = sim_action.copy()

        # for index, copy_action in copy_actions.items():
        #     print("kkk- %s %s %s" % (code_location, index, copy_action))
        #     sim_actions.pop(index)
        #     copy_action.live = False
        #     sim_actions[index] = copy_action

        if len(load_actions) == 0:
            return []

        load_ptr = load_actions[0].action_data
        if var_type is None:
            var_type = load_actions[0].var_type

        if type(action.src) is int:
            data_ast = BVV(action.src)

        elif not block.is_loop and type(st_value) is int:
            data_ast = BVV(st_value, st_size)

        elif type(st_data) is str:
            if var_type is None:
                var_type = get_sim_type(block, st_data)
            data_ast = BVS(st_data, st_size)

        else:
            return []

        new_expr = trace_expr.replace(load_ptr, data_ast, rep_type=var_type)
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB' or (var_type and var_type != 'ptr'):
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_register_store_def(self, st_addr, st_data, st_size, code_location, trace_expr):
        # if st_addr not in trace_expr.expr.sims:
        #     return []

        store_label = False

        # print("b_find_store: %s" % (trace_expr))
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            binop = sim_action.binop
            action_data = sim_action.action_data
            if name is None:
                continue

            if name[1] == 0 and name[0] == st_addr and action_data.op == 'Load':
                load_ptrs.append(action_data)
            elif name[1] == 0:
                store_label = True

        # record the store maybe alias ptr store action
        if len(load_ptrs) == 0:
            if store_label:
                self.backward_store_records.add(code_location)
                trace_expr.expr.flag |= 4
            return []

        if type(st_data) is int:
            if st_data == 0:
                l.info("The store data is zero, maybe the callee redefined it. do it future!")

            st_data = claripy.BVV(st_data, st_size)

        elif type(st_data) is str:
            st_data = claripy.BVS(st_data, st_size, explicit_name=True)

        elif type(st_data) is tuple:
            st_data = self._calculate_simple_binop_v1(st_data[1])

        load_ptr = load_ptrs[0]
        new_expr = trace_expr.replace(load_ptr, st_data)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_register_store_def2(self, st_addr, st_data, st_size, code_location, trace_expr):

        store_label = False

        # print("b_find_store: %s" % (trace_expr))
        sim_actions = trace_expr.expr.sim_actions
        if len(sim_actions) == 0:
            return []

        # for index, sim_action in sim_actions.items():
        #     print("%d %s" % (index, sim_action.action_data))
        #     print(sim_action.name)

        ls_addr_tmp = st_addr[0]
        ls_addr, ls_offset = st_addr[1][1][0], st_addr[1][1][1]
        _op = st_addr[1][0]
        load_ptrs = []
        for index, sim_action in sim_actions.items():
            name = sim_action.name
            binop = sim_action.binop
            action_data = sim_action.action_data

            if name and action_data.op == 'Load':
                if name[1] == ls_offset:
                    if _op == binop and name[0] == ls_addr:
                        load_ptrs.append(action_data)

                    else:
                        store_label = True
                elif name[1] == 0 and name[0] == ls_addr_tmp:
                    load_ptrs.append(action_data)

        if store_label:
            self.backward_store_records.add(code_location)
            trace_expr.expr.flag |= 4

        if len(load_ptrs) == 0:
            return []

        elif len(load_ptrs) > 1:
            l.info("There are two load ptr should be update!")

        # print("backward-find-store: %s" % (load_ptrs))

        if type(st_data) is int:
            if st_data == 0:
                l.info("The store data is zero, maybe the callee redefined it. do it future!")

            st_data = claripy.BVV(st_data, st_size)

        elif type(st_data) is str:
            st_data = claripy.BVS(st_data, st_size, explicit_name=True)

        elif type(st_data) is tuple:
            st_data = self._calculate_simple_binop_v1(st_data[1])

        load_ptr = load_ptrs[0]
        new_expr = trace_expr.replace(load_ptr, st_data)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if new_expr.expr.pattern == 'OB':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_put_def2(self, reg_name, put_data, put_size, code_location, trace_expr):

        trace_dir = None
        if type(put_data) is int:
            put_data = claripy.BVV(put_data, put_size)
            trace_dir = 'B'

        # print("put_def: %s %s %s" % (trace_expr, reg_name, put_data))
        new_expr = trace_expr.replace(reg_name, put_data)
        new_expr.expr.location = code_location
        new_expr.expr.trace_dir = trace_dir
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_wrtmp_def_v1(self, wr_tmp, wr_data, wr_size, code_location, var_type, trace_expr):

        if type(wr_data) is int:
            wr_data = BVV(wr_data, wr_size)
        else:
            wr_data = BVS(wr_data, wr_size)

        new_expr = trace_expr.replace(wr_tmp, wr_data, rep_type=var_type)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        # if type(wr_data) is str and 'r' in wr_data:
        #     wr_reg_sim = new_expr.expr.sims[wr_data]
        #     wr_reg_sim.def_loc = code_location

        return [new_expr]

    # Kai code
    def _find_wrtmp_def_v2(self, wr_tmp, data_info, var_type, code_location, sim_types, trace_expr):
        """
        The data_info's type is Tuple, '(op, (opnd1, opnd2), (opnd1_size, opnd2_size))'
        """
        if var_type and var_type != 'ptr':
            wr_data = BVS("o%d" % (next(symbolic_count)))
        else:
            wr_data = self.calculate_binop_stmt_v2(data_info)

        new_expr = trace_expr.replace(wr_tmp, wr_data, rep_info=sim_types)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_wrtmp_def2(self, wr_tmp, wr_data, wr_size, code_location, trace_expr):

        if type(wr_data) is int:
            wr_data = claripy.BVV(wr_data, wr_size)

        new_expr = trace_expr.replace(wr_tmp, wr_data)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if type(wr_data) is str and 'r' in wr_data:
            wr_reg_sim = new_expr.expr.sims[wr_data]
            wr_reg_sim.def_loc = code_location

        return [new_expr]

    # Kai code!
    def _find_wrtmp_binop_def(self, block, action, opnds_info, var_type, trace_expr, killed_exprs):

        new_exprs = []
        wr_tmp = action.dst
        code_location = action.code_location
        sim_types = get_opnds_type(block, opnds_info, var_type)

        if action.inc_flag:
            binop_data, base_ast, offset_ast = self._get_increment_ast(action)
            # if isinstance(trace_expr, RecursiveExpr):
            #     print("Kai-Rec: %s %s\n base-offset: %s %s" % (trace_expr, trace_expr.base, base_ast, offset_ast))

            if isinstance(trace_expr, RecursiveExpr):

                if code_location in trace_expr.inc_records:
                    killed_exprs.append(trace_expr)
                    return new_exprs

                elif base_ast is not None:
                    if trace_expr.is_update_base(wr_tmp) and self.taint_check:
                        new_expr = trace_expr.replace(wr_tmp, base_ast, rep_type=var_type)

                    elif trace_expr.with_same_inc_info(base_ast, offset_ast):
                        new_expr = trace_expr.replace(wr_tmp, base_ast, rep_type=var_type)

                    else:
                        new_expr = trace_expr.replace(wr_tmp, binop_data, rep_info=sim_types)

                else:
                    new_expr = trace_expr.replace(wr_tmp, binop_data, rep_info=sim_types)

            else:
                n_expr = trace_expr.replace(wr_tmp, binop_data, rep_info=sim_types)
                new_expr = self.create_recursive_expr(n_expr, base_ast, offset_ast)

            new_expr.inc_records.append(code_location)
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        else:
            if var_type and var_type != 'ptr' and self.taint_check:
                binop_data = self.get_binop_symbol(code_location)

            elif action.src_type != 'S':
                binop_data = self._get_binop_ast(action)

            elif type(action.value) is int:
                binop_data = BVV(action.value, action.var_size)

            else:
                binop_data = self._get_binop_ast(action)

            new_expr = trace_expr.replace(wr_tmp, binop_data, rep_type=var_type, rep_info=sim_types)
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        print("binop-kai: %s %s" % (binop_data, sim_types))

        return new_exprs

    # Kai code!
    def _find_wrtmp_unop_def(self, wr_tmp, wr_data, code_location, trace_expr):

        new_expr = trace_expr.replace(wr_tmp, wr_data)
        # new_expr.get_trace_variable(trace_expr.expr.killed_vars)
        new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        return [new_expr]

    # Kai code!
    def _find_wrtmp_load_def_v1(self, block, action, trace_expr):

        wr_tmp = action.dst
        code_location = action.code_location
        sim_types = {}

        var_type = trace_expr.expr.sims[wr_tmp].var_type
        if var_type:
            action.var_type = var_type
        else:
            var_type = get_sim_type(block, wr_tmp)

        if var_type and var_type != 'ptr' and trace_expr.expr.data_type == 'Tdata':
            ld_data = BVS('o', action.var_size)
        else:
            ld_data = self._get_load_action_ast(action, sim_types, is_loop=block.is_loop)

        if ld_data.op == 'Load':
            sim_action = trace_expr.create_sim_action(ld_data, def_loc=code_location, var_type=var_type, live=True)
            sim_action.var_type = var_type
            re_sim_actions = {0: sim_action}
        else:
            re_sim_actions = {}

        new_expr = trace_expr.replace(wr_tmp, ld_data, re_sim_actions, rep_info=sim_types)
        new_expr.index = code_location.stmt_idx

        if var_type and var_type != 'ptr' or trace_expr.expr.flag & 0x200:
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    # Kai code!
    def _find_wrtmp_load_def_v2(self, block, action, trace_expr):

        wr_tmp = action.dst
        code_location = action.code_location
        sim_types = {}
        ld_data = self._get_loadg_action_ast(action, sim_types)

        var_type = trace_expr.expr.sims[wr_tmp].var_type
        if var_type:
            action.var_type = var_type
        else:
            var_type = get_sim_type(block, wr_tmp)

        if ld_data.op == 'Load':
            sim_action = self.create_sim_action(ld_data, code_location)
            sim_action.var_type = var_type
            re_sim_actions = {0: sim_action}
        else:
            re_sim_actions = {}
        new_expr = trace_expr.replace(wr_tmp, ld_data, re_sim_actions, rep_info=sim_types)
        # new_expr.expr.location = code_location
        new_expr.index = code_location.stmt_idx

        if var_type and var_type != 'ptr':
            new_expr.expr.trace_dir = 'B'

        return [new_expr]

    def _judge_trace_dir(self, trace_expr):
        if (trace_expr.expr.data_type == 'Aptr' and
                trace_expr.expr.value.op == 'Store' and
                trace_expr.expr.ast.op not in ['BVS', 'Load']):
            trace_expr.expr.trace_dir = 'B'

    # Kai code!
    def _find_constant_store_def(self):

        return []

    # Kai code!
    def _label_and_create_reforward_exprs(self, alias_ptr, code_location, trace_exprs):
        """
        In backward, some load expr should re-forward to find store def.
        """
        alias_ptr = alias_ptr[1] if type(alias_ptr) is tuple else alias_ptr
        new_exprs = []
        for trace_expr in trace_exprs:
            if trace_expr.expr.is_contain_load_ptr(alias_ptr):
                new_expr = trace_expr.make_forward_copy()
                new_expr.expr.bw_loc = code_location
                new_expr.forward_path = trace_expr.forward_path
                new_expr.backward_path = trace_expr.backward_path
                new_expr.expr.flag |= 0x40
                # print("re-forward: %s %s 0x%x" % (new_expr, new_expr.expr.pattern, new_expr.expr.flag))
                new_exprs.append(new_expr)

        return new_exprs

    # Kai code!
    def _create_increment_data(self, wr_data_info, wr_size):
        binop = wr_data_info[0]
        opnds = wr_data_info[1]
        # print("psu-debug: %s %s" % (binop, opnds))
        inc_sym, inc_offset = None, None
        inc_data = None

        if binop == '+':
            for opnd in opnds:
                if type(opnd) is int:
                    inc_offset = opnd
                elif type(opnd) is str:
                    inc_sym = opnd

            if inc_sym and inc_offset:
                sym_ast = claripy.BVS(inc_sym, wr_size, explicit_name=True)
                i = claripy.BVS('i', wr_size, explicit_name=True)
                inc_data = sym_ast + i * inc_offset

        elif binop == '-':
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

    def get_constraint_copy(self, block):
        # print("\nLoop block %s get constraints" % (block))
        irsb = block.irsb
        irsb.pp()
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

        # print("constraints: %s %s %s" % (last_cmp_op, cmp_dep1, cmp_dep2))
        # if constraint is not None:
        #     print("con: %s" % (constraint))
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

    # Kai code!
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

    def get_user_trace_data(self, block, user_location):
        """
        :param block: a cfg block
        :param user_location: a CodeLocation, which is defined by user for data tracing.
        """
        irsb = block.irsb
        statements = irsb.statements
        stmt = statements[user_location.stmt_idx]
        if hasattr(stmt, 'data') and isinstance(stmt.data, pyvex.expr.RdTmp):
            tmp = stmt.data.tmp
            trace_data = claripy.BVS('t%d' % (tmp), self.arch_bits, explicit_name=True)
            return trace_data

    # Kai code!
    def create_sim_action(self, action_data, def_loc, var_type=None):
        all_deref_info = get_all_deref_info(action_data)
        deref_info = all_deref_info[0]

        binop, name, data = deref_info[0], deref_info[1], deref_info[2]
        new_sim_action = SimAction(name, binop, data)
        new_sim_action.def_locs.add(def_loc)
        if var_type:
            new_sim_action.var_type = var_type

        return new_sim_action

    # Kai code!
    def create_sim_actions(self, action_data, def_loc, var_type=None):
        # print("create_sim_actions: %s %s" % (action_data, def_loc))
        new_sim_actions = {}
        all_deref_info = get_all_deref_info(action_data)
        for i, deref_info in all_deref_info.items():
            binop, name, data = deref_info[0], deref_info[1], deref_info[2]
            new_sim_action = SimAction(name, binop, data)
            new_sim_action.def_locs.add(def_loc)
            if var_type:
                new_sim_action.var_type = var_type

            new_sim_actions[i] = new_sim_action

        return new_sim_actions

    def _get_vex_ls_offset(self, addr_info):
        _len = len(addr_info)
        if _len == 1:
            offset = 0
        elif _len > 1:
            offset = addr_info[1][1][1]
        # print("get offset: %s" % (offset))
        return offset

    def create_new_trace_expr(self, ast, value=None, pattern=None, data_type=None, trace_dir=None, code_location=None):
        var_expr = VarExpr(ast, value=value, pattern=pattern, data_type=data_type, trace_dir=trace_dir)
        var_expr.location = code_location
        var_expr.alias_id = code_location.__hash__()
        var_expr.source = code_location
        var_expr.initial_sims()

        trace_expr = TraceExpr(var_expr, index=code_location.stmt_idx)
        return trace_expr

    def _generate_ast_by_binop(self, opnd_info, data_size, code_location, block):
        op, opnds = opnd_info
        if op in ['+', '-']:
            ast = self._calculate_simple_binop_v2(opnd_info, data_size)
        elif op in self.ignore_binops:
            ast = self.insignificant_symbol
        else:
            # stmt = block.irsb.statements[code_location.stmt_idx]
            # translate_stmt(stmt, self.state)
            # ast = self.state.scratch.tmp_expr(stmt.tmp)
            ast = self.calculate_binop_stmt(op, opnds)
        print("psu-debug: generate ast %s" % (ast))
        return ast

    def _generate_ast_by_load(self, ld_addr, data_size):
        if type(ld_addr) is tuple:
            addr = self._calculate_simple_binop_v3(ld_addr)
            ast = claripy.Load(addr, data_size)
        else:
            addr = BVS(ld_addr) if type(ld_addr) is str else BVV(ld_addr)
            ast = claripy.Load(addr, data_size)
        return ast

    def _generate_ast_by_store(self, s_addr, data_size):
        if type(s_addr) is tuple:
            addr = self._calculate_simple_binop_v3(s_addr)
            ast = claripy.Store(addr, data_size)
        else:
            addr = BVS(s_addr) if type(s_addr) is str else BVV(s_addr)
            ast = claripy.Store(addr, data_size)
        return ast

    def _generate_ast(self, data, data_size=None):
        if type(data) is tuple:
            data_ast = self.calculate_binop_stmt_v2(data)
        else:
            data_size = self.arch_bits if data_size is None else data_size
            data_ast = BVS(data, data_size) if type(data) is str else BVV(data, data_size)
        return data_ast

    def _generate_ast_by_tmp(self, block, tmp):
        """
        Generate the tmp's alias expr by the live_defs.
        """
        live_defs = block.live_defs

        use_info = live_defs[tmp]
        stmt_type, code_location, use_data, data_size = use_info[0], use_info[1], use_info[2], use_info[3]
        print("psu-debug: %s %s" % (tmp, str(use_info)))

        asts = []
        if stmt_type == 'l':
            ast = self._generate_ast_by_load(use_data, data_size)
            asts.append(ast)
            # print("%s = %s" % (tmp, ast))
            block.tmp_info[tmp] = ast

        elif stmt_type == 'o':
            ast = self._generate_ast_by_binop(use_data, data_size, code_location, block)
            asts.append(ast)
            # print("%s = %s" % (tmp, ast))
            block.tmp_info[tmp] = ast

        elif stmt_type == 'w':
            ast = BVV(use_data, data_size) if type(use_data) is int else BVS(use_data, data_size)
            asts.append(ast)
            # print("%s = %s" % (tmp, ast))
            block.tmp_info[tmp] = ast

        elif stmt_type == 'i':
            pass

        new_tmps = set()
        for tmp in map(lambda ast: [sym for sym in ast.variables if 't' in sym], asts):
            new_tmps |= set(tmp)

        for t in new_tmps:
            self._generate_ast_by_tmp(block, t)

    def generate_expr_by_ud_chain(self, block, tmp, trace_dir='B'):
        """
        For the given tmp txx, generate it's ast expr in backward.
        """
        tmp_ast = BVS(tmp)
        code_location = block.live_defs[tmp][1]
        tmp_expr = self.create_new_trace_expr(tmp_ast, code_location=code_location)
        tmp_exprs = [tmp_expr]
        new_exprs = self._update_expr_by_ud_chain(block, tmp_exprs, trace_dir=trace_dir)
        # print("tmp: %s, new-exprs: %s" % (tmp_expr, new_exprs))

        return new_exprs

    def _update_expr_with_asts(self, use, u_def, code_location, trace_expr):

        new_exprs = []
        u_defs = []
        u_defs = u_def if type(u_def) is list else [u_def]
        for d in u_defs:
            re_sim_actions = {}
            if d.op == 'Load':
                sim_action = self.create_sim_action(d, code_location)
                re_sim_actions = {0: sim_action}
            new_expr = trace_expr.replace(use, d, re_sim_actions)
            new_expr.expr.location = code_location
            new_expr.index = code_location.stmt_idx
            new_exprs.append(new_expr)

        return new_exprs

    def _update_expr_by_ud_chain(self, block, trace_exprs, trace_dir='B'):
        results = []
        block_tmp_info = block.tmp_info

        for trace_expr in trace_exprs:
            new_exprs = []
            trace_sims = trace_expr.expr.sims
            uses = [u for u, sim in trace_sims.items() if 't' in u]
            if len(uses):
                use = uses[0]
                if use not in block_tmp_info:
                    self._generate_ast_by_tmp(block, use)

                use_d = block_tmp_info[use]
                if trace_dir == 'F':
                    if self._judge_reg_live_in_forward(block, use_d):
                        code_location = block.live_defs[use][1]
                        new_exprs = self._update_expr_with_asts(use, use_d, code_location, trace_expr)
                    # else:
                    new_exprs_two = self._update_forward_expr_with_register(block, use, trace_expr)
                    if len(new_exprs_two):
                        new_exprs.extend(new_exprs_two)
                else:
                    code_location = block.live_defs[use][1]
                    new_exprs = self._update_expr_with_asts(use, use_d, code_location, trace_expr)
            if len(new_exprs) == 0:
                results.append(trace_expr)
            else:
                new_exprs = self._update_expr_by_ud_chain(block, new_exprs, trace_dir)
                results.extend(new_exprs)
        return results

    def _judge_reg_live_in_forward(self, block, ast_data):
        """
        Judge the reg (rxx) in ast_data is live to block exit in forward.
        """
        reg_defs = block.reg_defs
        return not any([reg for reg in ast_data.variables if reg in reg_defs])

    def _update_forward_expr_with_register(self, block, u_tmp, trace_expr):
        new_exprs = []
        reg_defs = block.reg_defs
        alias_regs = [reg for reg, tmp in reg_defs.items() if tmp == u_tmp]
        for alias_reg in alias_regs:
            new_expr = trace_expr.replace(u_tmp, alias_reg)
            new_expr.expr.trace_dir = 'F'
            new_expr.index = len(block.irsb.statements)
            new_exprs.append(new_expr)
        return new_exprs

    def _generate_forward_exprs_update_tmp(self, block, u_tmp, code_location, trace_exprs):
        """
        Generate forward exprs by updating the tmp in trace exprs with tmp's alias.
        """
        if type(u_tmp) is not str or 't' not in u_tmp:
            return []

        new_exprs = []
        tmp_aliases = self.generate_expr_by_ud_chain(block, u_tmp, trace_dir='F')
        for trace_expr in trace_exprs:
            for tmp_alias in tmp_aliases:
                new_expr = trace_expr.replace(u_tmp, tmp_alias.expr.ast, tmp_alias.expr.sim_actions)
                new_expr.expr.trace_dir = 'F'
                new_expr.expr.location = code_location
                new_expr.index = code_location.stmt_idx
                new_exprs.append(new_expr)

        return new_exprs

    def _clear_alias_redef_exprs(self, block, forward_exprs, killed_exprs):
        """
        Remove the alias exprs which would be re-define by store.
        """
        if len(killed_exprs):
            print("clear_alise_redef_exprs: %s" % (killed_exprs))
        remove_exprs1, remove_exprs2 = [], []
        for kill_expr in killed_exprs:
            bw_loc = kill_expr.expr.bw_loc
            alias_id = kill_expr.expr.alias_id
            for f_expr in forward_exprs:
                if f_expr.expr.bw_loc == bw_loc and f_expr.expr.alias_id == alias_id:
                    remove_exprs1.append(f_expr)

            for f_expr in block.forward_exprs:
                if f_expr.expr.bw_loc == bw_loc and f_expr.expr.alias_id == alias_id:
                    remove_exprs2.append(f_expr)

            for r_expr in remove_exprs1:
                try:
                    forward_exprs.remove(r_expr)
                except ValueError:
                    pass
            for r_expr in remove_exprs2:
                try:
                    block.forward_exprs.remove(r_expr)
                except ValueError:
                    pass

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

    def get_ptr_xref_info(self, block, ptr_info, ptr_type=None):

        collect_info = []
        code_locations = block.code_locations
        actions = block.actions

        ptr_values = [t[1] for t in ptr_info]

        for code_location in code_locations:
            action = actions[code_location]
            action_type = action.action_type

            if action_type == 'p' or action_type == 'wl' or action_type == 'wo':
                value = action.value
                if value in ptr_values:
                    trace_ast = BVS(action.dst)
                    ptr_ast = BVV(value)
                    xref_info = (code_location.stmt_idx, ptr_ast, trace_ast)
                    collect_info.append(xref_info)

            elif action_type == 's':
                value = action.value
                if value in ptr_values:
                    addr_ast = BVS(action.dst) if type(action.dst) is str else BVV(action.dst)
                    trace_ast = claripy.Store(addr_ast, self.arch_bits)
                    ptr_ast = BVV(value)
                    xref_info = (code_location.stmt_idx, ptr_ast, trace_ast)
                    collect_info.append(xref_info)

        return collect_info

    def get_ptr_xref_info_block(self, block, ptr_info):
        collect_info = []
        collect_indexs = []
        solve_xrefs = []
        unsolve_ptrs = set()
        print("resolve concret ptr: %s %s" % (block, ptr_info))

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

    def get_icall_ptr(self, block):
        """
        Get the indirect callsite target's tmp backward ast data in VEX
            call qword ptr [rax+10]
            NEXT: PUT(rip) = t3; Ijk_Call
        """
        trace_tmp = None
        irsb = block.irsb
        self.state.scratch.tyenv = irsb.tyenv
        self.state.scratch.temps = {}
        irsb.pp()
        live_defs = block.live_defs
        for stmt in irsb.statements:
            if type(irsb.next) is pyvex.expr.RdTmp:
                trace_tmp = 't%d' % irsb.next.tmp

        if trace_tmp is None:
            return None, None

        use_at = live_defs[trace_tmp]
        if use_at.action_type in ['w', 'p', 'wu']:
            use_var = use_at.src_alias if type(use_at.src_alias) is str else use_at.src
            use_loc = use_at.code_location
        else:
            use_var = use_at.dst
            use_loc = CodeLocation(use_at.code_location.block_addr, use_at.code_location.stmt_idx+1)
        use_data = BVS(use_var)
        # print("Icall target: %s %s" % (use_var, use_loc))
        return use_data, use_loc

    def _get_sim_type_v1(self, opnds_info, live_defs):
        sim_types = {}
        opnds, opnds_type = opnds_info[1], opnds_info[3]
        for opnd, opnd_type in zip(opnds, opnds_type):
            if opnd_type:
                sim_types[opnd] = opnd_type

            elif opnd in live_defs:
                vtype = live_defs[opnd].var_type
                if vtype:
                    sim_types[opnd] = vtype

        return sim_types

    def _get_offset(self, binop_data, sim_types):
        """
        Get the base and offset in binop_data based on var types.
        """
        for var in binop_data.args:
            if var.op == 'xx':
                pass

    def set_trace_expr_constraint_in_backward(self, src, dst, backward_exprs):
        """
        In backward, set trace expr's constraint.
        """
        print("Set-constraint (B) in %s -> %s" % (src, dst))

        if src.addr not in dst.guard:
            return

        guard = dst.guard[src.addr]
        # print(guard)
        if guard.op == '__eq__':
            return

        var0, var1 = get_guard_args(src, guard)
        if var0 is None or var1 is None:
            return

        # print(var0, var1)
        if var0[1] == 0 or var1[1] == 0:
            return

        elif var0[0] is None and var1[0] is None:
            return

        for trace_expr in backward_exprs:
            v0, v1 = var0[0], var1[0]
            c0, c1 = var0[1], var1[1]
            trace_sims = trace_expr.expr.sims

            if c1 and v0 in trace_sims:
                # print("Hello-> %s %s %s" % (trace_expr, v0, c1))
                if c1 not in trace_expr.expr.constraints:
                    trace_expr.expr.constraints.append(c1)

            elif c0 and v1 in trace_sims:
                if c0 not in trace_expr.expr.constraints:
                    trace_expr.expr.constraints.append(c0)

    def get_loop_copy_expr(self, block, var, binop_data, base_ast, offset_ast, var_type, trace_expr):
        """
        Find loop copy and generate expr.
        """
        if var_type and var_type != 'ptr':
            base_ptr = trace_expr.expr.base_ptr
            base_ast = BVS(base_ptr) if type(base_ptr) is str else BVV(base_ptr) if type(base_ptr) is int else base_ast
            binop_data = BVV(0)
            n_expr = trace_expr.replace(var, binop_data)

        elif reg_type == 'ptr':
            n_expr = trace_expr.replace(var, base_ast, rep_type=reg_type)

        else:
            n_expr = trace_expr.replace(var, binop_data, rep_info=sim_types)
        n_expr.expr.flag &= 0xfdff
