#!/usr/bin/env python


from collections import defaultdict
from .parse_ast import *
from dataflow.data_process import ICALL_SOURCES

tainted_command_locs = []
tainted_length_locs = []

weaks_copy = defaultdict(list)
weaks_copy_length = defaultdict(list)
weaks_only_length = defaultdict(list)
weaks_loop = defaultdict(list)
weaks_command_exec = defaultdict(list)


MUSTALIAS, MAYALIAS, NOALIAS = 1, 2, 3


class Collector(object):
    """
    Collect all data generate in data flow analysis and analyze them.
    """

    def __init__(self, proj):

        self.support_data_types = ['Vptr', 'Iptr', 'Fptr', 'uArg', 'dArg', 'Aptr', 'Ret', 'Rptr', 'uData', 'sDef', 'Tdata', 'Dptr', 'tmp']

        self.proj = proj

        self.datas = {}

        self.icall_targets = {}
        self.switch_targets = {}

        self.analyzed_functions = set()

        self.state = self.proj.factory.blank_state()
        self.size_bytes = self.proj.arch.bytes
        self.endness = self.proj.arch.memory_endness

        self._initial_datas()



    def _initial_datas(self):

        for data_type in self.support_data_types:
            self.datas[data_type] = defaultdict(list)

    def _is_alias(self, datas1, datas2):
        print(datas1, datas2)
        d1_hashs = [data.expr.ast.__hash__() for data in datas1]
        d2_hashs = [data.expr.ast.__hash__() for data in datas2]
        d1_hashs = set(d1_hashs)
        d2_hashs = set(d2_hashs)

        same_hashs = set()
        for d1 in d1_hashs:
            if d1 in d2_hashs:
                same_hashs.add(d1)

        if len(same_hashs) == len(d1_hashs) and len(same_hashs) == len(d2_hashs):
            return MUSTALIAS
        elif len(same_hashs):
            return MAYALIAS
        else:
            return NOALIAS

    def read_value(self, addr):
        pe = get_mem_permission(addr)
        if pe == 'ro' or pe == 'rw':
            value_ast = self.state.memory.load(addr, self.size_bytes, endness=self.endness)
            if value_ast.op == 'BVV':
                return value_ast.args[0]

    def alias_check(self):
        from dataflow.data_process import ALIAS_SOURCES, ALL_SOURCES
        # print(ALIAS_SOURCES)

        alias_info = {}
        for funcea, datas in self.datas['uData'].items():
            for data in datas:
                aid = data.expr.alias_id
                if aid not in alias_info:
                    alias_info[aid] = []
                alias_info[aid].append(data)

                for sid in data.expr.contain_alias:
                    if sid not in alias_info:
                        alias_info[sid] = []
                    alias_info[sid].append(data)

        for as1, as2 in ALIAS_SOURCES:
            datas1 = alias_info.get(as1)
            datas2 = alias_info.get(as2)

            if datas1 and datas2:
                resalias = self._is_alias(datas1, datas2)
                if resalias == MUSTALIAS:
                    print("(%s %s) is MUSTALIAS" % (ALL_SOURCES[as1], ALL_SOURCES[as2]))

                elif resalias == MAYALIAS:
                    print("(%s %s) is MAYALIAS" % (ALL_SOURCES[as1], ALL_SOURCES[as2]))

                else:
                    print("(%s %s) is NOALIAS" % (ALL_SOURCES[as1], ALL_SOURCES[as2]))

            else:
                print("(%s %s) is NOALIAS" % (ALL_SOURCES[as1], ALL_SOURCES[as2]))

    def parse_function_ptr(self):

        print("\n Start-parse-icall-v1:\n")
        global_fptr_info = {}
        iptr_info = self.datas['Iptr']
        fptr_info = self.datas['Fptr']

        for funcea, fptr_exprs in fptr_info.items():
            for fptr_expr in fptr_exprs:
                base = fptr_expr.expr.base_ptr
                if type(base) is int:
                    if base not in global_fptr_info:
                        global_fptr_info[base] = []

                    global_fptr_info[base].append(fptr_expr)

        for funcea, iptr_exprs in iptr_info.items():
            for iptr_expr in iptr_exprs:
                base = iptr_expr.expr.base_ptr
                if type(base) is int and base in global_fptr_info:
                    fptr_exprs = global_fptr_info[base]
                    self._find_global_icall_target(iptr_expr, fptr_exprs)

                elif type(base) is str:
                    fptr_exprs = fptr_info.get(funcea)
                    if fptr_exprs:
                        self._find_symbol_icall_target(iptr_expr, fptr_exprs)

                # print("icall -> %s" % (iptr_expr))

        for funcea, icall_info in self.icall_targets.items():
            if len(icall_info):
                print("ICALL %x -> %s" % (funcea, icall_info))

            else:
                print("Unlucky, not found icall %x" % (funcea))

    def _find_global_icall_target(self, iptr_expr, fptr_exprs):
        iptr_struct_id = calculate_ast_struct_id(iptr_expr.expr.ast)
        funcea, iptr_src = ICALL_SOURCES.get(iptr_expr.expr.alias_id)
        if iptr_src is None:
            print("The iptr %s not in ICALL_SOURCES!" % (iptr_expr))
            return

        for fptr_expr in fptr_exprs:
            # print(" Icall- %s\n Fptr- %s" % (iptr_expr, fptr_expr))
            struct_id = calculate_ast_struct_id(fptr_expr.expr.ast)
            # print("Struct-ID: %s %s" % (iptr_struct_id, struct_id))
            if struct_id == iptr_struct_id:
                # print("Lucky, found icall %s -> %s" % (iptr_src, fptr_expr.expr.value))
                value_ast = fptr_expr.expr.value
                if value_ast.op == 'BVV':
                    value = value_ast.args[0]
                    self.add_icall_target(funcea, iptr_src, value)

    def _find_symbol_icall_target(self, iptr_expr, fptr_exprs):
        pass




    def parse_simple_function_ptr(self, proj):

        iptr_info = self.datas['Iptr']
        state = proj.factory.blank_state()
        size_bytes = proj.arch.bytes
        endness = proj.arch.memory_endness

        for funcea, iptr_exprs in iptr_info.items():
            for iptr_expr in iptr_exprs:
                print("Icall: %x has %s, with %s" % (funcea, iptr_expr, iptr_expr.expr.constraints))
                base_ptr = iptr_expr.expr.base_ptr
                ast = iptr_expr.expr.ast

                funcea, iptr_src = ICALL_SOURCES.get(iptr_expr.expr.alias_id)
                print("   -source: %x %x" % (funcea, iptr_src))

                if iptr_src in [0x2120c, 0x2115c]:
                    iptr_expr.expr.constraints.append(0xa590c)

                if ast.op == 'BVV' or type(base_ptr) is int and get_mem_permission(base_ptr) in ['ro', 'rw']:
                    targets = self.read_data_by_expr(iptr_expr, state, size_bytes, endness, mode='icall')
                    for target in targets:
                        func_name = self.get_extern_function_name(target)
                        if func_name:
                            self.add_icall_target(funcea, iptr_src, func_name)
                        else:
                            self.add_icall_target(funcea, iptr_src, target)

        for funcea, icall_info in self.icall_targets.items():
            if len(icall_info):
                print("ICALL %x -> %s" % (funcea, icall_info))

    def parse_switch_targets(self, call_graph, proj):
        """
        Resolve the switch targets.
        """
        iptr_info = self.datas['Iptr']
        state = proj.factory.blank_state()
        size_bytes = proj.arch.bytes
        endness = proj.arch.memory_endness

        for funcea, iptr_exprs in iptr_info.items():
            function = call_graph.get_function_by_addr(funcea)
            if function is None:
                print("The function %x not in call graph." % (funcea))
                continue

            for iptr_expr in iptr_exprs:
                print("Switch-jmp: %x has %s, with %s" % (funcea, iptr_expr, iptr_expr.expr.constraints))
                base_ptr = iptr_expr.expr.base_ptr
                ast = iptr_expr.expr.ast

                funcea, iptr_src = ICALL_SOURCES.get(iptr_expr.expr.alias_id)
                print("   -source: %x %x" % (funcea, iptr_src))

                if ast.op == 'BVV' or type(base_ptr) is int:
                    targets = self.read_data_by_expr(iptr_expr, state, size_bytes, endness, mode='switch')
                    for target in targets:
                        if target in function.cfg._nodes:
                            self.add_switch_target(funcea, iptr_src, target)

        for funcea, switch_info in self.switch_targets.items():
            for bb_addr, targets in switch_info.items():
                for target in targets:
                    print("Switch %x : %x -> %x" % (funcea, bb_addr, target))

    def read_data_by_expr(self, trace_expr, state, size_bytes, endness, mode=None):

        def get_sim_action_info(trace_expr):
            sim_action_info = {}
            sim_actions = trace_expr.expr.sim_actions
            for i, sim_action in sim_actions.items():
                # print("degu- %s %s" % (sim_action, sim_action.action_data.__hash__()))
                action_id = sim_action.action_data.__hash__()
                sim_action_info[action_id] = sim_action.var_type
            return sim_action_info

        # print(" ...start parse icall-expr")
        data_ast = trace_expr.expr.ast
        if data_ast.op == 'BVV' and data_ast.args[0]:
            read_values = set()
            read_values.add(data_ast.args[0])

        # elif mode == 'icall' and data_ast.op == 'Load':
        elif mode == 'icall':
            constraints = trace_expr.expr.constraints
            sim_action_info = get_sim_action_info(trace_expr)
            read_values = read_data_with_load(state, data_ast, size_bytes, endness, constraints, sim_action_info)

        elif mode == 'switch':
            constraints = trace_expr.expr.constraints
            sim_action_info = get_sim_action_info(trace_expr)
            read_values = calculate_switch_targets(state, data_ast, size_bytes, endness, constraints, sim_action_info)

        else:
            read_values = set()

        # print("read_values: %s" % (read_values))
        for value in read_values:
            print("i -> 0x%x" % (value))
        return read_values

    def add_icall_target(self, funcea, loc, target):
        if funcea not in self.icall_targets:
            self.icall_targets[funcea] = {}

        if loc not in self.icall_targets[funcea]:
            self.icall_targets[funcea][loc] = []

        if target not in self.icall_targets[funcea][loc]:
            self.icall_targets[funcea][loc].append(target)

    def add_switch_target(self, funcea, loc, target):
        if funcea not in self.switch_targets:
            self.switch_targets[funcea] = {}

        if loc not in self.switch_targets[funcea]:
            self.switch_targets[funcea][loc] = []

        if target not in self.switch_targets[funcea][loc]:
            self.switch_targets[funcea][loc].append(target)

    def collect_weaks(self, block, taint_expr):
        """
        Check taint security and collect some vulnerabilities.
        """
        taint_ast = taint_expr.expr.ast
        taint_loc = taint_expr.expr.taint_loc
        constraints = taint_expr.expr.constraints

        if (taint_ast.op == 'BVV' and
                get_scope(taint_ast.args[0]) == 'stack' and taint_loc):
            # print("collect-weak: %s %x" % (taint_expr, taint_expr.expr.flag))
            taint_expr.expr.taint_loc = None
            # if len(constraints) == 0 or taint_expr.expr.flag & 0x1000:
            #     stack_addr = taint_ast.args[0]
            #     stack_offset = 0x7fffffff - stack_addr
            #     if taint_loc not in self.weaks:
            #         self.weaks[taint_loc] = set()
            #     self.weaks[taint_loc].add(stack_offset)

            if taint_expr.expr.flag & 0x1000:
                if taint_expr not in weaks_copy_length[taint_loc]:
                    print("Add-weak-copy-and-length: %s" % (taint_expr))
                    weaks_copy_length[taint_loc].append(taint_expr)

            elif taint_expr not in weaks_copy[taint_loc]:
                print("Add-weak-copy: %s" % (taint_expr))
                weaks_copy[taint_loc].append(taint_expr)

    def get_extern_function_name(self, addr):
        """
        Get extern lib function name.
        """
        if self.proj.is_hooked(addr):
            proc = self.proj._sim_procedures[addr]
            name = proc.display_name
            print("%x with %s" % (addr, name))
            return name

    def get_sim_action_info(self, trace_expr):
        sim_action_info = {}
        sim_actions = trace_expr.expr.sim_actions
        for i, sim_action in sim_actions.items():
            action_id = sim_action.action_data.__hash__()
            sim_action_info[action_id] = sim_action.var_type
        return sim_action_info

    def parse_icall_targets_v1(self):
        """
        Parse icall_expr and calculate its call target.
        """
        iptr_info = self.datas['Iptr']

        stores_info = defaultdict(list)
        self.get_stores_info(stores_info, 'Vptr')
        self.get_stores_info(stores_info, 'Fptr')

        for store_id, values in stores_info.items():
            print("store-info: %s %s" % (store_id, values))

        for addr, iptr_exprs in iptr_info.items():
            print("\n %x has %s\n" % (addr, iptr_exprs))
            for iptr_expr in iptr_exprs:
                print("\nIcall: %x has %s, with %s" % (addr, iptr_expr, iptr_expr.expr.constraints))
                data_ast = iptr_expr.expr.ast
                new_asts = self.replace_load_value(data_ast, stores_info)
                print("simplify_load get: %s" % (new_asts))

                funcea, iptr_src = ICALL_SOURCES.get(iptr_expr.expr.alias_id)
                print("   -source: %x %x" % (funcea, iptr_src))

                sim_action_info = self.get_sim_action_info(iptr_expr)
                constraints = iptr_expr.expr.constraints

                if iptr_src in [0x2120c, 0x2115c]:
                    iptr_expr.expr.constraints.append(0xa590c)

                targets = set()
                for iptr in new_asts:
                    targets |= self.calculate_icall_targets(iptr, sim_action_info, constraints)

                for target in targets:
                    print("   i -> 0x%x" % (target))
                    func_name = self.get_extern_function_name(target)
                    if func_name:
                        self.add_icall_target(funcea, iptr_src, func_name)
                    else:
                        self.add_icall_target(funcea, iptr_src, target)

    def calculate_icall_targets(self, iptr, sim_action_info, constraints):
        values = set()

        if iptr.op == 'BVV':
            value = iptr.args[0]
            if is_code_region(value):
                values.add(value)

        elif iptr.op == 'Load':
            addr = iptr.args[0]
            if addr.op == 'BVV':
                addr_value = addr.args[0]
                value = self.read_value(addr_value)
                if value and (is_code_region(value) or is_extern_region(value)):
                    values.add(value)

            elif addr.op in offset_ops and not_contain_ls(addr):
                if 'i' in addr.variables:
                    read_values = self.read_recursive_data(addr, constraints=constraints, read_type='func')
                    if read_values:
                        values |= read_values

                else:
                    new_addr = claripy.simplify(addr)
                    if new_addr.op == 'BVV':
                        addr_value = new_addr.args[0]
                        value = self.read_value(addr_value)
                        if value and is_code_region(value):
                            values.add(value)

        return values

    def get_stores_info(self, stores_info, data_type):
        """
        Get the pointer sotre info, e.g. store(bss_addr) == dptr
        """
        dptr_info = self.datas[data_type]
        for funcea, dptr_exprs in dptr_info.items():
            for dptr_expr in dptr_exprs:
                print("Sotre-func-ptr: %s" % (dptr_expr))
                value = dptr_expr.expr.value
                # if value.op != 'BVV':
                #     continue
                data_ast = dptr_expr.expr.ast
                struct_id = calculate_ast_struct_id(data_ast)
                # value = value.args[0]
                stores_info[struct_id].append(value)
                # if value not in stores_info[struct_id]:
                #     stores_info[struct_id].append(value)

    def replace_one_load_value(self, data_ast, stores_info):

        new_datas = []
        if data_ast.op == 'Load':
            ld_id = calculate_ast_struct_id(data_ast)
            if ld_id in stores_info:
                for value in stores_info[ld_id]:
                    # value_ast = BVV(value, data_ast.size())
                    new_data = data_ast.replace(data_ast, value)
                    new_datas.append(new_data)
                return new_datas

        for child_ast in data_ast.recursive_children_asts:
            if child_ast.op != 'Load':
                continue

            ld_addr = child_ast.args[0]
            ld_id = calculate_ast_struct_id(child_ast)

            if ld_id in stores_info:
                for value in stores_info[ld_id]:
                    # value_ast = BVV(value, child_ast.size())
                    new_data = data_ast.replace(child_ast, value)
                    new_datas.append(new_data)
                return new_datas

            elif ld_addr.op == 'BVV' and get_mem_permission(ld_addr.args[0]) in ['ro', 'rw']:
                addr = ld_addr.args[0]
                value = self.state.memory.load(addr, self.size_bytes, endness=self.endness)
                if value.op == 'BVV' and value.args[0]:
                    new_data = data_ast.replace(child_ast, value)
                    new_datas.append(new_data)
                    return new_datas

            elif ld_addr.op in offset_ops and not_contain_ls(ld_addr) and 'i' in ld_addr.variables:
                child_ast_id = child_ast.__hash__()
                if child_ast_id in sim_action_info:
                    child_var_type = sim_action_info[child_ast_id]
                else:
                    child_var_type = get_no_ls_ast_type(ld_addr)
                # print("child_ast: %s %s %s" % (child_ast, child_ast.__hash__(), child_var_type))
                read_values = read_recursive_data(ld_addr, read_type='data', end_flag=0, var_type=child_var_type)
                for value in read_values:
                    value_ast = BVV(value, child_ast.size())
                    new_data = data_ast.replace(child_ast, value_ast)
                    new_datas.append(new_data)
                return new_datas

        return new_datas

    def replace_load_value(self, data_ast, stores_info):
        """
        Simplify the data/rodata/bss load expr with value.
        """
        new_asts = []
        data_worklist = [data_ast]
        while data_worklist:
            data_ast = data_worklist.pop()
            tmp_asts = self.replace_one_load_value(data_ast, stores_info)
            if tmp_asts:
                data_worklist.extend(tmp_asts)

            else:
                new_asts.append(data_ast)

        return new_asts

    def read_recursive_data(self, addr, constraints=None, read_type=None, end_flag=None, var_type=None):
        """
        Recurisive parse load data by replace the symbol 'i'.
        """
        read_values = set()
        i = BVS('i')
        max_value = constraints[0] if constraints else None

        for o in range(Max_i):
            offset = BVV(o)
            new_addr = addr.replace(i, offset)
            new_addr = claripy.simplify(new_addr)
            if new_addr.op == 'BVV' and get_mem_permission(new_addr.args[0]) in ['rw', 'ro']:
                addr_value = new_addr.args[0]
                if max_value and addr_value > max_value:
                    break

                value_ast = self.state.memory.load(addr_value, self.size_bytes, endness=self.endness)
                # print("read_recursive: addr %s, value: %s" % (new_addr, value_ast))
                if value_ast.op != 'BVV':
                    continue

                value = value_ast.args[0]
                if value and value > 0:
                    if read_type == 'func' and is_code_region(value):
                        read_values.add(value)
                        # print("  -- %x : %x" % (addr_value, value))

                    elif read_type == 'data' and is_data_region(value):
                        read_values.add(value)
                        # print("  -- %x : %x" % (addr_value, value))

                    else:
                        break

                elif value is None or value == end_flag:
                    break

                # elif value == 0:
                #     print("  -- %x : %x" % (addr_value, value))

            elif var_type and var_type != 'ptr':
                read_values.add(o)

            else:
                break

        return read_values
