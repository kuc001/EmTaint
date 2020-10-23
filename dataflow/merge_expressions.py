#!/usr/bin/env python

from .parse_ast import *


ls_op = ['Load', 'Store']
base_op = ['BVV', 'BVS']


def merge_simlilar_exprs_v1(trace_exprs):
    """
    Merge simlilar exprs and reduce trace exprs.
    """
    summary_exprs = []
    same_struct_exprs = defaultdict(list)
    contain_alias_ids = defaultdict(set)
    similar_struct_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        # print("\nmerge: %s" % (trace_expr))
        ast = trace_expr.expr.ast
        struct_id = calculate_ast_struct_id(ast)
        # print("struct id: %s" % (struct_id))

        alias_id = trace_expr.expr.alias_id
        same_struct_exprs[struct_id].append(trace_expr)
        contain_alias_ids[struct_id].add(alias_id)

    # DEBUG
    # for leaf_id, sim_structure_exprs in same_struct_exprs.items():
    #     print("\nkai leaf id: %s %d" % (leaf_id, len(sim_structure_exprs)))
    #     for e in sim_structure_exprs:
    #         print(e)

    for leaf_id, sim_structure_exprs in same_struct_exprs.items():

        struct_contain_ids = contain_alias_ids[leaf_id]
        # print("same: %s\n contain: %s" % (leaf_id, struct_contain_ids))

        if len(sim_structure_exprs) > 1:
            summary_expr = summary_similar_structure_v1(sim_structure_exprs)
            summary_exprs.append(summary_expr)
        elif len(sim_structure_exprs) == 1:
            summary_exprs.append(sim_structure_exprs[0])

    return summary_exprs


def merge_simlilar_exprs_v2(trace_exprs):
    """
    Merge simlilar exprs and reduce trace exprs.
    """
    summary_exprs = []
    same_struct_exprs = defaultdict(list)
    contain_alias_ids = defaultdict(set)
    similar_struct_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        # print("\nmerge: %s" % (trace_expr))
        ast = trace_expr.expr.ast
        struct_id = calculate_ast_struct_id(ast)
        # print("struct id: %s" % (struct_id))
        alias_id = trace_expr.expr.alias_id

        value = trace_expr.expr.value
        if value is not None:
            struct_id += value.__hash__()

        same_struct_exprs[struct_id].append(trace_expr)
        contain_alias_ids[struct_id].add(alias_id)

    for leaf_id, sim_structure_exprs in same_struct_exprs.items():

        struct_contain_ids = contain_alias_ids[leaf_id]
        # for sim_expr in sim_structure_exprs:
        #     print("same: %s, %s" % (leaf_id, sim_expr))

        if len(sim_structure_exprs) > 1:
            summary_expr = summary_similar_structure_v2(sim_structure_exprs)
            summary_exprs.append(summary_expr)
        elif len(sim_structure_exprs) == 1:
            summary_exprs.append(sim_structure_exprs[0])

    return summary_exprs


def _merge_exprs(self, trace_exprs):
    """
    merge the similar exprs and reduce the numbers.
    """

    summary_exprs = []
    same_struct_exprs = defaultdict(list)
    contain_alias_ids = defaultdict(set)
    similar_struct_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        # print("\nmerge: %s" % (trace_expr))

        ast = trace_expr.expr.ast
        struct_id = calculate_ast_struct_id(ast)

        # leaf_id = calculate_ast_leaf_id(ast)

        # print("struct id: %s" % (struct_id))
        # print("leaf id: %s" % (leaf_id))

        alias_id = trace_expr.expr.alias_id

        same_struct_exprs[struct_id].append(trace_expr)
        contain_alias_ids[struct_id].add(alias_id)

        # similar_struct_exprs[struct_id].append(trace_expr)

    # DEBUG
    # for leaf_id in same_struct_exprs.keys():
    #     print("same leaf id: %s" % (leaf_id))

    # for struct_id in similar_struct_exprs.keys():
    #     print("same struct id: %s" % (struct_id))

    # for leaf_id, sim_structure_exprs in same_struct_exprs.items():
    #     print("\nkai leaf id: %s %d" % (leaf_id, len(sim_structure_exprs)))

    #     for e in sim_structure_exprs:
    #         print(e)

    # for struct_id, sim_structure_exprs in similar_struct_exprs.items():
    #     print("\nkai struct id: %s %d" % (struct_id, len(sim_structure_exprs)))

    #     for e in sim_structure_exprs:
    #         print(e)

    repeat_exprs_ids = []
    summary_info = {}

    for leaf_id, sim_structure_exprs in same_struct_exprs.items():

        struct_contain_ids = contain_alias_ids[leaf_id]
        # print("same: %s\n contain: %s" % (leaf_id, struct_contain_ids))

        summary_asts = self._summary_similar_structure(sim_structure_exprs)
        # print("getnewast: %s" % (summary_asts))

        if len(summary_asts):
            repeat_exprs_ids.append(leaf_id)
            summary_info[leaf_id] = summary_asts

    # print("could remove: %s" % (repeat_exprs_ids))

    for remove_id in repeat_exprs_ids:
        remove_exprs = same_struct_exprs[remove_id]

        for r_expr in remove_exprs:
            trace_exprs.remove(r_expr)

    for leaf_id, summary_asts in summary_info.items():

        struct_contain_ids = contain_alias_ids[leaf_id]
        new_trace_exprs = self._create_summary_expr(summary_asts, struct_contain_ids)

        for new_expr in new_trace_exprs:
            trace_exprs.append(new_expr)

    for leaf_id, sim_structure_exprs in same_struct_exprs.items():

        if leaf_id in repeat_exprs_ids:
            continue

        self._remove_repeat_exprs(sim_structure_exprs, trace_exprs)

def _summary_exprs(self, trace_exprs):
    """
    In loop, the exprs maybe similar. summary the similar exprs and reduce the numbers.
    """

    summary_exprs = []
    same_id_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        # print("summary: %s" % (trace_expr))

        source = trace_expr.expr.source
        alias_id = trace_expr.expr.alias_id
        # print("source: %s, id: %s" % (source, alias_id))

        same_id_exprs[alias_id].append(trace_expr)

    for alias_id, sim_exprs in same_id_exprs.items():
        same_exprs = {}
        repeat_exprs_ids = []
        all_summary_asts = []

        if len(sim_exprs) >= 2:
            for sim_expr in sim_exprs:

                ast = sim_expr.expr.ast
                leaf_id = calculate_ast_leaf_id(ast)
                # print("leaf id: %s" % (leaf_id))

                if leaf_id not in same_exprs:
                    same_exprs[leaf_id] = []

                same_exprs[leaf_id].append(sim_expr)

        for leaf_id, sim_structure_exprs in same_exprs.items():

            # print("same: %s" % (leaf_id))
            summary_asts = self._summary_similar_structure(sim_structure_exprs)
            # print("getnewast: %s" % (summary_asts))

            if len(summary_asts):
                repeat_exprs_ids.append(leaf_id)
                all_summary_asts.extend(summary_asts)

        # print("could remove: %s" % (repeat_exprs_ids))

        for remove_id in repeat_exprs_ids:
            remove_exprs = same_exprs[remove_id]

            for r_expr in remove_exprs:
                trace_exprs.remove(r_expr)

        if len(all_summary_asts):
            original_expr = sim_exprs[0]

            new_exprs = self._create_summary_expr(original_expr, all_summary_asts)

            for new_expr in new_exprs:
                trace_exprs.append(new_expr)

def simple_chose_expr(trace_expr):
    data_type = trace_expr.expr.data_type
    simplify_simple_expr(trace_expr)
    trace_ast = trace_expr.expr.ast
    if data_type == 'Tdata':
        if trace_ast.op == 'BVS' or trace_ast.op == 'BVV':
            return True

        elif is_str_pointer(trace_ast):
            new_ast = trace_ast.args[0]
            trace_expr.expr.ast = new_ast
            return True

    for var in trace_ast.variables:
        if 'o' in var or 'i' in var:
            return True
    return False

def summary_similar_structure_v1(sim_structure_exprs):

    result_expr = None
    for index, sim_expr in enumerate(sim_structure_exprs):
        if simple_chose_expr(sim_expr):
            result_expr = sim_expr
            break

    if result_expr is None:
        result_expr = sim_structure_exprs[0]

    return result_expr


def summary_similar_structure_v2(sim_structure_exprs):

    result_expr = None
    for index, sim_expr in enumerate(sim_structure_exprs):
        ast = sim_expr.expr.ast
        if not_contain_ls(ast):
            new_ast = claripy.simplify(ast)
            if new_ast.op == 'BVS':
                sim_expr.expr.ast = new_ast
                result_expr = sim_expr
                break

    if result_expr is None:
        result_expr = sim_structure_exprs[0]

    return result_expr


def summary_similar_structure(sim_structure_exprs):

    arch_bits = self._binary_parser.arch_bits
    simplify_ops = ['__add__', '__sub__']
    summary_asts = []

    with_same_base = {}
    hash_to_ast = {}
    for index, expr in enumerate(sim_structure_exprs):

        # ast_len = get_ast_len(ast)
        # print("%d %s\n with len: %d\n" % (index, ast, ast_len))
        # continue

        ast = expr.expr.ast

        simplify_asts = []
        get_simplify_ast(ast, simplify_asts)
        # print("ast: %s" % (ast))
        # print("could simplify: %s" % (simplify_asts))

        base_hash = 0
        bases_and_incs = []
        for sim_ast in simplify_asts:
            inc_info = get_inc_data_info(sim_ast)
            # print("inc info: %s" % (inc_info))

            base_asts = inc_info['base']
            mul_inc = inc_info['mul_inc']
            inc_num = inc_info['inc_num']

            inc_flag = False
            if len(mul_inc) > 0:
                # print("with inc :%s" % (mul_inc))
                inc_flag = True

            if len(inc_num):
                # print("with inc: %s" % (inc_num))

                maybe_incs = []
                for inc, num in inc_num.items():
                    if num >= 3:
                        maybe_incs.append(inc)
                        inc_flag = True

                for inc in maybe_incs:
                    mul_inc.add(inc)
                    inc_num.pop(inc)

            if len(base_asts) == 0:
                sym_bases = []
                for inc_sym, num in inc_num.items():
                    if type(inc_sym) is str and num == 1:
                        sym_bases.append(inc_sym)

                    elif type(inc_sym) is int and num == 1:
                        con_type = get_mem_permission(inc_sym)
                        if con_type in ['ro','rw', 'bss']:
                            sym_bases.append(inc_sym)

                for sym_b in sym_bases:
                    if type(sym_b) is str:
                        sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                    elif type(sym_b) is int:
                        sym_ast = claripy.BVV(sym_b, arch_bits)

                    base_asts.append(sym_ast)
                    inc_num.pop(sym_b)

            if inc_flag:
                for base_ast in base_asts:
                    base_hash += base_ast.__hash__()

                info = [sim_ast, base_asts, mul_inc, inc_num]
                bases_and_incs.append(info)

        if len(bases_and_incs):
            if base_hash in with_same_base:
                old_bases_and_incs = with_same_base[base_hash]

                if len(bases_and_incs) > len(old_bases_and_incs):
                    with_same_base[base_hash] = bases_and_incs
                    hash_to_ast[base_hash] = ast

            else:
                with_same_base[base_hash] = bases_and_incs
                hash_to_ast[base_hash] = ast

    all_syms = []
    remove_hash = []
    for b_hash, bases_and_incs in with_same_base.items():
        # print("\n%s containt %s" % (b_hash, bases_and_incs))
        # print("ast %s" % (hash_to_ast[b_hash]))

        inc_syms = set()
        for info in bases_and_incs:
            mul_inc, inc_num = info[2], info[3]
            for inc_sym in mul_inc:
                inc_syms.add(inc_sym)

            for inc_sym in inc_num.keys():
                inc_syms.add(inc_sym)

        inc_syms = tuple(inc_syms)
        if inc_syms not in all_syms:
            all_syms.append(inc_syms)

        else:
            remove_hash.append(b_hash)

    for r_hash in remove_hash:
        with_same_base.pop(r_hash)

    # print("test: %s\n" % (with_same_base))

    for b_hash, bases_and_incs in with_same_base.items():
        original_ast = hash_to_ast[b_hash]

        new_ast = self._generate_summary_ast(original_ast, bases_and_incs)
        summary_asts.append(new_ast)


    return summary_asts

def _generate_summary_ast(self, original_ast, simplify_ast_infos):

    new_ast = original_ast

    for simplify_ast_info in simplify_ast_infos:

        summary_ast = self._get_the_summary_ast(original_ast, simplify_ast_info)

        sim_ast = simplify_ast_info[0]

        new_ast = new_ast.replace(sim_ast, summary_ast)

    return new_ast

def _get_the_summary_ast(self, original_ast, simplify_ast_info):

    # print("old ast: %s" % (original_ast))

    arch_bits = self._binary_parser.arch_bits

    sim_bases = simplify_ast_info[1]

    summary_ast = 0
    for base in sim_bases:

        all_bash_hash, bases_and_incs = self._get_ast_base_and_inc_info(base)

        # print("Get hash: %s\ninfo: %s" % (all_bash_hash, bases_and_incs))

        if len(bases_and_incs) == 0:

            summary_ast += base

        else:
            new_base = base
            for sim_ast_info in bases_and_incs:
                base_summ_ast = self._get_the_summary_ast(base, sim_ast_info)

                base_sim_ast = sim_ast_info[0]
                new_base = new_base.replace(base_sim_ast, base_summ_ast)

            summary_ast += new_base

    mul_inc, inc_num = simplify_ast_info[2], simplify_ast_info[3]

    if len(mul_inc):
        i = claripy.BVS('i', arch_bits, explicit_name=True)

        for inc_o in mul_inc:
            if type(inc_o) is int:
                inc_ast = claripy.BVV(inc_o, arch_bits)

            elif type(inc_o) is str:
                inc_ast = claripy.BVS(inc_o, arch_bits, explicit_name=True)

            else:
                continue

            summary_ast += i * inc_ast

    for inc_o, num in inc_num.items():
        if type(inc_o) is int:
            inc_ast = claripy.BVV(inc_o, arch_bits)

        elif type(inc_o) is str:
            inc_ast = claripy.BVS(inc_o, arch_bits, explicit_name=True)

        else:
            continue

        summary_ast += inc_ast * num

    # print("summary ast: %s" % (summary_ast))
    return summary_ast

def _get_ast_base_and_inc_info(self, ast):

    simplify_asts = []
    arch_bits = self._binary_parser.arch_bits
    get_simplify_ast(ast, simplify_asts)

    base_hash = 0
    bases_and_incs = []
    for sim_ast in simplify_asts:
        inc_info = get_inc_data_info(sim_ast)

        base_asts = inc_info['base']
        mul_inc = inc_info['mul_inc']
        inc_num = inc_info['inc_num']

        inc_flag = False
        if len(mul_inc) > 0:
            inc_flag = True

        if len(inc_num):
            maybe_incs = []
            for inc, num in inc_num.items():
                if num >= 3:
                    maybe_incs.append(inc)
                    inc_flag = True

            for inc in maybe_incs:
                mul_inc.add(inc)
                inc_num.pop(inc)

        if len(base_asts) == 0:
            sym_bases = []
            for inc_sym, num in inc_num.items():
                if type(inc_sym) is str and num == 1:
                    sym_bases.append(inc_sym)

                elif type(inc_sym) is int and num == 1:
                    con_type = get_mem_permission(inc_sym)
                    if con_type in ['ro', 'rw', 'bss']:
                        sym_bases.append(inc_sym)

            for sym_b in sym_bases:
                if type(sym_b) is str:
                    sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                elif type(sym_b) is int:
                    sym_ast = claripy.BVV(sym_b, arch_bits)

                base_asts.append(sym_ast)
                inc_num.pop(sym_b)

        if inc_flag:
            for base_ast in base_asts:
                base_hash += base_ast.__hash__()

            info = [sim_ast, base_asts, mul_inc, inc_num]
            bases_and_incs.append(info)

    return base_hash, bases_and_incs

def _create_summary_expr(self, summary_asts, struct_contain_ids):

    new_trace_exprs = []
    for summary_ast in summary_asts:

        new_expr = VarExpr(summary_ast, pattern='OB', trace_dir='B', data_type='Iptr')
        new_expr.get_trace_variable()
        new_expr.initial_sims()

        alias_id = 0
        for a_id in struct_contain_ids:
            new_expr.contain_alias.add(a_id)
            alias_id += a_id

        new_expr.alias_id = alias_id

        new_trace_expr = TraceExpr(new_expr)

        new_trace_exprs.append(new_trace_expr)

    return new_trace_exprs

def _reduce_same_exprs(self, same_exprs):

    simplify_ops = ['__add__', '__sub__']
    summary_exprs = []

    for leaf_id, same_asts in same_exprs.items():
        # print("same: %s" % (leaf_id))

        with_same_base = {}
        hash_to_ast = {}
        for ast in same_asts:

            # simplify_asts = get_simplify_ast(ast)
            simplify_asts = []
            get_simplify_ast(ast, simplify_asts)
            # print("ast: %s" % (ast))
            # print("could simplify: %s" % (simplify_asts))

            base_hash = 0
            bases_and_incs = {}
            for sim_ast in simplify_asts:
                inc_info = get_inc_data_info(sim_ast)
                # print("inc info: %s" % (inc_info))

                base_asts = inc_info['base']
                mul_inc = inc_info['mul_inc']
                inc_num = inc_info['inc_num']

                inc_flag = False
                if len(mul_inc) > 0:
                    # print("with inc :%s" % (mul_inc))
                    inc_flag = True

                if len(inc_num):
                    # print("with inc: %s" % (inc_num))

                    maybe_incs = []
                    for inc, num in inc_num.items():
                        if num >= 3:
                            maybe_incs.append(inc)
                            inc_flag = True

                    for inc in maybe_incs:
                        mul_inc.add(inc)
                        inc_num.pop(inc)

                if len(base_asts) == 0:
                    sym_bases = []
                    for inc_sym, num in inc_num.items():
                        if type(inc_sym) is str and num == 1:
                            sym_bases.append(inc_sym)

                        elif type(inc_sym) is int and num == 1:
                            con_type = get_mem_permission(inc_sym)
                            if con_type in ['ro', 'rw', 'bss']:
                                sym_bases.append(inc_sym)

                    for sym_b in sym_bases:
                        if type(sym_b) is str:
                            sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                        elif type(sym_b) is int:
                            sym_ast = claripy.BVV(sym_b, arch_bits)

                        base_asts.append(sym_ast)
                        inc_num.pop(sym_b)

                if inc_flag:
                    for base_ast in base_asts:
                        base_hash += base_ast.__hash__()

                    info = [sim_ast, base_asts, mul_inc, inc_num]
                    sim_ast_hash = sim_ast.__hash__()
                    bases_and_incs[sim_ast_hash] = info

            if len(bases_and_incs):
                if base_hash in with_same_base:
                    old_bases_and_incs = with_same_base[base_hash]

                    if len(bases_and_incs) > len(old_bases_and_incs):
                        with_same_base[base_hash] = bases_and_incs
                        hash_to_ast[base_hash] = ast

                else:
                    with_same_base[base_hash] = bases_and_incs
                    hash_to_ast[base_hash] = ast

                # simplifiy_ast_with_base.append([sim_ast, base_asts])

            # TODO
            # if len(simplify_asts) >= 2:
            #     self._find_embedded_base(simplify_asts)

        # for b_hash, info in with_same_base.items():
        #     print("\n%s containt %s" % (b_hash, info))
        #     print("ast %s" % (hash_to_ast[b_hash]))


def _summary_same_base(self, same_bases, hash_to_ast):

    arch_bits = self._binary_parser.arch_bits

    for b_hash, ast_infos in same_bases.items():
        original_ast = hash_to_ast[b_hash]

        # if len(ast_infos) >= 2:
        #     print("There are two or more ast could be simplified!")

        base_with_hash = {}
        sim_ast_hash = ast_infos.keys()
        # print("Contain hash: %s" % (sim_ast_hash))

        for ast_info in ast_infos.values():
            bases = ast_info[1]

            for base in bases:
                b_hash = base.__hash__()
                base_with_hash[b_hash] = base

        for ast_info in ast_infos.values():
            simplify_ast = ast_info[0]
            bases = ast_info[1]
            mul_inc = ast_info[2]
            inc_num = ast_info[3]

            # print("simplify_ast: %s" % (simplify_ast))
            # print("bases: %s, mul_inc: %s, inc_num: %s" % (bases, mul_inc, inc_num))

            self._get_the_summary_ast(bases, base_with_hash, ast_infos)

        # simplify_ast = bases + i*mul_inc + inc_num


def _find_embedded_base(self, simplify_asts):

    pass
    # print("\n")
    # for sim_ast in simplify_asts:
    #     print("sim: %s" % (sim_ast))


def simplify_exprs_v1(trace_exprs):
    """
    Simplify exprs version-1:
        replace load(xxx) * value with 'i * value'
    """
    new_exprs = []
    for trace_expr in trace_exprs:
        new_expr = replace_load_int_var(trace_expr)
        # print("\nold-expr: %s \nnew-expr: %s" % (trace_expr, new_expr))
        new_exprs.append(new_expr)
    return new_exprs


def replace_load_int_var(trace_expr):
    """
    replace load(xxx) * value with 'i * value'
    """
    data_ast = trace_expr.expr.ast
    for child_ast in data_ast.recursive_children_asts:
        if 'mul' in child_ast.op:
            op1, op2 = child_ast.args
            # print("mul- %s" % child_ast)
            if op1.op == 'Load' and op2.op == 'BVV':
                iast = BVS('i', op1.size())
                new_ast = data_ast.replace(op1, iast)
                new_expr = trace_expr.replace(op1, iast)
                # print("new- %s" % (new_ast))
                return replace_load_int_var(new_expr)
    return trace_expr

def merge_recurisive_exprs(trace_exprs, min_level=0):
    """
    Merge the recurisive exprs.
    """
    # print("Start-merge-recurisive!")
    summary_exprs = []
    same_struct_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        ast = trace_expr.expr.ast
        struct_id, recur_level = calculate_recurisive_id(ast)
        # print("ooo-> %s %s %s" % (trace_expr, struct_id, recur_level))

        same_struct_exprs[struct_id].append((recur_level, trace_expr))

    for struct_id, sim_struct_info in same_struct_exprs.items():
        if len(sim_struct_info) == 1:
            summary_exprs.append(sim_struct_info[0][1])
            continue
        elif len(sim_struct_info) == 0:
            continue

        index = 20
        choose_expr = None
        for recur_level, sim_expr in sim_struct_info:
            if recur_level < index:
                choose_expr = sim_expr
                index = recur_level

            if recur_level <= min_level:
                summary_exprs.append(sim_expr)

        if choose_expr is not None:
            summary_exprs.append(choose_expr)

    # for summary_expr in summary_exprs:
    #     print("choose-expr: %s" % (summary_expr))

    return summary_exprs

def dedup_exprs_v1(trace_exprs):
    new_exprs = []
    choose_ids = set()

    for trace_expr in trace_exprs:
        _id = hash((trace_expr.expr.ast.__hash__(), trace_expr.expr.invariant_loc))
        if _id in choose_ids:
            continue
        choose_ids.add(_id)
        new_exprs.append(trace_expr)
    return new_exprs

def merge_simlilar_exprs_v3(trace_exprs):
    """
    Merge simlilar exprs and reduce trace exprs.
    """
    summary_exprs = []
    same_struct_exprs = defaultdict(list)
    contain_alias_ids = defaultdict(set)
    similar_struct_exprs = defaultdict(list)

    for trace_expr in trace_exprs:
        # print("\nmerge: %s" % (trace_expr))
        if trace_expr.expr.data_type == 'Iptr':
            summary_exprs.append(trace_expr)
            continue
        ast = trace_expr.expr.ast
        value = trace_expr.expr.value
        struct_id = calculate_ast_struct_id(ast)
        if value is not None:
            struct_id += value.__hash__()
        # print("struct id: %s" % (struct_id))

        alias_id = trace_expr.expr.alias_id
        same_struct_exprs[struct_id].append(trace_expr)
        contain_alias_ids[struct_id].add(alias_id)

    for leaf_id, sim_structure_exprs in same_struct_exprs.items():

        struct_contain_ids = contain_alias_ids[leaf_id]
        # print("same: %s\n contain: %s" % (leaf_id, struct_contain_ids))

        if len(sim_structure_exprs) > 1:
            summary_expr = summary_similar_structure_v1(sim_structure_exprs)
            summary_exprs.append(summary_expr)
        elif len(sim_structure_exprs) == 1:
            summary_exprs.append(sim_structure_exprs[0])

    return summary_exprs
