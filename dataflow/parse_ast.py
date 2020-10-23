#!/usr/bin/env python

import re
import claripy
from collections import defaultdict
from dataflow.global_config import *

import logging
l = logging.getLogger("parse_ast")
l.setLevel('INFO')

Taint_Offset = 0x64
STACK_MIN, STACK_MAX = (0x6fffffff, 0x8000ffff)

Max_i = 0x1000
Max_o = 50

struct_component = [0x3, 0x5, 0x7, 0x11, 0x13, 0x17, 0x19, 0x23, 0x29, 0x31, 37, 41, 43, 47]
max_struct_level = len(struct_component)


def BVS(name, size=None):
    if size:
        return claripy.BVS(name, size, explicit_name=True)
    else:
        return claripy.BVS(name, arch_info['bits'], explicit_name=True)


def BVV(value, size=None):
    if size:
        return claripy.BVV(value, size)
    else:
        return claripy.BVV(value, arch_info['bits'])

def BVValue(ast):
    value = ast.args[0]
    if value >> (arch_info['bits']-1):
        n = ~ast
        value = 0 - (n.args[0]+1)
    return value

def get_immediate_value(value):
    arch_bits = arch_info['bits']
    if value >> (arch_bits-1):
        max_immi = 2**arch_bits
        return 0 - (max_immi - value)
    return value

def get_mem_permission(addr):
    """
    Get the addr's read/write permission.
    """
    if STACK_MIN <= addr <= STACK_MAX:
        return 'stack'

    for name, (start, end) in section_regions.items():
        if start <= addr <= end:
            if name in ro_region_names:
                return 'ro'

            elif name in rw_region_names:
                return 'rw'

            elif name in bss_region_names:
                return 'bss'

            elif name == '.extern':
                return 'ext'

            elif name == '.text':
                return 'code'

    min_addr, max_addr = section_regions['.loader']
    if min_addr <= addr <= max_addr:
        return 'r'
    return 'imm'


def readable_address(addr):
    """
    If a concret value at the addr.
    """
    addr_immi = get_immediate_value(addr)
    # addr_str = '%x' % addr
    # if 'f' in addr_str[0]:
    #     return False
    return section_regions['.loader'][0] <= addr_immi <= section_regions['.loader'][1]
    # for name, (start, end) in section_regions.items():
    #     if name != '.loader' and start <= addr <= end:
    #         # print("get_mem: %s %x" % (name, addr))
    #         if (name in ro_region_names or
    #                 name in rw_region_names or
    #                 name == '.text'):
    #             return True
    # return False


def get_value_label(addr):
    """
    Get the addr's lable (G, E, C, I, S, etc...).
    """
    if STACK_MIN <= addr <= STACK_MAX:
        return 'S'

    min_addr, max_addr = section_regions['.loader']
    if addr < min_addr or addr > max_addr:
        return 'I'

    for name, (start, end) in section_regions.items():
        if name == '.extern' and start <= addr <= end:
            return 'E'

        elif name == '.text' and start <= addr <= end:
            return 'C'

        elif name == '.got' and start <= addr <= end:
            return 'g'

    return 'G'


def maybe_function(addr):
    """
    Whether the addr is a function address.
    The function addr maybe in '.text', '.extern', '.plt'
    """
    text_region = section_regions.get('.text')
    if text_region and text_region[0] <= addr <= text_region[1]:
        return True

    extern_region = section_regions.get('.extern')
    if extern_region and extern_region[0] <= addr <= extern_region[1]:
        return True

    plt_region = section_regions.get('.plt')
    if plt_region and plt_region[0] <= addr <= plt_region[1]:
        return True

    return False


def is_plt_region(addr):
    plt_region = section_regions.get('.plt')
    if plt_region and plt_region[0] <= addr <= plt_region[1]:
        return True

    return False


def is_code_region(addr):
    """
    Wheter the addr is code region.
    """
    region = section_regions.get('.text')
    if region is None:
        return False

    if region[0] <= addr <= region[1]:
        return True

    return False


def is_extern_region(addr):
    """
    Wheter the addr is extern region.
    """
    region = section_regions.get('.extern')
    if region is None:
        return False

    if region[0] <= addr <= region[1]:
        return True

    return False


def is_data_region(addr):
    """
    Wheter the addr is data (rodata etc.) region.
    """
    pe = get_mem_permission(addr)
    if pe == 'imm':
        return False
    elif pe == 'ro' or pe == 'rw':
        return True
    elif pe == 'r' and not is_code_region(addr):
        return True
    return False


def get_concrete_type(value, size=None):
    """
    Get concret value's data type (char, int, long, ptr etc.)
    """
    if get_mem_permission(value) != 'imm':
        return 'ptr'
    elif size is None:
        return basic_types['default']
    else:
        return basic_types[size]


def get_scope(addr):
    """
    Get the pointer's scope (global, heap, stack, etc.)
    """
    pe = get_mem_permission(addr)
    if pe == 'stack':
        return 'stack'

    elif pe == 'imm':
        return 'imm'

    else:
        return 'global'


def is_stack_symbol(sym):
    """
    Judge the symobl is a stack argument (some argument is push into stack).
    """
    p = re.match(r'^[s][\d]+$', sym)
    return True if p else False


def get_trace_symbols(ast):
    symbols = set()
    for v in ast.variables:
        p = re.match(r'^[srt][\d]+$', v)
        if p:
            symbols.add(p.string)

    return symbols


def is_arg_symbol(sym, arguments=None):
    if arguments is None:
        arguments = argument_vars

    if 'r' in sym and sym in arguments:
        return True

    # elif 's' in sym and sym in argument_vars:
    elif 's' in sym:
        return True

    return False

def is_simple_arg_constraint(ast, arguments=None):
    """
    """
    # print("simple-cons: %s %s" % (ast, ast.op))
    if arguments is None:
        arguments = argument_vars

    if ast.op == 'ZeroExt':
        ast = ast.args[1]

    if ast.op == 'BVS':
        sym = ast.args[0]
        if sym in arguments:
            return True
    elif ast.op != 'Load' and ast.op != 'Store' and len(ast.args) == 2:
        arg0, arg1 = ast.args
        if arg0.op == 'BVS' and arg1.op == 'BVS':
            sym0, sym1 = arg0.args[0], arg1.args[0]
            if sym0 in arguments and sym1 in arguments:
                return True
        elif arg0.op == 'BVS' and arg1.op == 'BVV':
            sym0 = arg0.args[0]
            if sym0 in arguments:
                return True
        elif arg0.op == 'BVV' and arg1.op == 'BVS':
            sym1 = arg1.args[0]
            if sym1 in arguments:
                return True
    return False

def sim_action_len(ast):
    """
    How many 'load' or 'store' action the ast has?
    """
    count = 0
    if ast.op in ls_ops:
        count += 1
    for child_ast in ast.recursive_children_asts:
        if child_ast.op in ls_ops:
            count += 1
    return count

def contain_mul(ast, var):
    """
    Whether containt a 'var * 4' or 'var * 8' in ast.
    """
    for child_ast in ast.recursive_children_asts:
        if (child_ast.op == '__mul__' and len(child_ast.args) == 2 and
                child_ast.args[0].op == 'BVS' and child_ast.args[1].op == 'BVV' and
                child_ast.args[0].args[0] == var and
                child_ast.args[1].args[0] in [4, 8]):
            return True
    return False

def has_sym_o(ast):
    for v in ast.variables:
        if 'o' in v:
            return True
    return False


def get_symbols(ast):
    """
    Get all symbols in a ast varialbe.
    """
    symbols = set()
    for v in ast.variables:
        if v != 'i':
            symbols.add(v)
    return list(symbols)


def parse_bool_condition(bool_con):
    cc_deps = []
    if len(bool_con.args) == 2:
        cc_dep1 = bool_con.args[0]
        cc_dep2 = bool_con.args[1]
        cc_deps.append(cc_dep1)
        cc_deps.append(cc_dep2)

    else:
        l.info("The bool expr %s have not two args, do it future!" % (bool_con))

    return cc_deps


def is_argument_define(ast_data, pure=True):
    if pure:
        if ast_data.op == 'BVS':
            if any([v for v in ast_data.variables if v in argument_vars]):
                return True

    else:
        if any([v for v in ast_data.variables if v in argument_vars]):
            return True

    return False


def is_argument(ast_data):

    has_global, has_arg = True, True

    for leaf_ast in ast_data.recursive_leaf_asts:
        if leaf_ast.op == 'BVV':
            if get_mem_permission(leaf_ast.args[0]) == 'stack':
                return False

        elif leaf_ast.op == 'BVS':
            v = leaf_ast.args[0]
            if 'r' in v and v not in argument_vars or 't' in v:
                return False

    return True


def contain_argument_or_global(ast_data, arguments=None):

    has_global, has_arg = True, True
    if arguments is None:
        arguments = argument_vars

    # stack_args = self.get_stack_arguments(arguments)

    for leaf_ast in ast_data.recursive_leaf_asts:
        if leaf_ast.op == 'BVV':
            pe = get_mem_permission(leaf_ast.args[0])
            if pe == 'stack':
                return False

            elif pe != 'imm':
                has_global = True

        elif leaf_ast.op == 'BVS':
            v = leaf_ast.args[0]
            if 'r' in v and v not in arguments or 't' in v:
                return False

            elif v in arguments:
                has_arg = True

    if has_global or has_arg:
        return True

    else:
        return False


def is_argument_v2(ast_data):
    if any([v for v in ast_data.variables if v != 'i' and v not in argument_vars]):
        return False


def get_stack_arguments(arguments):
    stack_args = []
    for arg in arguments:
        if is_stack_symbol(arg):
            stack_args.append(arg)
    return stack_args


def get_argument_define_info(self, ast_data, arg_define_info):
    """
    If data if a argument definition, get the pointer in the expr.
    """

    arg_syms = [v for v in ast_data.variables if v in argument_vars]
    if len(arg_syms) == 0:
        return

    if ast_data.op == 'BVS':
        arg_sym = arg_syms[0]
        arg_define_info[arg_sym] = 'LBF'

    else:
        for arg_sym in arg_syms:
            arg_define_info[arg_sym] = 'SLBF'


def get_argument_syms(ast_data):
    arg_syms = [v for v in ast_data.variables if v in argument_vars]
    return arg_syms


def get_simplify_ast(ast_data, simplify_asts):

    if ast_data.op == 'Load':
        load_ptr = ast_data.args[0]
        s_flag = is_simplify(load_ptr)

        if s_flag:
            simplify_asts.append(load_ptr)

        else:
            get_simplify_ast(load_ptr, simplify_asts)

    else:
        s_flag = is_simplify(ast_data)
        if s_flag:
            simplify_asts.append(ast_data)

        elif ast_data.op not in ['BVV', 'BVS']:
            for child_ast in ast_data.args:
                get_simplify_ast(child_ast, simplify_asts)


def is_simplify(ast):
    """
    Judge a ast could be simplify.
    """
    simplify_flag = False
    if ast.op in simplify_ops:
        if len(ast.args) >= 3:
            simplify_flag = True

        elif len(ast.args) == 2:
            if ast.args[0].op in simplify_ops:
                simplify_flag = True

            elif ast.args[1].op in simplify_ops:
                simplify_flag = True

    return simplify_flag


def is_pure_simplify(ast):
    """
    Judge a ast could be simplified, the ast must not contain 'load'.
    """
    if 'Load' not in str(ast) and 'Store' not in str(ast) and is_simplify(ast):
        return True

    return False


def get_inc_data_info(ast):
    inc_op = ast.op
    if inc_op not in ['__add__', '__sub__']:
        return

    inc_info = {'base':[], 'inc':set(), 'mul_inc':set(), 'inc_num':defaultdict(int)}

    child_asts = [ast]
    while child_asts:
        child_ast = child_asts.pop()
        for arg_ast in child_ast.args:
            if arg_ast.op in ['BVV', 'BVS']:
                inc_data = arg_ast.args[0]
                inc_info['inc'].add(inc_data)
                inc_info['inc_num'][inc_data] += 1
                # print("inc data: %s" % (inc_data))

            elif arg_ast.op == inc_op:
                child_asts.append(arg_ast)

            elif arg_ast.op == '__mul__':
                inc_o = get_mul_inc_offset(arg_ast)
                # print("mul inc offset: %s" % (inc_o))

                if inc_o is not None and inc_o.op in ['BVV', 'BVS']:
                    mul_inc_data = inc_o.args[0]
                    inc_info['mul_inc'].add(mul_inc_data)

            else:
                inc_info['base'].append(arg_ast)
                # print("base ast: %s" % (arg_ast))

    for mi in inc_info['mul_inc']:
        if mi in inc_info['inc_num']:
            inc_info['inc_num'].pop(mi)

    return inc_info

def get_mul_inc_offset(ast):
    arg_ast_0 = ast.args[0]
    arg_ast_1 = ast.args[1]
    if arg_ast_0.op == 'BVS':
        d = arg_ast_0.args[0]
        if d == 'i':
            return arg_ast_1

    elif arg_ast_1.op == 'BVV':
        d = arg_ast_1.args[0]
        if d == 'i':
            return arg_ast_0

    return None

def calculate_ast_struct_id(ast):
    leaf_info = []
    leaf_datas = []

    collect_ast_leaf_info(ast, 0, leaf_datas, leaf_info)

    struct_id = 0
    for leaf in leaf_info:
        leaf_data = leaf[0]
        # print("leaf_data: %s" % (leaf_data))
        if type(leaf_data) is str and (leaf_data[0] == 'o' or leaf_data[0] == 'i'):
            continue

        struct_id += (hash(leaf) * leaf[1])

    return struct_id


def collect_ast_leaf_info(ast, struct_level, leaf_datas, leaf_info):
    if struct_level >= max_struct_level:
        return
    level_con = struct_component[struct_level]
    # print("%s struct levle: %d %d" % (ast, struct_level, level_con))

    if ast.op in ['Load', 'Store']:
        struct_level += 1
        leaf_datas = []
        if struct_level >= max_struct_level:
            return
        level_con = struct_component[struct_level]
        # print("level: %d" % (struct_level))

    elif ast.op in atoms_ops:
        leaf_data = ast.args[0]
        leaf_info.append((leaf_data, level_con))
        return

    elif ast.op not in offset_ops:
        return

    for child_ast in ast.args:
        if type(child_ast) in [int, str]:
            continue

        # print("child: %s" % (child_ast))
        if child_ast.op in atoms_ops:

            leaf_data = child_ast.args[0]
            if leaf_data in leaf_datas or leaf_data in [1, 2, 3]:
                continue

            if leaf_data:
                leaf_datas.append(leaf_data)
                leaf_info.append((leaf_data, level_con))

        else:
            collect_ast_leaf_info(child_ast, struct_level, leaf_datas, leaf_info)


def get_ast_len(ast):
    return len(list(ast.recursive_children_asts))


def get_all_deref_info_with_search(ast_data, r_ast):
    """
    Find all child load ast variables in the ast_data.
    Only process the load(rax), load(rax + offset), or load(0x467890)
    """
    deref_info = {}
    search_index = []

    index = 0

    if ast_data.op == 'BVS':
        return deref_info

    elif ast_data.op in ['Load', 'Store']:
        addr = ast_data.args[0]
        binop, base_offset = extract_base_and_offset(addr, depth=0)

        if base_offset:
            deref_info[index] = (binop, base_offset, ast_data)

        else:
            deref_info[index] = None

        index += 1

    r_ast_hash = r_ast.__hash__()

    for child in ast_data.recursive_children_asts:
        if child.op in ['Load', 'Store']:
            addr = ast_data.args[0]
            binop, base_offset = extract_base_and_offset(addr, depth=0)

            if base_offset:
                deref_info[index] = (binop, base_offset, ast_data)

            else:
                deref_info[index] = None

            index += 1

        child_hash = child.__hash__()

        if child_hash == r_ast_hash:
            if r_ast.op in ['Load', 'Store']:
                search_index.append(index-1)

            else:
                search_index.append(index)
                index += 1

    return deref_info, search_index


def get_all_deref_info(ast_data):
    """
    Find all child load ast variables in the ast_data.
    Only process the load(rax), load(rax + offset), or load(0x467890)
    """
    deref_info = {}
    sub_datas = []

    if ast_data.op == 'BVS':
        return deref_info

    elif ast_data.op in ['Load', 'Store']:
        sub_datas.append(ast_data)

    for child in ast_data.recursive_children_asts:
        if child.op in ['Load', 'Store']:
            sub_datas.append(child)

    for index, sub_data in enumerate(sub_datas):
        addr = sub_data.args[0]
        binop, base_offset = extract_base_and_offset(addr, depth=0)

        # if base_offset:
        deref_info[index] = (binop, base_offset, sub_data)

        # else:
        #     deref_info[index] = None

    return deref_info


def extract_base_and_offset(addr, depth=0):
    """
    Extract 'base+offset' from a load(addr) expr.
    :param addr: the load expr's addr
    """
    binop, base_offset = None, None

    if addr.op == 'BVS':
        v = addr.args[0]
        binop = '+'
        base_offset = (v, 0)

    elif addr.op == 'BVV':
        v = addr.args[0]
        binop = '+'
        base_offset = (v, 0)

    elif addr.op == 'Load' or addr.op == 'Store':
        binop = '+'
        base_offset = (None, 0)

    elif len(addr.args) == 2:

        if 'add' in addr.op:
            binop = '+'

        elif 'sub' in addr.op:
            binop = '-'

        else:
            return binop, base_offset

        arg_0, arg_1 = addr.args[0], addr.args[1]
        sym0, value0, sym1, value1 = None, None, None, None
        # print("arg_0: %s, arg_1: %s" % (arg_0, arg_1))

        if arg_0.op == 'BVS':
            sym0 = arg_0.args[0]

        elif arg_0.op == 'BVV':
            value0 = arg_0.args[0]

        else:
            if is_pure_simplify(addr) and depth == 0:
                # print("pure simplify: %s" % (addr))
                new_addr = claripy.simplify(addr)
                return extract_base_and_offset(new_addr, depth=1)

        if arg_1.op == 'BVS':
            sym1 = arg_1.args[0]

        elif arg_1.op == 'BVV':
            value1 = arg_1.args[0]

        else:
            if is_pure_simplify(addr) and depth == 0:
                # print("pure simplify: %s" % (addr))
                new_addr = claripy.simplify(addr)
                return extract_base_and_offset(new_addr, depth=1)

        if value0 and value1:
            base = value0 + value1
            base_offset = (base, 0)

        elif sym0 and sym1:
            base_offset = (sym0, sym1)

        elif value1:
            if get_mem_permission(value1) == 'imm':

                if sym0:
                    base_offset = (sym0, value1)

                else:
                    base_offset = (None, value1)

            else:

                if sym0:
                    base_offset = (value1, sym0)

        elif value0:
            if get_mem_permission(value0) == 'imm':

                if sym1:
                    base_offset = (sym1, value0)

                else:
                    base_offset = (None, value0)

            else:

                if sym1:
                    base_offset = (value0, sym1)

    elif is_pure_simplify(addr) and depth == 0:
        # print("pure simplify: %s" % (addr))
        new_addr = claripy.simplify(addr)
        return extract_base_and_offset(new_addr, depth=1)

    return binop, base_offset


def get_index_info_with_sim(ast_data, sim):
    """
    get the special child ast index.
    """
    sim_index = []
    index = 0

    if ast_data.op == 'BVS':
        if sim == ast_data.args[0]:
            sim_index.append(0)

        return sim_index

    elif ast_data.op == 'Load':
        index += 1

    for child in ast_data.recursive_children_asts:
        if child.op == 'Load':
            index += 1

        elif child.op == 'BVS' and child.args[0] == sim:
            sim_index.append(index)
            index += 1

    return sim_index


def get_index_info_with_child_ast(ast_data, child_ast):
    """
    get the special child ast index.
    """
    index = 0
    all_contain_asts = [ast_data]
    indexs, child_indexs = [], []

    for child in ast_data.recursive_children_asts:
        all_contain_asts.append(child)

    for child in all_contain_asts:
        if child.__hash__() == child_ast.__hash__():
            child_indexs.append(index)
            indexs.append(index)
            index += 1

        elif child.op in ['Load', 'Store']:
            indexs.append(index)
            index += 1

    return indexs, child_indexs

def get_ls_indexs(ast_data):
    ls = []
    index = 0
    if ast_data.op in ['Load', 'Store']:
        ls.append(index)
        index += 1

    for child in ast_data.recursive_children_asts:
        if child.op in ['Load', 'Store']:
            ls.append(index)
            index += 1

    return ls

def extract_vptr_and_offset(ast_data):
    """
    Extract vtable pointer and virtual function offset in vtable.
    """
    base, offset = None, None
    addr = ast_data.args[0]
    if len(addr.args) == 2 and 'add' in addr.op or 'sub' in addr.op:
        arg_0, arg_1 = addr.args[0], addr.args[1]

        if arg_1.concrete:
            if get_mem_permission(arg_1.args[0]) == 'imm':
                base, offset = arg_0, arg_1

            else:
                base, offset = arg_1, arg_0

        elif arg_0.concrete:
            if get_mem_permission(arg_0.args[0]) == 'imm':
                base, offset = arg_1, arg_0

            else:
                base, offset = arg_0, arg_1

    elif addr.op in ['BVS', 'BVV']:
        base, offset = addr, 0

    elif addr.op in ['Load', 'Store']:
        base, offset = addr, 0

    return base, offset


def calculate_offset(offsets_info):

    op, offset = offsets_info[0]
    binop = '+' if op == '__add__' else '-'
    if len(offsets_info) == 1:
        return (binop, offset)

    else:
        for op, o in offsets_info[1:]:
            if op == '__add__':
                offset += o

            else:
                offset -= o
        return (binop, offset)


def get_base_offset_v2(binop_data, trace_sims):
    """
    Get the base and offset in binop_data based on var types.
    The binop_data not contain load and store operations.
    """
    # print("get_offset-v2: %s %s" % (binop_data, trace_sims))
    if binop_data.op not in offset_ops:
        # raise Exception("%s op is not offset" % (binop_data))
        return None, None

    binop_data = claripy.simplify(binop_data)
    if binop_data.op in leaf_operations:
        return binop_data, ('+', BVV(0))

    offsets_info = []
    bases = []
    unknows = []

    stack_list = [binop_data]
    while stack_list:
        op_data = stack_list.pop()
        binop = op_data.op
        for arg in op_data.args:
            if arg.op in leaf_operations:
                var = arg.args[0]
                if type(var) is int:
                    pe = get_mem_permission(var)
                    if pe == 'imm':
                        offsets_info.append((binop, arg))

                    else:
                        bases.append(arg)

                elif var in trace_sims:
                    if trace_sims[var].var_type == 'ptr':
                        bases.append(arg)

                    elif trace_sims[var].var_type is not None:
                        offsets_info.append((binop, arg))

                    else:
                        unknows.append((binop, arg))

                else:
                    offsets_info.append((binop, arg))

            elif arg.op in offset_ops:
                stack_list.append(arg)

            else:
                offsets_info.append((binop, arg))

    # print("bases: %s offsets: %s unknows: %s" % (bases, offsets_info, unknows))

    if len(bases) == 0 and len(unknows) == 1:
        bases.append(unknows[0][1])
        unknows.clear()

    if len(bases) == 0:
        # raise Exception("Unlucky, we couldn't find base ptr in %s" % (binop_data))
        return None, None

    elif len(bases) > 1:
        # raise Exception("There are more than one base ptr in %s" % (binop_data))
        return None, None

    if len(unknows):
        offsets_info.extend(unknows)

    if len(offsets_info) == 0:
        # raise Exception("We couldn't find offset in %s" % (binop_data))
        return None, None

    offset = calculate_offset(offsets_info)

    return bases[0], offset


def find_length_taint(opnd_info, trace_ast, trace_sims):
    """
    calculate the stirng's length by a loop.
    """
    pass

def find_ptr_taint_v2(opnd_info, trace_ast, trace_sims):
    """
    In forward, find the taint transfer in binop, e.g. (Add r3, r3, 5)
    """
    find_flag = False
    opnd0, opnd1 = opnd_info[1]
    if opnd0 not in trace_sims:
        return find_flag

    opnd0_type = trace_sims[opnd0].var_type
    if opnd0_type and opnd0_type != 'ptr':
        return find_flag

    if trace_ast.op == 'BVS':
        trace_var = trace_ast.args[0]
        if (type(opnd1) is int and opnd1 <= Taint_Offset or type(opnd1) is str):
            find_flag = True

    elif trace_ast.op in offset_ops:
        base, offset_info = get_base_offset_v2(trace_ast, trace_sims)
        # print(base, offset_info)
        if base is None:
            return False

        base_var = base.args[0]
        if base_var != opnd0:
            return find_flag

        op, offset = offset_info
        if offset.op in leaf_operations:
            off_var = offset.args[0]
            if off_var == opnd1 and op == opnd_info[0]:
                find_flag = True

            elif (type(off_var) is str and ('o' in off_var or 'i' in off_var)
                    and (type(opnd1) is str or (type(opnd1) is int and -8 < opnd1 <= Taint_Offset))):
                find_flag = True

            elif type(off_var) is int and type(opnd1) is int and 0 < opnd1-off_var <= Taint_Offset:
                find_flag = True

        else:
            if (type(opnd1) is str or (type(opnd1) is int and 0<= opnd1 <= Taint_Offset)):
                find_flag = True

    return find_flag


def find_ptr_taint_v1(addr_var, trace_ast, trace_sims):
    """
    In forward, find the taint transfer in ptr.
    """
    find_flag = False
    if addr_var not in trace_sims:
        return find_flag

    addr_type = trace_sims[addr_var].var_type
    if addr_type and addr_type != 'ptr':
        return find_flag

    if trace_ast.op == 'BVS' or is_str_pointer(trace_ast):
        find_flag = True

    elif trace_ast.op in offset_ops:
        base, offset_info = get_base_offset_v2(trace_ast, trace_sims)
        # print("%s %s" % (base, offset_info))
        if base is None:
            return False

        base_var = base.args[0]
        if base_var != addr_var:
            return find_flag

        op, offset = offset_info
        if offset.op in leaf_operations:
            off_var = offset.args[0]
            if type(off_var) is str and 'o' in off_var or (type(off_var) is int and 1 <= off_var <= 3):
                find_flag = True

        # else:
        #     find_flag = True

    return find_flag

def find_ptr_taint_v3(addr_value, trace_ast, trace_sims):
    """
    In forward, find the taint transfer in ptr.
    """
    find_flag = False

    # print("%s %x" % (trace_ast, addr_value))

    if trace_ast.op == 'BVV':
        if addr_value == trace_ast.args[0]:
            find_flag = True

    elif trace_ast.op in offset_ops:
        base, offset_info = get_base_offset_v2(trace_ast, trace_sims)
        if base is None:
            return False
        base_value = base.args[0]
        if base_value != addr_value:
            return find_flag

        op, offset = offset_info
        if offset.op in leaf_operations:
            off_var = offset.args[0]
            if type(off_var) is str and 'o' in off_var:
                find_flag = True

        # else:
        #     find_flag = True

    return find_flag


def find_ptr_taint_v4(opnd_info, ast):
    # print("taint-v4: %s %s" % (str(opnd_info), ast))
    opnds = opnd_info[1]
    if len(ast.args) == 2:
        arg0, arg1 = ast.args
        if arg0.op in ['BVV', 'BVS'] and arg0.args[0] == opnds[0] and arg1.op == 'BVS' and 'o' in arg1.args[0]:
            return ast

        elif arg0.op in offset_ops and arg1.op == 'BVV':
            return find_ptr_taint_v4(opnd_info, arg0)


def set_opnds_type(opnds_info, var_type):
    op = opnds_info[0]
    opnd0_type, opnd1_type = None, None
    if var_type == 'ptr':
        opnds_type = opnds_info[3]
        if op == '+':
            if opnds_type[0] is None and (opnds_type[1] and opnds_type[1] != 'ptr'):
                opnd0_type = 'ptr'

            elif (opnds_type[0] and opnds_type[0] != 'ptr') and opnds_type[1] is None:
                opnd1_type = 'ptr'

    if opnd0_type:
        opnds_type = (opnd0_type, opnds_info[3][1])
        return (op, opnds_info[1], opnds_info[2], opnds_type)

    elif opnd1_type:
        opnds_type = (opnds_info[3][0], opnd1_type)
        return (op, opnds_info[1], opnds_info[2], opnds_type)

    else:
        return opnds_info


def get_increment_data(opnds_info, sim_types):

    opnds = opnds_info[1]


def get_no_ls_ast_type(ast):
    var_type = basic_types['default']
    for leaf_ast in ast.recursive_leaf_asts:
        if leaf_ast.op == 'BVV':
            value = leaf_ast.args[0]
            v_type = get_concrete_type(value)
            if v_type == 'ptr':
                var_type = v_type
    return var_type


def simplify_rodata_load(state, data_ast, size_bytes, endness, sim_action_info, mode=None):

    new_datas = []
    for child_ast in data_ast.recursive_children_asts:
        if child_ast.op != 'Load':
            continue

        ld_addr = child_ast.args[0]
        # print("load: %s" % (ld_addr))

        if ld_addr.op == 'BVV':
            addr = ld_addr.args[0]
            pe = get_mem_permission(addr)
            if pe == 'ro' or pe == 'rw':
                value = state.memory.load(addr, size_bytes, endness=endness)
                # print("%s %s" % (value, endness))
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
            read_values = set()
            read_recursive_data(state, ld_addr, size_bytes, endness, read_values, read_type='data', end_flag=0, var_type=child_var_type)
            for value in read_values:
                value_ast = BVV(value, child_ast.size())
                new_data = data_ast.replace(child_ast, value_ast)
                new_datas.append(new_data)
            return new_datas

        elif mode == 'guess' and ld_addr.op in offset_ops and not_contain_ls(ld_addr) and contain_sym(ld_addr, 'o'):
            read_values = set()
            read_recursive_data_v2(state, ld_addr, size_bytes, endness, read_values, read_type='data', end_flag=0)
            for value in read_values:
                value_ast = BVV(value, child_ast.size())
                new_data = data_ast.replace(child_ast, value_ast)
                new_datas.append(new_data)
            return new_datas

    return new_datas


def not_contain_ls(data_ast):
    for child_ast in data_ast.recursive_children_asts:
        if child_ast.op in ['Load', 'Store']:
            return False
    return True

def is_str_pointer(data_ast):
    if data_ast.op == '__add__' and len(data_ast.args) == 2:
        opnd0, opnd1 = data_ast.args
        if opnd0.op == 'BVS' and opnd1.op == '__mul__' and len(opnd1.args) ==2:
            mul0, mul1 = opnd1.args
            if mul0.op == 'BVS' and 'i' in mul0.args[0]:
                return True
    return False

def is_str_pointer_v2(data_ast):
    if data_ast.op == '__add__' and len(data_ast.args) == 2:
        opnd0, opnd1 = data_ast.args
        if ((opnd0.op == 'BVS' or (opnd0.op == 'Store' and opnd0.args[0].op == 'BVV')) and
                opnd1.op == '__mul__' and len(opnd1.args) ==2):
            mul0, mul1 = opnd1.args
            if mul0.op == 'BVS' and 'i' in mul0.args[0]:
                return True
    return False

def has_simple_offset(data_ast, add_level=0):
    if add_level >= 2:
        return False
    if data_ast.op == '__add__' and len(data_ast.args) >= 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if not is_simple_offset(opnd1):
            return False
        elif (opnd0.op in leaf_operations or opnd0.op in ls_ops):
            return True
        else:
            add_level += 1
            return has_simple_offset(opnd0 ,add_level=add_level)
    return False

def is_simple_offset(data_ast):
    if data_ast.op in leaf_operations:
        return True
    elif data_ast.op == '__mul__' and len(data_ast.args) ==2:
        mul0, mul1 = data_ast.args
        if (mul0.op == 'BVS' and ('i' in mul0.args[0] or 'o' in mul0.args[0]) and
                (mul1.op == 'BVV' and 0 <= mul1.args[0] <= 64 or
                 mul1.op == 'BVS' and 'o' in mul1.args[0])):
            return True
    return False

def is_inc_offset(data_ast):
    if data_ast.op == '__mul__' and len(data_ast.args) ==2:
        mul0, mul1 = data_ast.args
        if (mul0.op == 'BVS' and ('i' in mul0.args[0] or 'o' in mul0.args[0]) and
                (mul1.op == 'BVV' and 0 <= mul1.args[0] <= 64 or
                 mul1.op == 'BVS' and 'o' in mul1.args[0])):
            return True
    return False

def has_simple_offset_v2(data_ast, add_level=0):
    if data_ast.op == '__add__' and len(data_ast.args) == 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if (opnd0.op in leaf_operations or opnd0.op in ls_ops):
            if is_inc_offset(opnd1):
                return True
            # elif (opnd1.op == 'BVS' and 'o' in opnd1.args[0]) or (opnd1.op == 'BVV' and 0 <= opnd1.args[0] <= 0x5120 and opnd1.args[0] % 4 == 0):
            elif (opnd1.op == 'BVS' and 'o' in opnd1.args[0]) or (opnd1.op == 'BVV' and 0 <= opnd1.args[0] <= 0x5120):
                return True
    return False

def has_simple_offset_v3(data_ast, add_level=0):
    if data_ast.op == '__add__' and len(data_ast.args) == 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if (opnd0.op in leaf_operations or opnd0.op in ls_ops):
            if is_inc_offset(opnd1):
                return True
            elif (opnd1.op == 'BVS') or (opnd1.op == 'BVV' and 0 <= opnd1.args[0] <= 0x8000 and opnd1.args[0] % 4 == 0):
                return True
    return False

def is_simple_cons(cons_ast):
    def is_simple_addr(addr_ast):
        if addr_ast.op in leaf_operations:
            return True
        elif addr_ast.op == '__add__' and len(addr_ast.args) ==2:
            opnd0, opnd1 = addr_ast.args
            if opnd0.op in leaf_operations and opnd1.op == 'BVV':
                return True
        return False

    if cons_ast.op in leaf_operations:
        return True
    elif cons_ast.op in offset_ops:
        # print("xpx-> %s %s" % (cons_ast, cons_ast.args))
        if len(cons_ast.args) == 2:
            opnd0, opnd1 = cons_ast.args
            print(opnd0, opnd1)
            if opnd1.op != 'BVV':
                return False
            if opnd0.op in leaf_operations:
                return True
            elif opnd0.op in ls_ops and is_simple_addr(opnd0.args[0]):
                return True
        else:
            return False
    elif cons_ast.op in ['ZeroExt']:
        # print("xpx-> %s %s" % (cons_ast.op, cons_ast.args))
        return is_simple_cons(cons_ast.args[1])
    elif cons_ast.op == 'Load' and is_simple_addr(cons_ast.args[0]):
        return True
    elif cons_ast.op == '__mul__' and cons_ast.args[0].op in leaf_operations and cons_ast.args[1].op in leaf_operations:
        return True
    return False

def is_filter_v1(data_ast):
    """
    Filter some complex expr.
    """
    # print("ooo-> %s %s" % (data_ast, data_ast.op))
    if data_ast.op in ls_ops:
        data_ast = data_ast.args[0]
        # print(data_ast.op, data_ast.args)
    op = data_ast.op
    if op not in ls_ops and op not in offset_ops and op not in leaf_operations:
        return True
    if op == '__sub__':
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        # if opnd0.op == '__sub__' or opnd0.op == '__add__':
        if opnd0.op not in leaf_operations:
            if is_filter_v1(opnd0):
                return True
        if opnd1.op not in leaf_operations:
            return True
    elif op == '__add__':
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if opnd0.op not in leaf_operations:
            if is_filter_v1(opnd0):
                return True
        if opnd1.op not in leaf_operations and not not_contain_ls(opnd1):
            return True
    return False

"""
Store(Store(Load(Load(r88 + 0x8) + 0x1 + 0x24 + 0x1 + 0x1 + 0x1 + 0x1 + o87 + 0x1 + i * o48 + 0xffffff08) + 0x20))
ooo-> <BV32 Store(Store(Load(Load(Load(r80 + 0xc80) + i * o48 + 0xffffff08) + 0x20) + 0x20))> Store
ooo-> <BV32 Load(Load(Load(r80 + 0xc80) + i * o48 + 0xffffff08) + 0x20) + 0x20> __add__
ooo-> <BV32 Load(Load(Load(r80 + 0xc80) + i * o48 + 0xffffff08) + 0x20)> Load
ooo-> <BV32 Load(Load(r80 + 0xc80) + i * o48 + 0xffffff08)> Load
OMG-->1
OMG-->2
OMG-->2
"""
def is_filter_v2(data_ast):
    """
    Filter some complex expr.
    """
    # print("ooo-> %s %s" % (data_ast, data_ast.op))
    flag = False
    if data_ast.op in ls_ops:
        data_ast = data_ast.args[0]
        # print(data_ast.op, data_ast.args)
    # print("ooo-> %s %s" % (data_ast, data_ast.op))
    op = data_ast.op
    # if op not in ls_ops and op not in offset_ops and op not in leaf_operations:
    #     flag = True
    if op == '__sub__' and len(data_ast.args) >= 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if opnd0.op not in leaf_operations and opnd0.op not in ls_ops:
            flag = True
        elif opnd1.op != 'BVV':
            flag = True
        elif opnd0.op in ls_ops:
            if is_filter_v2(opnd0):
                flag = True
    elif op == '__add__' and len(data_ast.args) >= 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if has_simple_offset(data_ast):
            # print("Y1")
            if opnd0.op in ls_ops:
                if is_filter_v2(opnd0):
                    # print("Y2")
                    flag = True
                # else:
                    # print("Y3")
            elif opnd0.op in offset_ops:
                if is_filter_v2(opnd0):
                    flag = True
                # print("Yx")
        else:
            # print("Y4")
            flag = True
    elif op in ls_ops:
        if is_filter_v2(data_ast.args[0]):
            flag = True
        # print("Y5 %s" % (flag))
    elif op not in leaf_operations:
        flag = True
    return flag

def is_filter_v3(data_ast):
    """
    Filter some complex expr.
    """
    # print("ooo-> %s %s" % (data_ast, data_ast.op))
    flag = False
    if data_ast.op in ls_ops:
        data_ast = data_ast.args[0]
        # print(data_ast.op, data_ast.args)
    # print("ooo-> %s %s" % (data_ast, data_ast.op))
    op = data_ast.op
    # if op not in ls_ops and op not in offset_ops and op not in leaf_operations:
    #     flag = True
    if op == '__sub__' and len(data_ast.args) >= 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if opnd0.op not in leaf_operations and opnd0.op not in ls_ops:
            flag = True
        elif opnd1.op != 'BVV' or (opnd1.op == 'BVV' and (opnd1.args[0] > 64 or opnd1.args[0] < 0 or opnd1.args[0] % 4 != 0)):
            flag = True
        elif opnd0.op in ls_ops:
            if is_filter_v3(opnd0):
                flag = True
    elif op == '__add__' and len(data_ast.args) == 2:
        opnd0, opnd1 = data_ast.args[0], data_ast.args[1]
        if has_simple_offset_v2(data_ast):
            # print("Y1")
            if opnd0.op in ls_ops:
                if is_filter_v3(opnd0):
                    # print("Y2")
                    flag = True
                # else:
                    # print("Y3")
            elif opnd0.op in offset_ops:
                if is_filter_v3(opnd0):
                    flag = True
                # print("Yx")
        else:
            # print("Y4")
            flag = True
    elif op in ls_ops:
        if is_filter_v3(data_ast.args[0]):
            flag = True
        # print("Y5 %s" % (flag))
    elif op not in leaf_operations:
        flag = True
    return flag

def is_filter_v4(data_ast):
    if data_ast.op in leaf_operations:
        return False
    elif has_simple_offset_v3(data_ast):
        return False
    else:
        return is_filter_v3(data_ast)
    return True

def simplify_simple_expr(trace_expr):
    ast = trace_expr.expr.ast
    if ('add' in ast.op or 'sub' in ast.op) and len(ast.args) == 2:
        opnd0, opnd1 = ast.args
        if opnd1.op == 'BVV' and (opnd1.args[0] == 0):
            trace_expr.expr.ast = opnd0
        elif (trace_expr.expr.data_type == 'Tdata' and
              trace_expr.expr.var_type == 'ptr' and
              opnd0.op == 'BVS' and opnd1.op == 'BVS' and 'o' in opnd1.args[0]):
            trace_expr.expr.ast = opnd0

def contain_sym(ast, sym):
    for var in ast.variables:
        if sym in var:
            return True
    return False

def get_var(ast, sym):
    offset = 0
    for child_ast in ast.recursive_children_asts:
        if child_ast.op == '__mul__' and len(child_ast.args) ==2:
            opnd0, opnd1 = child_ast.args
            if opnd0.op == 'BVS' and opnd1.op == 'BVV' and 'o' in opnd0.args[0]:
                offset = opnd1.args[0]
                return opnd0.args[0], offset
    for var in ast.variables:
        if sym in var:
            return var, offset


def read_data(state, addr, size_bytes, endness):
    pe = get_mem_permission(addr)
    if pe == 'ro' or pe == 'rw':
        value_ast = state.memory.load(addr, size_bytes, endness=endness)
        if value_ast.op == 'BVV':
            return value_ast.args[0]


def read_recursive_data(state, addr, size_bytes, endness, read_values, constraints=None, read_type=None, end_flag=None, var_type=None):
    i = BVS('i')
    max_offset = constraints[0] if constraints else None
    for o in range(Max_i):
        offset = BVV(o)
        new_addr = addr.replace(i, offset)
        new_addr = claripy.simplify(new_addr)
        # print("read_recursive: addr %s" % (new_addr))
        if new_addr.op == 'BVV':
            addr_value = new_addr.args[0]
            if max_offset and addr_value > max_offset:
                break

            value = read_data(state, addr_value, size_bytes, endness)
            if value and value > 0:
                if read_type == 'func' and is_code_region(value):
                    read_values.add(value)
                    # print("  -- %x : %x" % (addr_value, value))

                elif read_type == 'data' and is_data_region(value):
                    read_values.add(value)
                    # print("  -- %x : %x" % (addr_value, value))

                else:
                    return

            elif value is None or value == end_flag:
                return

            # elif value == 0:
                # print("  -- %x : %x" % (addr_value, value))

        elif var_type and var_type != 'ptr':
            read_values.add(o)


def read_recursive_data_v2(state, addr, size_bytes, endness, read_values, constraints=None, read_type=None, end_flag=None, var_type=None):
    var, offset = get_var(addr, 'o')
    subvariable = BVS(var)
    step = 1 if offset != 0 and offset%4 == 0 else state.arch.bytes
    arch_bits = state.arch.bytes
    end = step * Max_o if step != 1 else step * Max_o * arch_bits
    # print("step: %d" % (step))
    max_offset = constraints[0] if constraints else None
    for o in range(0, end, step):
        offset = BVV(o)
        # print(addr, subvariable, offset)
        new_addr = addr.replace(subvariable, offset)
        new_addr = claripy.simplify(new_addr)
        print("read_recursive: addr %s" % (new_addr))
        if new_addr.op == 'BVV':
            addr_value = new_addr.args[0]
            if max_offset and addr_value > max_offset:
                break

            value = read_data(state, addr_value, size_bytes, endness)
            # print("value: %x" % (value))
            if value and value > 0:
                read_values.add(value)

            elif value is None or value == end_flag:
                return


"""
<R-Expr <BV32 Load(Load(0xa3dd4 + i * 0x8 - 0x4) + i * 0x18 + 0x8)> (671188) (B)>
"""

def read_data_with_load(state, data_ast, size_bytes, endness, constraints, sim_action_info):

    read_values = set()
    new_asts = []

    data_worklist = [data_ast]
    while data_worklist:
        data_ast = data_worklist.pop()
        tmp_asts = simplify_rodata_load(state, data_ast, size_bytes, endness, sim_action_info)
        if tmp_asts:
            data_worklist.extend(tmp_asts)

        else:
            new_asts.append(data_ast)

    for data_ast in new_asts:
        # print("Load data from: %s" % (data_ast))
        if data_ast.op == 'BVV':
            read_values.add(data_ast.args[0])

        elif data_ast.op == 'Load':
            addr = data_ast.args[0]
            if addr.op == 'BVV':
                addr_value = addr.args[0]
                value = read_data(state, addr_value, size_bytes, endness)
                if value and (is_code_region(value) or is_extern_region(value)):
                    read_values.add(value)

            elif addr.op in offset_ops and not_contain_ls(addr):
                if 'i' in addr.variables:
                    read_recursive_data(state, addr, size_bytes, endness, read_values, constraints, read_type='func')

                else:
                    new_addr = claripy.simplify(addr)
                    if new_addr.op == 'BVV':
                        addr_value = new_addr.args[0]
                        value = read_data(state, addr_value, size_bytes, endness)
                        if value and is_code_region(value):
                            read_values.add(value)

    return read_values


def calculate_switch_targets(state, data_ast, size_bytes, endness, constraints, sim_action_info):

    read_values = set()
    new_asts = []

    data_worklist = [data_ast]
    while data_worklist:
        data_ast = data_worklist.pop()
        tmp_asts = simplify_rodata_load(state, data_ast, size_bytes, endness, sim_action_info, mode='guess')
        if tmp_asts:
            data_worklist.extend(tmp_asts)

        else:
            new_asts.append(data_ast)

    for data_ast in new_asts:
        print("Load data from: %s" % (data_ast))
        if data_ast.op == 'BVV':
            read_values.add(data_ast.args[0])

        elif data_ast.op == 'Load':
            addr = data_ast.args[0]
            if addr.op == 'BVV':
                addr_value = addr.args[0]
                value = read_data(state, addr_value, size_bytes, endness)
                if value and (is_code_region(value) or is_extern_region(value)):
                    read_values.add(value)

            elif addr.op in offset_ops and not_contain_ls(addr):
                if 'i' in addr.variables:
                    read_recursive_data(state, addr, size_bytes, endness, read_values, constraints, read_type='func')

                else:
                    new_addr = claripy.simplify(addr)
                    if new_addr.op == 'BVV':
                        addr_value = new_addr.args[0]
                        value = read_data(state, addr_value, size_bytes, endness)
                        if value and is_code_region(value):
                            read_values.add(value)

    return read_values


def get_var_in_block(block, v):
    if type(v) is int:
        return None, v

    elif type(v) is str:
        if 't' in v:
            at = block.live_defs[v]
            if v in block.tmp_alias:
                return list(block.tmp_alias[v])[0], at.value

        elif 'r' in v and v not in block.reg_defs:
            at = block.live_defs[v]
            return v, at.value


def read_stack_var(block, stack_addr):
    if stack_addr in block.live_defs:
        print("stack-var: %s" % (block.live_defs[stack_addr]))


def get_value(block, v):
    """
    Get reg or tmp's value in block.
    """
    if type(v) is int:
        return v

    elif type(v) is str:
        if 't' in v:
            at = block.live_defs[v]
            if type(at.value) is int:
                return at.value

        elif 'r' in v:
            pre_blocks = list(block.predecessors)
            if len(pre_blocks):
                pre_block = pre_blocks[0]
                if v in pre_block.live_defs and type(pre_block.live_defs[v].value) is int:
                    return pre_block.live_defs[v].value

            elif v in block.live_defs and type(block.live_defs[v].value) is int:
                return block.live_defs[v].value

    return None


def get_guard_args(block, guard):
    if len(guard.args) != 2:
        return None, None
    live_defs = block.live_defs
    arg0, arg1 = guard.args
    # print(arg0, arg1)
    var0 = get_var_in_block(block, arg0.args[0])
    var1 = get_var_in_block(block, arg1.args[0])

    return var0, var1

def calculate_recurisive_id(ast):
    """
    Calculate the recurisive expr's struct id.
    """
    collect_leaf_datas = set()
    struct_id, recur_level = 1, 0
    if ast.op in ls_ops:
        recur_level += 1
    for child_ast in ast.recursive_children_asts:
        if child_ast.op in ls_ops:
            recur_level += 1
        if child_ast.op in leaf_operations:
            v = child_ast.args[0]
            if v and v not in collect_leaf_datas:
                collect_leaf_datas.add(v)
                struct_id *= hash(v)
    return struct_id, recur_level
