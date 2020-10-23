#!/usr/bin/env python

from .parse_ast import *
from .global_config import *


def get_sim_scope(var, sims):
    if var in sims and sims[var].var_type == 'ptr':
        return 'aptr'


def get_expr_base_ptr(expr):
    """
    Get the expr's base pointer.
    """
    bases = []
    base_ptr = None
    for var, sim in expr.sims.items():
        if sim.var_type == 'ptr':
            bases.append(var)

    if len(bases) == 1:
        base_ptr = bases[0]

    elif len(bases) >= 2:
        base_ptr = get_complex_expr_base_ptr(expr)

    else:
        print("BASE-PTR-ERROR, %s" % (expr))

    if base_ptr is None:
        print("NON-BASE, %s" % (expr))

    return base_ptr


def get_complex_expr_base_ptr(expr):
    ast = expr.ast
    sims = expr.sims
    sim_actions = expr.sim_actions

    sim_action_info = {}
    for i, sim_action in sim_actions.items():
        action_id = sim_action.action_data.__hash__()
        sim_action_info[action_id] = sim_action.var_type

    base = get_ast_base_ptr(ast, sims, sim_action_info)

    return base


def judge_leaf_base(ast, sims):
    var = ast.args[0]
    if type(var) is str and var in sims and sims[var].var_type == 'ptr':
        return var

    elif type(var) is int and get_scope(var) != 'imm':
        return var

    return None

def get_ast_base_ptr(ast, sims, sim_action_info):
    """
    Get the root pointer in ast.
    """

    if ast.op in leaf_operations:
        base = judge_leaf_base(ast, sims)
        if base:
            return base

    elif ast.op in offset_ops:
        for child_ast in ast.args:
            if child_ast.op in leaf_operations:
                base = judge_leaf_base(child_ast, sims)
                if base:
                    return base

            elif child_ast.op in ls_ops:
                ls_ty = get_sim_action_scope(child_ast, sim_action_info)
                if ls_ty == 'ptr' or ls_ty is None:
                    base = get_ast_base_ptr(child_ast.args[0], sims, sim_action_info)
                    if base:
                        return base

            elif child_ast.op in offset_ops:
                base = get_ast_base_ptr(child_ast, sims, sim_action_info)
                if base:
                    return base

    elif ast.op in ls_ops:
        base = get_ast_base_ptr(ast.args[0], sims, sim_action_info)
        if base:
            return base


def judge_ls_base(ast):
    is_reg, is_global, is_stack = False, False, False
    for leaf_ast in ast.recursive_leaf_asts:
        if leaf_ast.op == 'BVS' and ('r' in leaf_ast.args[0] or 's' in leaf_ast.args[0]):
            is_reg = True

        elif leaf_ast.op == 'BVV':
            concret_scope = get_scope(leaf_ast.args[0])
            if concret_scope == 'global':
                is_global = True
            elif concret_scope == 'stack':
                is_stack = True

    if is_global and not is_reg and not is_stack:
        return 'global'

    elif is_reg and not is_global and not is_stack:
        return 'aptr'

    elif is_stack and not is_global and not is_reg:
        return 'stack'

    else:
        return None


def get_sim_action_scope(ast, sim_action_info):
    ast_id = ast.__hash__()
    return sim_action_info[ast_id] if ast_id in sim_action_info else None


def judge_ast_is_pointer(ast, sims, sim_action_info):
    # print("Analyze: %s" % (ast))
    if ast.op == 'BVS':
        ty = get_sim_scope(ast.args[0], sims)
        if ty:
            return ty

    elif ast.op == 'BVV':
         ty = get_scope(ast.args[0])
         if ty != 'imm':
             return ty

    elif ast.op in offset_ops:
        for child_ast in ast.args:
            if child_ast.op == 'BVS':
                ty = get_sim_scope(child_ast.args[0], sims)
                if ty == 'aptr':
                    return ty

            elif child_ast.op == 'BVV':
                ty = get_scope(child_ast.args[0])
                if ty != 'imm':
                    return ty

            elif child_ast.op in ls_ops:
                ls_ty = get_sim_action_scope(child_ast, sim_action_info)
                if ls_ty == 'ptr' or ls_ty is None:
                    ls_ty = judge_ast_is_pointer(child_ast, sims, sim_action_info)
                    if ls_ty:
                        return ls_ty

            elif child_ast.op in offset_ops:
                ty = judge_ast_is_pointer(child_ast, sims, sim_action_info)
                if ty:
                    return ty

    elif ast.op in ls_ops:
        ls_ty = judge_ls_base(ast)
        if ls_ty:
            return ls_ty

        else:
            ls_ty = judge_ast_is_pointer(ast.args[0], sims, sim_action_info)
            if ls_ty:
                return ls_ty


def get_expr_base_pointer_type(trace_expr):
    ast = trace_expr.expr.ast
    sims = trace_expr.expr.sims
    sim_actions = trace_expr.expr.sim_actions

    sim_action_info = {}
    for i, sim_action in sim_actions.items():
        action_id = sim_action.action_data.__hash__()
        sim_action_info[action_id] = sim_action.var_type
        # print("sim-action: %s" % (sim_action))

    base_scope = judge_ast_is_pointer(ast, sims, sim_action_info)

    return base_scope


def get_child_ast_type(ast, sims, sim_action_info):
    if ast.op == 'BVS':
        var = ast.args[0]
        if var in sims:
            return sims[var].var_type
        else:
            return basic_types['default']

    elif ast.op == 'BVV':
        return get_concrete_type(ast.args[0], ast.size())

    elif ast.op in ls_ops:
        ls_id = ast.__hash__()
        return sim_action_info[ls_id].var_type if ls_id in sim_action_info else None

    elif ast.op not in offset_ops:
        return basic_types['default']

    else:
        return None


# TODO
def infer_sim_action_type(ast, sims, sim_action_info, var_type):

    if ast.op == '__add__':
        if len(ast.args) == 2:
            arg1, arg2 = ast.args
            opnd1_ty = get_child_ast_type(arg1, sims, sim_action_info)
            opnd2_ty = get_child_ast_type(arg2, sims, sim_action_info)

            if opnd2_ty and opnd2_ty != 'ptr' and opnd1_ty is None:
                if arg1.op in ls_ops:
                    ls_id = arg1.__hash__()
                    sim_action_info[ls_id].var_type = var_type

    elif ast.op == '__sub__':
        op, opnds_type = '-', []
        if len(ast.args) == 2:
            ty = get_child_ast_type(child_ast, sims, sim_action_info)
            opnds_type.append(ty)

    elif ast.op in ls_ops:
        ast_id = ast.__hash__()
        sim_action_info[ast_id].var_type = var_type


def reset_sim_action_type(trace_expr, var_type):
    ast = trace_expr.expr.ast
    sims = trace_expr.expr.sims
    sim_actions = trace_expr.expr.sim_actions
    sim_action_info = {}

    for i, sim_action in sim_actions.items():
        action_id = sim_action.action_data.__hash__()
        sim_action_info[action_id] = sim_action
        # print("sim-action: %s" % (sim_action))

    infer_sim_action_type(ast, sims, sim_action_info, var_type)


def get_sim_type(block, var):
    var_type = None
    if 'r' in var:
        for pre_block in block.predecessors:
            if var in pre_block.live_defs:
                var_type = pre_block.live_defs[var].var_type
                if var_type:
                    break

    else:
        var_type = block.live_defs[var].var_type

    return var_type


def get_opnds_type(block, opnds_info, var_type=None):
    sim_types = {}
    should_revision = False
    opnds, opnds_type = opnds_info[1], opnds_info[3]
    for opnd, opnd_type in zip(opnds, opnds_type):
        if opnd_type:
            sim_types[opnd] = opnd_type

        else:
            v_type = get_sim_type(block, opnd)
            sim_types[opnd] = v_type

            if v_type is None:
                should_revision = True

    if var_type and should_revision:
        revision_opnds_type(opnds_info, sim_types, var_type)

    return sim_types


def revision_opnds_type(opnds_info, sim_types, var_type):
    print("Revision-type: opnds: %s sim_types: %s, var_type: %s" % (str(opnds_info), sim_types, var_type))
    op, opnds_size = opnds_info[0], opnds_info[2]
    opnd1, opnd2 = opnds_info[1]
    opnd1_type, opnd2_type = sim_types[opnd1], sim_types[opnd2]

    if opnd1_type and opnd2_type:
        return

    if op == '+':
        if var_type == 'ptr':
            if opnd1_type is None and (opnd2_type and opnd2_type != 'ptr'):
                sim_types[opnd1] = 'ptr'

            elif opnd2_type is None and (opnd1_type and opnd1_type != 'ptr'):
                sim_types[opnd2] = 'ptr'

            else:
                # hypothesis: if type of 'op1 + op2' is ptr, then op1 is ptr
                # and op2 is int.
                sim_types[opnd1] = 'ptr'
                sim_types[opnd2] = basic_types[opnds_size[1]]

        else:
            if opnd1_type is None:
                sim_types[opnd1] = basic_types[opnds_size[0]]

            if opnd2_type is None:
                sim_types[opnd2] = basic_types[opnds_size[1]]

    elif op == '-':
        if var_type == 'ptr':
            sim_types[opnd1] = 'ptr'
            sim_types[opnd2] = basic_types[opnds_size[1]]

        else:
            if opnd1_type == 'ptr' and opnd2_type is None:
                sim_types[opnd2] = 'ptr'

            if opnd1_type is None and opnd2_type == 'ptr':
                sim_types[opnd1] = 'ptr'

    else:
        if var_type and var_type != 'ptr':
            if opnd1_type is None:
                sim_types[opnd1] = basic_types[opnds_size[0]]

            if opnd2_type is None:
                sim_types[opnd2] = basic_types[opnds_size[1]]


def get_type_with_binop(block, opnds_info):
    """
    Calculate the opnds_info's type result.
    """
    op = opnds_info[0]
    sim_types = get_opnds_type(block, opnds_info)
    opnds_type = []
    for sim, ty in sim_types.items():
        opnds_type.append(ty)
    result_type = calculate_variable_type(op, opnds_type)
    return result_type


def get_ast_var_type(ast, sims):
    opnds_type = []
    if ast.op == '__add__':
        op = '+'
        for arg in ast.args:
            if arg.op == 'BVS':
                opnds_type.append(sims[arg.args[0]])

    elif ast.op == '__sub__':
        op = '-'
        for arg in ast.args:
            if arg.op == 'BVS':
                opnds_type.append(sims[arg.args[0]])

    if len(opnds_type) == 2:
        return calculate_variable_type(op, opnds_type)


def calculate_variable_type(op, opnds_type, default_type=None):
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

    elif op == '-':
        if opnd1_type == 'ptr' and opnd2_type == 'ptr' or opnd2_type == 'ptr':
            var_type = basic_types['default']

        elif opnd1_type == 'ptr' and (opnd2_type and opnd2_type != 'ptr'):
            var_type = 'ptr'

        elif opnd1_type and opnd1_type != 'ptr':
            var_type = basic_types['default']

        elif opnd1_type and opnd2_type:
            var_type = opnd1_type

    else:
        var_type = default_type

    return var_type


def infer_variable_type(cfg, block, opnds_info, var_type):
    """
    Infer each variable's type in opnds according the variable type.
    """
    # print("Infer variable type: %s with %s" % (opnds_info, var_type))
    op, opnds, opnds_size, opnds_type = opnds_info[0], opnds_info[1], opnds_info[2], opnds_info[3]
    opnd1, opnd2 = opnds
    opnd1_type, opnd2_type = opnds_type

    if op == '+':
        if var_type == 'ptr':
            if opnd1_type is None and (opnd2_type and opnd2_type != 'ptr'):
                update_variable_type(block, opnd1, 'ptr')

            elif opnd2_type is None and (opnd1_type and opnd1_type != 'ptr'):
                update_variable_type(block, opnd2, 'ptr')

        else:
            if opnd1_type is None:
                v_type = basic_types[opnds_size[0]]
                update_variable_type(block, opnd1, v_type)

            if opnd2_type is None:
                v_type = basic_types[opnds_size[1]]
                update_variable_type(block, opnd2, v_type)

    elif op == '-':
        if var_type == 'ptr':
            if opnd1_type is None:
                update_variable_type(block, opnd1, 'ptr')

            if opnd2_type is None:
                v_type = basic_types[opnds_size[1]]
                update_variable_type(block, opnd2, v_type)

        else:
            if opnd1_type == 'ptr' and opnd2_type is None:
                update_variable_type(block, opnd2, 'ptr')

            if opnd1_type is None and opnd2_type == 'ptr':
                update_variable_type(block, opnd1, 'ptr')


def update_pre_block_variable_type(block, reg, var_type):
    for pre_block in block.predecessors:
        live_defs = pre_block.live_defs
        if reg in live_defs:
            live_defs[reg].var_type = var_type


def update_block_variable_type(cfg, block, action):
    var_type = action.var_type
    reg_at = block.live_defs[action.src]
    if (reg_at.code_location.block_addr == block.addr and
            reg_at.code_location.stmt_idx > action.code_location.stmt_idx):
        update_pre_block_variable_type(block, action.src, var_type)

    else:
        reg_at.var_type = var_type


def update_variable_type(block, var, var_type):
    if type(var) is not str:
        return

    if 'r' in var:
        update_reg_var_type(block, var, var_type)

    else:
        block.live_defs[var].var_type = var_type


def update_reg_var_type(block, reg, var_type):
    # print("update-reg: %s" % (block))
    if reg not in block.live_defs:
        return

    reg_at = block.live_defs[reg]
    update_pre_block_variable_type(block, reg, var_type)

    if reg_at.code_location.block_addr != block.addr:
        reg_at.var_type = var_type
        # print("Lucky, set type (%s):\n %s" % (var_type, reg_at))


def update_action_var_type(cfg, action):
    var_type = action.var_type
    code_location = action.code_location
    block = cfg.get_node_by_addr(code_location.block_addr)
    # print("Update - %s" % (action))
    src, src_alias = action.src, action.src_alias

    if type(src) is str:
        if 't' in src:
            block.live_defs[src].var_type = var_type

        elif 'r' in src:
            update_reg_var_type(block, src, var_type)

    if type(src_alias) is tuple:
        infer_variable_type(cfg, block, src_alias, var_type)

    elif type(src_alias) is str and src_alias != src:
        if 't' in src_alias:
            block.live_defs[src_alias].var_type = var_type

        elif 'r' in src_alias:
            update_reg_var_type(block, src_alias, var_type)


def backward_trace_variable_type(function, block):
    cfg = function.cfg
    if cfg is None:
        return

    for var, action in block.live_defs.items():
        if action.action_type in ['w', 'wo']:
            if action.var_type is None:
                continue

            var_type = action.var_type
            def_loc = action.code_location
            curr_block = cfg.get_node_by_addr(def_loc.block_addr) if def_loc.block_addr != block.addr else block

            # print("reset %s with: %s" % (curr_block, action))

            if type(action.src) is str and 'r' in action.src:
                update_block_variable_type(cfg, curr_block, action)

            if action.src_alias:
                src_alias = action.src_alias
                if type(src_alias) is str and 'r' in src_alias:
                    update_block_variable_type(cfg, curr_block, action)

                elif type(src_alias) is tuple:
                    infer_variable_type(cfg, curr_block, src_alias, var_type)
