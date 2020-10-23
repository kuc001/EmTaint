#!/usr/bin/env python

from .global_config import default_arg_names, default_stack_arg_names


def predict_parameter_pointer_in_backward(callsite):
    """
    In backward, the callsite's backward exprs should predict whether contain parameter ptrs.
    <T-Expr <BV32 Load(Load(0x7fffffeb) + 0x8)> (2147483627) (ptr) (B-0)>
    """
    parameter_ptrs = []
    context_info = {}
    backward_exprs = callsite.backward_exprs
    # live_defs = callsite.live_defs

    for pre_block in callsite.predecessors:
        # print("uuu- pre: %s" % (pre_block))
        live_defs = pre_block.live_defs
        for arg in default_arg_names:
            get_context_alias_info(arg, context_info, live_defs)
    # print("callsite: %s has context: \n%s" % (callsite, context_info))

    for trace_expr in backward_exprs:
        trace_sims = trace_expr.expr.sims
        if len(trace_expr.expr.sim_actions) == 0:
            continue

        for var, sim in trace_sims.items():
            for alias, info in context_info.items():
                if type(alias) is tuple and alias[1] == var:
                    arg, arg_type = info
                    if arg_type is None:
                        arg_type = find_stack_var_type(var, trace_expr)

                    if arg_type == 'ptr' and arg not in parameter_ptrs:
                        parameter_ptrs.append(arg)

                elif alias == var:
                    arg, arg_type = context_info[var]
                    if arg_type is None:
                        arg_type = sim.var_type

                    if arg_type == 'ptr' and arg not in parameter_ptrs:
                        parameter_ptrs.append(arg)

    # print("Get parameter_ptrs: %s" % (parameter_ptrs))
    return parameter_ptrs

def find_stack_var_type(addr, trace_expr):
    """
    Find a stack variable's type by the sim_actoins, e.g., load(stack_addr)
    """
    sim_actions = trace_expr.expr.sim_actions
    for i, sim_action in sim_actions.items():
        action_data = sim_action.action_data
        # print(sim_action)
        if action_data.op == 'Load' and action_data.args[0].op == 'BVV' and action_data.args[0].args[0] == addr:
            return sim_action.var_type

def get_context_alias_info(arg, context_info, live_defs):
    """
    """
    if arg not in live_defs:
        return
    arg_at = live_defs[arg]
    # print("context-%s %s" % (arg, arg_at))
    arg_alias = arg_at.src_alias if type(arg_at.src_alias) is str else arg_at.src
    if type(arg_alias) is str:
        if 't' in arg_alias and arg_alias in live_defs:
            arg_alias = get_stack_load_addr(arg_alias, live_defs)
        if arg_alias:
            context_info[arg_alias] = (arg, arg_at.var_type)

    if type(arg_at.value) is int and arg_at.src_type == 'S':
        context_info[arg_at.value] = (arg, 'ptr')

def get_stack_load_addr(tmp, live_defs):
    """
    For the 'txx = Load(stack_addr)', the the load stack pointer.
    """
    tmp_at = live_defs[tmp]
    if tmp_at.action_type == 'wl' and tmp_at.addr_type == 'S' and type(tmp_at.addr_value) is int:
        # print("Stack-load-addr %x" % (tmp_at.addr_value))
        return ('*', tmp_at.addr_value)
