#!/usr/bin/env python

from .global_config import default_arg_names, default_stack_arg_names


def predict_parameter_pointer_in_backward(callsite):
    """
    In backward, the callsite's backward exprs should predict whether contain parameter ptrs.
    """
    parameter_ptrs = []
    context_info = {}
    backward_exprs = callsite.backward_exprs
    # live_defs = callsite.live_defs

    for pre_block in callsite.predecessors:
        # print("uuu- pre: %s" % (pre_block))
        live_defs = pre_block.live_defs
        for arg in default_arg_names:
            if arg in live_defs:
                arg_at = live_defs[arg]
                arg_alias = arg_at.src_alias if type(arg_at.src_alias) is str else arg_at.src
                context_info[arg_alias] = (arg, arg_at.var_type)
    print("callsite: %s has context: \n%s" % (callsite, context_info))

    for trace_expr in backward_exprs:
        trace_sims = trace_expr.expr.sims
        if len(trace_expr.expr.sim_actions) == 0:
            continue

        for var, sim in trace_sims.items():
            if var in context_info:
                arg, arg_type = context_info[var]
                if arg_type is None:
                    arg_type = sim.var_type

                if arg_type == 'ptr':
                    parameter_ptrs.append(arg)

    print("Get parameter_ptrs: %s" % (parameter_ptrs))
    return parameter_ptrs
