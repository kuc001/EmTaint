#!/usr/bin/env python

from dataflow.global_config import default_arguments, arch_info
import dataflow

class strsep(dataflow.SimProcedure):
    """
    strsep(char **stringp, const char *delim)
    :result: *stringp
    *stringp = *stringp + N
    """

    def run(self, stringp, delim):
        """
        In block forward_exprs, should have expr like 'store(r8)' in arm.
        'store(r8) = taint_ptr'
        """
        print("execute strsep in %s" % (self.block))
        ret_name = 'r%d' % (self.arch.ret_offset)

        new_forward_exprs = []
        killed_exprs = []

        for trace_expr in self.block.forward_exprs:
            trace_ast = trace_expr.expr.ast
            sim_actions = trace_expr.expr.sim_actions

            if (trace_ast.op == 'Store' and trace_ast.args[0].op == 'BVS' and stringp in trace_expr.expr.sims):
                # Add strsep return ptr to forward_exprs
                new_expr = trace_expr.replace(trace_ast, ret_name, rep_type='ptr')
                new_expr.expr.trace_dir = 'F'
                new_expr.index = 0
                new_forward_exprs.append(new_expr)
                print("In strsep, get new-expr: %s" % (new_expr))

                # Remove the store(r8) trace expr from forward_exprs
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        for succ_block in self.block.successors:
            for new_expr in new_forward_exprs:
                succ_block.forward_exprs.append(new_expr)

    def infer_type(self, stringp, delim):
        self.label_variable_type(stringp, 'ptr')
        self.label_variable_type(delim, 'N')
        self.label_return_type('ptr')
