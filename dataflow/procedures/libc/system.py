import dataflow
from dataflow.data_collector import weaks_command_exec

class system(dataflow.SimProcedure):
    """
    int system(const char *command)
    """

    def run(self, command):
        if self.flow_dir == 'F' and self.purpose == 0:
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast
                flag = trace_expr.expr.flag

                if trace_ast.op == 'BVS' and flag & 0x100 and command in trace_sims:
                    self.block.is_tainted = 2
                    weaks_command_exec[self.block.addr].append(trace_expr)
                    print("Good, find taint in system! %s %s 0x%x %d" % (self.block, trace_expr, trace_expr.expr.taint_source, len(trace_expr.inter_funcs)))

        return 1

    def infer_type(self, command):
        self.label_variable_type(command, 'ptr')
        self.label_return_type('N')
