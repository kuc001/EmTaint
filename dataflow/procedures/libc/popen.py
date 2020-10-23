import dataflow
from dataflow.data_collector import weaks_command_exec

class popen(dataflow.SimProcedure):
    """
    FILE *popen(const char *command, const char *modes)
    """

    def run(self, command, modes):
        if self.flow_dir == 'F' and self.purpose == 0:
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast
                flag = trace_expr.expr.flag

                if trace_ast.op == 'BVS' and flag & 0x100 and command in trace_sims:
                    print("Good, find taint in popen! %s" % (self.block))
                    self.block.is_tainted = 2
                    # if trace_expr not in weaks_command_exec[self.block.addr]:
                    weaks_command_exec[self.block.addr].append(trace_expr)

        return 1

    def infer_type(self, command, modes):
        self.label_variable_type(command, 'ptr')
        self.label_variable_type(modes, 'ptr')
        self.label_return_type('ptr')
