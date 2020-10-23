import dataflow
from dataflow.data_collector import tainted_command_locs

class popen(dataflow.SimProcedure):
    """
    FILE *popen(const char *command, const char *modes)
    """

    def run(self, command, modes):
        if self.flow_dir == 'F':
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast

                if trace_ast.op == 'BVS' and command in trace_sims:
                    print("Good, find taint in popen! %s" % (self.block))
                    if self.block.addr not in tainted_command_locs:
                        tainted_command_locs.append(self.block.addr)

        return 1

    def infer_type(self, command, modes):
        self.label_variable_type(command, 'ptr')
        self.label_variable_type(modes, 'ptr')
        self.label_return_type('ptr')
