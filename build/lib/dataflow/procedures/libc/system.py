import dataflow
from dataflow.data_collector import tainted_command_locs, weaks_command_exec

class system(dataflow.SimProcedure):
    """
    int system(const char *command)
    """

    def run(self, command):
        if self.flow_dir == 'F':
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast

                if trace_ast.op == 'BVS' and command in trace_sims:
                    print("Good, find taint in system! %s" % (self.block))
                    if trace_expr not in weaks_command_exec[self.block.addr]:
                        weaks_command_exec[self.block.addr].append(trace_expr)
                    # if self.block.addr not in tainted_command_locs:
                        # tainted_command_locs.append(self.block.addr)

        return 1

    def infer_type(self, command):
        self.label_variable_type(command, 'ptr')
        self.label_return_type('N')
