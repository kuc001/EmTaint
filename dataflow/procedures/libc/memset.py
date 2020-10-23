import dataflow

class memset(dataflow.SimProcedure):
    """
    void *memset(void *s, int c, size_t n)
    """

    def run(self, s, c, n):
        # print("run memset")
        if self.flow_dir == 'F' and self.purpose == 0:
            killed_exprs = []
            for trace_expr in self.block.forward_exprs:
                sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast
                if trace_expr.expr.data_type == 'Tdata' and s in sims and trace_ast.op == 'BVS':
                    killed_exprs.append(trace_expr)

            for kill_expr in killed_exprs:
                self.block.forward_exprs.remove(kill_expr)

            return 0

        else:
            return 1

    def infer_type(self, s, c, n):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(c, 'N')
        self.label_variable_type(n, 'N')
