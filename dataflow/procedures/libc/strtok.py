import dataflow

save_ptr = 'r1001'

class strtok(dataflow.SimProcedure):
    """
    char *strtok(char *s, const char *delim)
    Set the 'r1001' as SAVE_PTR
    """

    def run(self, s, delim):
        # print("run strtok")
        s_at = self.get_reg_action(s)
        if s_at and s_at.src == 0:
            s = 'r1001'

        if self.flow_dir == 'F' and self.purpose == 0:
            return self._run_forward(s, delim)

        else:
            return self._run_backward(s, delim)

    def infer_type(self, s, delim):
        # print("infer type in strtok")
        live_defs = self.block.live_defs
        if s not in live_defs or live_defs[s].src != 0:
            self.set_strtok_ptr()
            self.label_variable_type(s, 'ptr')

        self.label_variable_type(delim, 'ptr')
        self.label_return_type('ptr')

    def _run_forward(self, s, delim):
        new_exprs = []
        killed_exprs = []
        ret_name = 'r%d' % (self.arch.ret_offset)
        for trace_expr in self.block.forward_exprs:
            trace_ast = trace_expr.expr.ast
            if s in trace_expr.expr.sims and trace_ast.op == 'BVS' and not self.block.contain_exprs(trace_expr):
                new_expr = trace_expr.replace(trace_ast, ret_name, rep_type='ptr')
                new_expr.expr.trace_dir = 'F'
                new_expr.expr.ptr_id = self.block.addr
                new_expr.index = 0
                new_exprs.append(new_expr)

            if s != save_ptr and save_ptr in trace_expr.expr.sims and trace_ast.op == 'BVS':
                killed_exprs.append(trace_expr)

            elif ret_name in trace_expr.expr.sims:
                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            self.block.forward_exprs.remove(kill_expr)

        if len(new_exprs) and s != save_ptr:
            trace_expr = new_exprs[0]
            new_expr = trace_expr.replace(trace_expr.expr.ast, save_ptr, rep_type='ptr')
            new_expr.expr.trace_dir = 'F'
            new_expr.expr.ptr_id = self.block.addr
            new_expr.index = 0
            new_exprs.append(new_expr)

        for succ_block in self.block.successors:
            for new_expr in new_exprs:
                new_expr.taint_propagaton_level += 1
                succ_block.forward_exprs.append(new_expr)
                # print("In-strtok, find %s" % (new_expr))

        return 0

    def _run_backward(self, s, delim):
        return 1
