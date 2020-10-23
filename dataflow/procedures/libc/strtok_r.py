import claripy
import dataflow

# save_ptr = 'r1001'

class strtok_r(dataflow.SimProcedure):
    """
    char *strtok_r(char *s, const char *delim, char **save_ptr)
    """

    def run(self, s, delim, save_ptr):
        # s_at = self.get_reg_action(s)
        # if s_at and s_at.src == 0:
        #     s = 'r1001'

        if self.flow_dir == 'F' and self.purpose == 0:
            self.process_strtok_r(s, delim, save_ptr)
            return 0

        else:
            return 1

    def infer_type(self, s, delim, save_ptr):
        # print("infer type in strtok")
        live_defs = self.block.live_defs
        if s not in live_defs or live_defs[s].src != 0:
            self.set_strtok_ptr()
            self.label_variable_type(s, 'ptr')

        self.label_variable_type(delim, 'ptr')
        self.label_variable_type(save_ptr, 'ptr')
        self.label_return_type('ptr')

    # def _run_forward(self, s, delim, save_ptr):
    #     new_exprs = []
    #     killed_exprs = []
    #     ret_name = 'r%d' % (self.arch.ret_offset)
    #     for trace_expr in self.block.forward_exprs:
    #         trace_ast = trace_expr.expr.ast
    #         if (((s in trace_expr.expr.sims and trace_ast.op == 'BVS' ) or
    #                  (save_ptr in trace_expr.expr.sims and trace_ast.op == 'Store' and trace_ast.args[0].op == 'BVS')) and
    #                 not self.block.contain_exprs(trace_expr)):
    #             new_expr = trace_expr.replace(trace_ast, ret_name, rep_type='ptr')
    #             new_expr.expr.trace_dir = 'F'
    #             new_expr.index = 0
    #             new_exprs.append(new_expr)

    #         # if s != save_ptr and save_ptr in trace_expr.expr.sims and trace_ast.op == 'BVS':
    #         #     killed_exprs.append(trace_expr)

    #         elif ret_name in trace_expr.expr.sims:
    #             killed_exprs.append(trace_expr)

    #     for kill_expr in killed_exprs:
    #         self.block.forward_exprs.remove(kill_expr)

    #     if len(new_exprs):
    #         trace_expr = new_exprs[0]
    #         trace_ast = trace_expr.expr.ast
    #         s_ptr = claripy.BVS(save_ptr, trace_ast.size())
    #         save_data = claripy.Store(s_ptr, s_ptr.size())
    #         # new_expr = trace_expr.replace(trace_expr.expr.ast, save_data, rep_info=sim_types, rep_sim_actions=xx)
    #         new_expr = trace_expr.deep_copy()
    #         new_expr.expr.ast = save_data
    #         code_location = CodeLocation(self.block.addr, 0)
    #         code_location =
    #         new_expr.expr.initial_sims(var_type='ptr')
    #         new_expr.expr.initial_sim_actions(code_location, var_type='ptr')
    #         new_expr.expr.trace_dir = 'B'

    #         for pre_block in self.block.predecessors:
    #             last_index = len(pre_block.irsb.statements) if pre_block.irsb else 0
    #             new_expr.expr.kill_store_action_by_loc()
    #             new_expr.expr.flag &= 0xfeff
    #             new_expr.expr.taint_live = self.block.addr
    #             new_expr.index = last_index
    #             pre_block.backward_exprs.append(new_expr)

    #     for succ_block in self.block.successors:
    #         for new_expr in new_exprs:
    #             succ_block.forward_exprs.append(new_expr)
    #             # print("In-strtok, find %s" % (new_expr))

    #     return 0

    # def _run_backward(self, s, delim, save_ptr):
    #     return 1
