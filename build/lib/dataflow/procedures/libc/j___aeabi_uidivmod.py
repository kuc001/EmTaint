
import dataflow
from dataflow.global_config import default_arguments, basic_types
from dataflow.parse_ast import BVS

class j___aeabi_uidivmod(dataflow.SimProcedure):
    """
    :return a % b
    """

    def run(self, a, b):
        print("libc execute j___aeabi_uidivmod in %s" % (self.block))

        # TODO in ARM, the mod return is saved in r1
        mod_ret = 'r%d' % default_arguments[1]
        default_type = basic_types['default']

        if self.flow_dir == 'F':
            pass

        elif self.flow_dir == 'B':
            new_exprs = []
            killed_exprs = []
            for trace_expr in self.block.backward_exprs:
                trace_sims = trace_expr.expr.sims
                if mod_ret in trace_sims:
                    data = BVS(a) % BVS(b)
                    sim_types = {a: default_type, b: default_type}
                    new_expr = trace_expr.replace(mod_ret, data, rep_type=default_type, rep_info=sim_types)
                    new_expr.expr.trace_dir = 'B'

                    killed_exprs.append(trace_expr)
                    new_exprs.append(new_expr)

            for kill_expr in killed_exprs:
                block.backward_exprs.remove(kill_expr)

            for pre_block in self.block.predecessors:
                for new_expr in new_exprs:
                    pre_block.backward_exprs.append(new_expr)

            return 1

    def infer_type(self, a, b):
        self.label_variable_type(a, 'N')
        self.label_variable_type(b, 'N')

        mod_ret = 'r%d' % default_arguments[1]
        self.label_return_type_v2(mod_ret, 'N')
