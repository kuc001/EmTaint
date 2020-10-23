import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser
from dataflow.data_collector import weaks_command_exec


class _system(FormatParser):
    """
    _system(char *command, ...)
    """

    def run(self, command):
        if self.flow_dir == 'F' and self.purpose == 0:
            for trace_expr in self.block.forward_exprs:
                trace_sims = trace_expr.expr.sims
                trace_ast = trace_expr.expr.ast
                flag = trace_expr.expr.flag

                if trace_ast.op == 'BVS' and flag & 0x100 and command in trace_sims:
                    print("Good, find taint in _system! %s" % (self.block))
                    self.block.is_tainted = 2
                    # if trace_expr not in weaks_command_exec[self.block.addr]:
                    weaks_command_exec[self.block.addr].append(trace_expr)

            self._parse(None, command)
            args = self.block.format_args
            if args:
                self._find_taint_propagate_in_format_v3(args)
        return 0

    def infer_type(self, command):
        self.label_variable_type(command, 'ptr')
