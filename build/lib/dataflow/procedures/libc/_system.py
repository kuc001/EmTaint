import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser
from dataflow.data_collector import tainted_command_locs, weaks_command_exec


class _system(FormatParser):
    """
    _system(char *command, ...)
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
                    #     tainted_command_locs.append(self.block.addr)

            self._parse(None, command)
            args = self.block.format_args
            if args:
                self._find_taint_propagate_in_format_v3(args)
                # if flag:
                #     if self.block.addr not in tainted_command_locs:
                #         if trace_expr not in weaks_command_exec[self.block.addr]:
                #             weaks_command_exec[self.block.addr].append(trace_expr)
                    # tainted_command_locs.append(self.block.addr)
        return 0

    def infer_type(self, command):
        self.label_variable_type(command, 'ptr')
