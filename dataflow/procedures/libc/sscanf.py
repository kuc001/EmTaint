import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class sscanf(FormatParser):
    """
    int sscanf(const char *s, const char *format, ...)
    """

    def run(self, s, format_ptr):
        r = 1
        if self.flow_dir == 'F' and len(self.block.forward_exprs) and self.purpose == 0:
            self._parse(s, format_ptr)
            args = self.block.format_args
            if args:
                # print("sscanf has args: %s" % (args))
                r = self._find_taint_propagate_in_format_v2(s, args)
        return r

    def infer_type(self, s, format_ptr):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(format_ptr, 'ptr')
        self.label_return_type('N')
