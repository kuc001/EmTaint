import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class sprintf(FormatParser):
    """
    sprintf(char *s, size_t maxlen, const char *format, ...)
    """

    def run(self, s, format_ptr):
        # print("run sprintf.")
        r = 1
        if self.flow_dir == 'F' and len(self.block.forward_exprs) and self.purpose == 0:
            self._parse(s, format_ptr)
            args = self.block.format_args
            # print("format args %s" % (args))
            # if args:
            self._find_taint_propagate_in_format_v1(s, args)
            r = 0
        return r

    def infer_type(self, s, format_ptr):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(format_ptr, 'ptr')
        self.label_return_type('N')
