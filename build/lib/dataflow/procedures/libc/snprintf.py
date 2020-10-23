import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class snprintf(FormatParser):
    """
    fprintf(char *s, size_t maxlen, const char *format, ...)
    """

    def run(self, s, maxlen, format_ptr):
        print("run snprintf.")
        r = 1
        if self.flow_dir == 'F':
            self._parse(s, format_ptr)
            args = self.block.format_args
            if args:
                print("snprintf has args: %s" % (args))
                r = self._find_taint_propagate_in_format_v1(s, args)

        return r

    def infer_type(self, s, maxlen, format_ptr):
        self.label_variable_type(s, 'ptr')
        self.label_return_type('N')
