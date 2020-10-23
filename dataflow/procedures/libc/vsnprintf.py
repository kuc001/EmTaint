import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class vsnprintf(FormatParser):
    """
    int vsnprintf(char *s, size_t maxlen, const char *format, __gnuc_va_list arg)
    """

    def run(self, s, maxlen, format_ptr, arg_list):
        r = 1
        if self.flow_dir == 'F' and len(self.block.forward_exprs) and self.purpose == 0:
            self._parse(s, format_ptr)
            args = self.block.format_args
            print("vsnprintf has args: %s" % (args))
            self._find_taint_propagate_in_format_v4(s, arg_list, args, constraint=maxlen)
            r = 0

        return r


    def infer_type(self, s, maxlen, format_ptr, arg_list):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(maxlen, 'N')
        self.label_variable_type(format_ptr, 'ptr')
        self.label_variable_type(arg_list, 'ptr')
        self.label_return_type('N')
