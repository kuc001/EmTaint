import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class vsnprintf(FormatParser):
    """
    int vsnprintf(char *s, size_t maxlen, const char *format, __gnuc_va_list arg)
    """

    def run(self, s, maxlen, format_ptr, arg_list):
        return 1
        # if not self.has_trace_expr():
        #     return 1
        # r = self._parse(s, format_ptr)
        # return r

    def infer_type(self, s, maxlen, format_ptr, arg_list):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(maxlen, 'N')
        self.label_variable_type(format_ptr, 'ptr')
        self.label_variable_type(arg_list, 'ptr')
        self.label_return_type('N')
