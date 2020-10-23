import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class printf(FormatParser):
    """
    int printf(const char *format, ...)
    """

    def run(self, format_ptr):
        return 1

    def infer_type(self, format_ptr):
        self.label_variable_type(format_ptr, 'ptr')
        self.label_return_type('N')
