
import dataflow

class fputs(dataflow.SimProcedure):
    """
    int fputs(char *s, FILE *stream)
    """

    def run(self, s, stream):
        return 1

    def infer_type(self, s, stream):
        # print("infer type in fputs")
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(stream, 'ptr')
        self.label_return_type('N')
