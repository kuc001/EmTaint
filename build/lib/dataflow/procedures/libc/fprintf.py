import dataflow

class fprintf(dataflow.SimProcedure):
    """
    fprintf(FILE *stream, const char *format, ...)
    """

    def run(self, stream, format):
        return 1

    def infer_type(self, stream, format):
        pass
