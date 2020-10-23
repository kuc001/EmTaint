
import dataflow

class fwrite(dataflow.SimProcedure):
    """
    size_t fwrite(const void *ptr, size_t size, size_t n, FILE *s)
    """
    def run(self, ptr, size, n, stream):
        return 1

    def infer_type(self, ptr, size, n, stream):
        # print("infer type in fwrite")
        self.label_variable_type(ptr, 'ptr')
        self.label_variable_type(stream, 'ptr')
        self.label_variable_type(size, 'N')
        self.label_variable_type(n, 'N')
        self.label_return_type('N')
