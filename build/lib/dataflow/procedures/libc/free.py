import dataflow

class free(dataflow.SimProcedure):
    """
    int free(void *ptr)
    """

    def run(self, ptr):
        return 1

    def infer_type(self, ptr):
        self.label_variable_type(ptr, 'ptr')
