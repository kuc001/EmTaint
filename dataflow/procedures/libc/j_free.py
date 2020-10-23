import dataflow

class j_free(dataflow.SimProcedure):
    """
    j_free(void *ptr)
    """

    def run(self, ptr):
        if self.flow_dir == 'F':
            self.exec_free(ptr)

        return 0

    def infer_type(self, ptr):
        self.label_variable_type(ptr, 'ptr')
