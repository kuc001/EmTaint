
import dataflow

class unlink(dataflow.SimProcedure):
    """
    int unlink(const char *name)
    """
    def run(self, name):
        return 1

    def infer_type(self, name):
        self.label_variable_type(name, 'ptr')
        self.label_return_type('N')
