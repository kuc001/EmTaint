
import dataflow

class fopen(dataflow.SimProcedure):
    """
    FILE *fopen(const char *filename, const char *modes)
    """
    def run(self, filename, modes):
        return 1

    def infer_type(self, filename, modes):
        self.label_variable_type(filename, 'ptr')
        self.label_variable_type(modes, 'ptr')
        self.label_return_type('N')
