
import dataflow

class fopen(dataflow.SimProcedure):
    """
    FILE *fopen(const char *filename, const char *modes)
    """
    def run(self, filename, modes):
        r = 1
        # if self.flow_dir == 'B' and self.purpose == 0:
        #     r = self.process_open_handle(filename, 0, 8)
        return r

    def infer_type(self, filename, modes):
        self.label_variable_type(filename, 'ptr')
        self.label_variable_type(modes, 'ptr')
        self.label_return_type('N')
