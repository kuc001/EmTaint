
import dataflow

class close(dataflow.SimProcedure):
    """
    int close(int fd)
    """
    def run(self, fd):
        return 1

    def infer_type(self, fd):
        self.label_variable_type(fd, 'N')
        self.label_return_type('N')
