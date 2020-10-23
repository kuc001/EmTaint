
import dataflow

class fork(dataflow.SimProcedure):
    """
    __pid_t fork(void)
    """
    def run(self):
        return 1

    def infer_type(self):
        self.label_return_type('N')
