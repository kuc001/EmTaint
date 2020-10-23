
import dataflow

class atol(dataflow.SimProcedure):
    """
    long atol(const char *nptr)
    """
    def run(self, nptr):
        print("run atol")
        r = 1
        if self.flow_dir == 'F':
            r = self.propagate_int_taint_to_ret(nptr, name='atol')
        return r

    def infer_type(self, nptr):
        self.label_variable_type(nptr, 'ptr')
        self.label_return_type('N')
