
import dataflow

class atoi(dataflow.SimProcedure):
    """
    int atoi(const char *nptr)
    """
    def run(self, nptr):
        print("run atoi")
        r = 1
        if self.flow_dir == 'F':
            r = self.propagate_int_taint_to_ret(nptr, name='atoi')
        return r

    def infer_type(self, nptr):
        self.label_variable_type(nptr, 'ptr')
        self.label_return_type('N')
