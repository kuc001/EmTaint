
import dataflow

class atoi(dataflow.SimProcedure):
    """
    int atoi(const char *nptr)
    """
    def run(self, nptr):
        # print("run atoi")
        r = 1
        if self.flow_dir == 'F' and self.purpose == 0:
            r = self.propagate_int_taint_to_ret(nptr, name='atoi', cons_type=4)
        elif self.flow_dir == 'B' and self.purpose == 1:
            r = self.check_backward_libc_return(ret_type=1)
        return r

    def infer_type(self, nptr):
        self.label_variable_type(nptr, 'ptr')
        self.label_return_type('N')
