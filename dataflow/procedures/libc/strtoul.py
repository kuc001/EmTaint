
import dataflow

class strtoul(dataflow.SimProcedure):
    """
    unsigned __int32 strtoul(const char *nptr, char **endptr, int base)
    """
    def run(self, nptr, endptr, base):
        # print("run strtoul")
        r = 1
        if self.flow_dir == 'F' and self.purpose == 0:
            r = self.propagate_int_taint_to_ret(nptr, name='strtoul', cons_type=4)
        return r

    def infer_type(self, nptr, endptr, base):
        self.label_variable_type(nptr, 'ptr')
        self.label_variable_type(base, 'N')
        self.label_return_type('N')
