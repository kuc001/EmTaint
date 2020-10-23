
import dataflow

class strncpy(dataflow.SimProcedure):

    def run(self, dest, src, n):
        # print("run strncpy")
        if self.flow_dir == 'F' and self.purpose == 0:
            self.reg_taint_propagate(dest, src, constraint=n)
        return 1

    def infer_type(self, dest, src, n):
        self.label_variable_type(dest, 'ptr')
        self.label_variable_type(src, 'ptr')
        self.label_variable_type(n, 'N')
