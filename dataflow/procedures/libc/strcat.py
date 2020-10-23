import dataflow

class strcat(dataflow.SimProcedure):
    """
    char *strcat(char *dest, const char *src)
    """
    def run(self, dest, src):
        # print("run strcat.")
        if self.flow_dir == 'F' and self.purpose == 0:
            self.reg_taint_propagate(dest, src)
        return 1

    def infer_type(self, dest, src):
        self.label_variable_type(dest, 'ptr')
        self.label_variable_type(src, 'ptr')
        self.label_return_type('ptr')
