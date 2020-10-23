import dataflow

class strcpy(dataflow.SimProcedure):
    """
    strcpy(char * destination, const char * source)
    """
    def run(self, dest, src):
        # print("run strcpy.")
        self.reg_taint_propagate(dest, src)
        return 1

    def infer_type(self, dest, src):
        # print("infer type in strcpy")
        self.label_variable_type(dest, 'ptr')
        self.label_variable_type(src, 'ptr')
