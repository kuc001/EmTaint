import dataflow

class strdup(dataflow.SimProcedure):
    """
    char *strdup(const char *s)
    """

    def run(self, s):
        # print("run strdup")
        if self.flow_dir == 'F':
            return self.taint_propagate_to_ret(s)

        else:
            return 1

    def infer_type(self, s):
        # print("infer type in strdup")
        self.label_variable_type(s, 'ptr')
        self.label_return_type('ptr')
