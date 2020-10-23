import dataflow

class index(dataflow.SimProcedure):
    """
    char *index(const char *s, int c)
    """

    def run(self, s, c):
        if self.flow_dir == 'F' and self.purpose == 0:
            return self.taint_propagate_to_ret(s)

        else:
            return 1

    def infer_type(self, s, c):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(c, 'N')
        self.label_return_type('ptr')
