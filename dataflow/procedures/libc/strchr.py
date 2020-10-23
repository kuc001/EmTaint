import dataflow

class strchr(dataflow.SimProcedure):
    """
    char *strchr(char *s, int c)
    """

    def run(self, s, c):
        # print("run strchr")
        if self.flow_dir == 'F' and self.purpose == 0:
            return self.taint_propagate_to_ret(s)

        else:
            return self._run_backward(s, c)

    def infer_type(self, s, c):
        # print("infer type in strchr")
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(c, 'N')
        self.label_return_type('ptr')

    def _run_backward(self, s, c):
        return 1
