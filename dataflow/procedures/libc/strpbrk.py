import dataflow

class strpbrk(dataflow.SimProcedure):
    """
    char *strpbrk(const char *s1, const char *s2)
    """
    def run(self, s1, s2):
        # print("execute strpbrk in %s" % (self.block))

        if self.flow_dir == 'F' and self.purpose == 0:
            return self.taint_propagate_to_ret(s1)

        else:
            return 1

    def infer_type(self, s1, s2):
        self.label_variable_type(s1, 'ptr')
        self.label_variable_type(s2, 'ptr')
        self.label_return_type('ptr')
