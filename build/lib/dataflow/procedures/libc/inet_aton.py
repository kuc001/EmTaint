
import dataflow

class inet_aton(dataflow.SimProcedure):
    """
    int inet_aton(const char *cp, struct in_addr *inp)
    """
    def run(self, cp, inp):
        return 1

    def infer_type(self, cp, inp):
        self.label_variable_type(cp, 'ptr')
        self.label_variable_type(inp, 'ptr')
        self.label_return_type('N')
