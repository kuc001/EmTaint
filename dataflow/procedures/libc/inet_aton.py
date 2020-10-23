
import dataflow

class inet_aton(dataflow.SimProcedure):
    """
    int inet_aton(const char *cp, struct in_addr *inp)
    """
    def run(self, cp, inp):
        if self.flow_dir == 'F' and self.purpose == 0:
            # self.add_special_constraint(cp, cons_type=1, name='inet_aton')
            self.add_special_constraint_v2(cp, None, cons_type=1, name='inet_aton')
        return 1

    def infer_type(self, cp, inp):
        self.label_variable_type(cp, 'ptr')
        self.label_variable_type(inp, 'ptr')
        self.label_return_type('N')
