
import dataflow

class gethostbyname2(dataflow.SimProcedure):
    """
    struct hostent *gethostbyname2(const char *cp, int af)
    """
    def run(self, cp, af):
        if self.flow_dir == 'F' and self.purpose == 0:
            # self.add_special_constraint(cp, cons_type=1, name='gethostbyname2')
            self.add_special_constraint_v2(cp, None, cons_type=1, name='gethostbyname2')
        return 1

    def infer_type(self, cp, af):
        self.label_variable_type(cp, 'ptr')
        self.label_variable_type(af, 'N')
        self.label_return_type('ptr')
