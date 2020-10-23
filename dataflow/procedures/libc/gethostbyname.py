
import dataflow

class gethostbyname(dataflow.SimProcedure):
    """
    struct hostent *gethostbyname(const char *name)
    """
    def run(self, cp):
        if self.flow_dir == 'F' and self.purpose == 0:
            # self.add_special_constraint(cp, cons_type=1, name='gethostbyname')
            self.add_special_constraint_v2(cp, None, cons_type=1, name='gethostbyname')
        return 1

    def infer_type(self, cp):
        self.label_variable_type(cp, 'ptr')
        self.label_return_type('ptr')
