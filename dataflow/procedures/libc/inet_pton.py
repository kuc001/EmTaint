
import dataflow

class inet_pton(dataflow.SimProcedure):
    """
    int inet_pton(int af, const char *cp, void *buf)
    """
    def run(self, af, cp, buf):
        if self.flow_dir == 'F' and self.purpose == 0:
            # self.add_special_constraint(cp, cons_type=1, name='inet_pton')
            self.add_special_constraint_v2(cp, None, cons_type=1, name='inet_pton')
        return 1

    def infer_type(self, af, cp, buf):
        self.label_variable_type(af, 'N')
        self.label_variable_type(cp, 'ptr')
        self.label_variable_type(buf, 'ptr')
        self.label_return_type('N')
