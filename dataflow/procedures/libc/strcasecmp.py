
import dataflow

class strcasecmp(dataflow.SimProcedure):
    """
    strcasecmp(const char *str1, const char *str2)
    """
    def run(self, str1, str2):
        if self.flow_dir == 'F' and self.purpose == 0:
            self.add_special_constraint_v2(str1, str2, cons_type=2, name='strcasecmp')
        return 1

    def infer_type(self, str1, str2):
        # print("infer type in strcasecmp")
        self.label_variable_type(str1, 'ptr')
        self.label_variable_type(str2, 'ptr')
        self.label_return_type('N')
