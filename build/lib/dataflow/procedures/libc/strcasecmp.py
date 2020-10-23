
import dataflow

class strcasecmp(dataflow.SimProcedure):
    """
    strcasecmp(const char *str1, const char *str2)
    """
    def run(self, str1, str2):
        return 1

    def infer_type(self, str1, str2):
        print("infer type in strcasecmp")
        self.label_variable_type(str1, 'ptr')
        self.label_variable_type(str2, 'ptr')
        self.label_return_type('N')
