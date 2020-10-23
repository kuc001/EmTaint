
import dataflow

class memcmp(dataflow.SimProcedure):
    """
    memcmp(const char *str1, const char *str2, size_t n)
    """
    def run(self, str1, str2, n):
        return 1

    def infer_type(self, str1, str2, n):
        # print("infer type in memcmp")
        self.label_variable_type(str1, 'ptr')
        self.label_variable_type(str2, 'ptr')
        self.label_variable_type(n, 'N')
        self.label_return_type('N')
