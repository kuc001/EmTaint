import dataflow

class strstr(dataflow.SimProcedure):
    """
    char *strstr(const char *haystack, const char *needle)
    """

    def run(self, haystack, needle):
        # print("run strstr")
        if self.flow_dir == 'F' and self.purpose == 0:
            return self.taint_propagate_to_ret(haystack)

        else:
            return 1

    def infer_type(self, haystack, needle):
        # print("infer type in strstr")
        self.label_variable_type(haystack, 'ptr')
        self.label_variable_type(needle, 'ptr')
        self.label_return_type('ptr')
