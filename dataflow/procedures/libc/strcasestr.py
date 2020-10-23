import dataflow

class strcasestr(dataflow.SimProcedure):
    """
    char *strcasestr(const char *haystack, const char *needle)
    """

    def run(self, haystack, needle):
        # print("run strcasestr")
        if self.flow_dir == 'F' and self.purpose == 0:
            return self.taint_propagate_to_ret(haystack)

        else:
            return 1

    def infer_type(self, haystack, needle):
        # print("infer type in strcasestr")
        self.label_variable_type(haystack, 'ptr')
        self.label_variable_type(needle, 'N')
        self.label_return_type('ptr')
