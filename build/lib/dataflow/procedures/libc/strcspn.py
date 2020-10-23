import dataflow

class strcspn(dataflow.SimProcedure):
    """
    size_t strcspn(const char *s, const char *reject)
    """
    def run(self, s, reject):
        return 1

    def infer_type(self, s, reject):
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(reject, 'ptr')
        self.label_return_type('N')
