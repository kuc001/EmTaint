import dataflow


class exit(dataflow.SimProcedure):
    """
    void __noreturn exit(int status)
    """

    def run(self, status):
        self.block.backward_exprs.clear()
        self.block.forward_exprs.clear()
        return 0

    def infer_type(self, status):
        self.label_variable_type(status, 'N')
