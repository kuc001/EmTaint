import dataflow

class memcpy(dataflow.SimProcedure):
    """
    memcpy(void *dest, const void *src, size_t n)
    """

    def run(self, dest, src, n):
        # print("run memcpy")
        self.reg_taint_propagate(dest, src, constraint=n, copy_type=1)
        return 1

    def infer_type(self, dest, src, n):
        # print("infer type in memcpy(%s %s %s)" % (dest, src, n))
        self.label_variable_type(dest, 'ptr')
        self.label_variable_type(src, 'ptr')
        self.label_variable_type(n, 'N')
