import dataflow

class gcgiFetchString(dataflow.SimProcedure):
    """
    gcgiFetchString(char *qstr, void *dest, size_t n)
    """

    def run(self, qstr, dest, n):
        print("run gcgiFetchString")
        if self.block.exec_taint == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {qstr: 'src', dest: 'dst', n: 'length'}
            self.initial_arguments_taint_source(describe)
            self.block.exec_taint = 1

        else:
            print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, qstr, dest, n):
        self.label_variable_type(qstr, 'ptr')
        self.label_variable_type(dest, 'ptr')
        self.label_variable_type(n, 'N')
