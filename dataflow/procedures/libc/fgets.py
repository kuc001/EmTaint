
import dataflow

class fgets(dataflow.SimProcedure):
    """
    char *fgets(char *s, int n, FILE *stream)
    """

    def run(self, s, n, stream):
        # print("Get source fgets in %s" % (self.block))

        if self.block.exec_taint == 0 and self.purpose == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {stream: 'src', s: 'dst', n: 'length'}
            self.initial_arguments_taint_source(describe)
            self.block.exec_taint = 1

        else:
            pass
            # print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, s, n, stream):
        # print("infer type in fgets")
        self.label_variable_type(s, 'ptr')
        self.label_variable_type(stream, 'ptr')
        self.label_variable_type(n, 'N')
        self.label_return_type('ptr')
