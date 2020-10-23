
import dataflow

class fread(dataflow.SimProcedure):
    """
    size_t fread(void *ptr, size_t size, size_t n, FILE *stream)
    """

    def run(self, ptr, size, n, stream):
        if self.block.exec_taint == 0 and self.purpose == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {stream: 'src', ptr: 'dst', n: 'length', size: 'size'}
            self.initial_arguments_taint_source(describe)
            self.block.exec_taint = 1

        else:
            pass
            # print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, ptr, size, n, stream):
        self.label_variable_type(ptr, 'ptr')
        self.label_variable_type(size, 'N')
        self.label_variable_type(n, 'N')
        self.label_variable_type(stream, 'N')
        self.label_return_type('N')
