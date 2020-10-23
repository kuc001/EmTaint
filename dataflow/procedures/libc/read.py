
import dataflow
from dataflow.data_process import inital_source_arguments

class read(dataflow.SimProcedure):
    """
    ssize_t read(int fd, void *buf, size_t nbytes)
    """

    def run(self, fd, buf, nbytes):
        # print("Get source read in %s" % (self.block))

        if self.block.exec_taint == 0 and self.purpose == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {fd: 'src', buf: 'dst', nbytes: 'length'}
            self.initial_arguments_taint_source(describe)
            self.block.exec_taint = 1

        else:
            pass
            # print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, fd, buf, nbytes):
        # print("infer type in read")
        self.label_variable_type(fd, 'N')
        self.label_variable_type(buf, 'ptr')
        self.label_variable_type(nbytes, 'N')
        self.label_return_type("N")
