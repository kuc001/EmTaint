
import dataflow
from dataflow.data_process import inital_source_arguments

class recv(dataflow.SimProcedure):
    """
    recv(int fd, void *buf, size_t n, int flags)
    """

    def run(self, fd, buf, length, flags):
        print("Get source recv in %s" % (self.block))

        if self.block.exec_taint == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {fd: 'src', buf: 'dst', length: 'length'}
            inital_source_arguments(self.block, describe)
            self.block.exec_taint = 1

        else:
            print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, fd, buf, length, flags):
        print("infer type in recvfrom")
        self.label_variable_type(fd, 'N')
        self.label_variable_type(buf, 'ptr')
        self.label_variable_type(length, 'N')
        self.label_variable_type(flags, 'N')

        self.label_return_type('N')
