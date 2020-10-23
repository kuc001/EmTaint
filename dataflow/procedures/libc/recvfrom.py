
import dataflow
from dataflow.data_process import inital_source_arguments

class recvfrom(dataflow.SimProcedure):
    """
    recvfrom(int sockfd, void *buf, size_t len, int flags,
                 struct sockaddr *src_addr, socklen_t *addrlen)
    """

    def run(self, fd, buf, length, flags, src_addr, addrlen):
        # print("Get source recvfrom in %s" % (self.block))

        if self.block.exec_taint == 0 and self.purpose == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {fd: 'src', buf: 'dst', length: 'length'}
            self.initial_arguments_taint_source(describe)
            self.block.exec_taint = 1

        else:
            # print("Has initial before in %s" % (self.block))
            pass

        return 1

    def infer_type(self, fd, buf, length, flags, src_addr, addrlen):
        # print("infer type in recvfrom")
        self.label_variable_type(fd, 'N')
        self.label_variable_type(buf, 'ptr')
        self.label_variable_type(length, 'N')
        self.label_variable_type(flags, 'N')

        self.label_return_type('N')
