
import dataflow

class setsockopt(dataflow.SimProcedure):
    """
    int setsockopt(int fd, int level, int optname, const void *optval, socklen_t optlen)
    """
    def run(self, fd, level, optname, optval, optlen):
        return 1

    def infer_type(self, fd, level, optname, optval, optlen):
        self.label_variable_type(fd, 'N')
        self.label_variable_type(level, 'N')
        self.label_variable_type(optname, 'N')
        self.label_variable_type(optval, 'ptr')
        self.label_return_type('N')
