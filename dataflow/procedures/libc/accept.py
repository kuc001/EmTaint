
import dataflow

class accept(dataflow.SimProcedure):
    """
    int accept(int fd, struct sockaddr *addr, socklen_t *addr_len)
    """
    def run(self, fd, addr, addr_len):
        r = 1
        if self.flow_dir == 'B' and self.purpose == 0:
            r = self.process_socket_handle(0x11)
        return r

    def infer_type(self, fd, addr, addr_len):
        self.label_variable_type(fd, 'N')
        self.label_variable_type(addr, 'ptr')
        self.label_variable_type(addr_len, 'ptr')
        self.label_return_type('N')
