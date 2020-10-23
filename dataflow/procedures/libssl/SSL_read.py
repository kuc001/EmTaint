
import dataflow
from dataflow.data_process import inital_source_arguments

class SSL_read(dataflow.SimProcedure):
    """
    int SSL_read(SSL *ssl, void *buf, int num)
    """

    def run(self, ssl, buf, num):
        print("Get source SSL_read in %s" % (self.block))

        if self.block.exec_taint == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {ssl: 'src', buf: 'dst', num: 'length'}
            inital_source_arguments(self.block, describe)
            self.block.exec_taint = 1

        else:
            print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, ssl, buf, num):
        # print("infer type in SSL_read")
        self.label_variable_type(ssl, 'ptr')
        self.label_variable_type(buf, 'ptr')
        self.label_variable_type(num, 'N')
        self.label_return_type('N')
