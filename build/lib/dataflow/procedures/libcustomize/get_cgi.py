import dataflow

class get_cgi(dataflow.SimProcedure):
    """
    char *get_cgi(const char *name)
    """

    def run(self, name):
        # print("run getenv")
        if self.flow_dir == 'F' and self.block.exec_taint == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {name: 'src'}
            self.initial_ret_taint_source(describe)
            self.block.exec_taint = 1

        else:
            print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, name):
        # print("infer type in getenv")
        self.label_variable_type(name, 'ptr')
        self.label_return_type('ptr')
