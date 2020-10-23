import dataflow

class hdf_get_value(dataflow.SimProcedure):
    """
    char *hdf_get_value(entry, const char *name, flag)
    """

    def run(self, entry, name, flag):
        if self.flow_dir == 'F' and self.block.exec_taint == 0 and self.purpose == 0:
            print("Inital taint source in %s" % (self.block))
            describe = {name: 'src'}
            self.initial_ret_taint_source(describe)
            self.block.exec_taint = 1

        else:
            pass
            # print("Has initial before in %s" % (self.block))

        return 1

    def infer_type(self, entry, name, flag):
        self.label_variable_type(name, 'ptr')
        self.label_variable_type(entry, 'ptr')
        self.label_variable_type(flag, 'N')
        self.label_return_type('ptr')
