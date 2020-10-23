import dataflow

class config_get(dataflow.SimProcedure):
    """
    char* config_get(char* key)
    """

    def run(self, key):
        if self.flow_dir == 'F' and self.purpose == 0:
            self.nvram_get_value(key)

        return 1

    def infer_type(self, key):
        self.label_variable_type(key, 'ptr')
        self.label_return_type('N')
