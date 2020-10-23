import dataflow

class config_set(dataflow.SimProcedure):
    """
    config_set(char* key, char* value)
    """

    def run(self, key, value):
        if self.flow_dir == 'F' and self.purpose == 0:
            self.nvram_set_value(key, value)

        return 0

    def infer_type(self, key, value):
        self.label_variable_type(key, 'ptr')
        self.label_variable_type(value, 'ptr')
