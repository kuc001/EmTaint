
import dataflow
from dataflow.global_config import default_arguments, arch_info, basic_types
from dataflow.parse_ast import BVS

class strspn(dataflow.SimProcedure):
    """
    size_t strspn(const char *str1, const char *str2)
    """
    def run(self, str1, str2):
        if self.flow_dir == 'F':
            # TODO
            # self.find_str_length_taint(str1)
            return 1
        else:
            return 1

    def infer_type(self, str1, str2):
        self.label_variable_type(str1, 'ptr')
        self.label_variable_type(str2, 'ptr')
        self.label_return_type('N')
