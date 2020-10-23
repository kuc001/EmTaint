
import dataflow
from dataflow.global_config import default_arguments, arch_info, basic_types
from dataflow.parse_ast import BVS

class strspn(dataflow.SimProcedure):
    """
    size_t strspn(const char *str1, const char *str2)
    """
    def run(self, str1, str2):
        r = 1
        # if self.flow_dir == 'F' and self.purpose == 0:
        #     r = self.propagate_int_taint_to_ret(str1, name='strspn', cons_type=5)
        return r

    def infer_type(self, str1, str2):
        self.label_variable_type(str1, 'ptr')
        self.label_variable_type(str2, 'ptr')
        self.label_return_type('N')
