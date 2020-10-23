
import dataflow
from dataflow.global_config import default_arguments, arch_info, basic_types
from dataflow.parse_ast import BVS

class strlen(dataflow.SimProcedure):
    """
    strlen(const char *str)
    """
    def run(self, str_ptr):
        r = 1
        if self.flow_dir == 'F':
            r = self.propagate_int_taint_to_ret(str_ptr, name='strlen')
        return r

    def infer_type(self, str_ptr):
        # print("infer type in strlen.")
        self.label_variable_type(str_ptr, 'ptr')
        self.label_return_type('N')
