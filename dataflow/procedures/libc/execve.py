import dataflow
from dataflow.procedures.stubs.format_parser import FormatParser


class execve(FormatParser):
    """
    int execve(const char *filename, char *const argv[ ], char *const envp[ ])
    """

    def run(self, filename, argv, envp):
        if self.flow_dir == 'F' and self.purpose == 0:
            self._find_taint_propagate_argv(argv, end_flag=0)
        return 1

    def infer_type(self, filename, argv, envp):
        self.label_variable_type(filename, 'ptr')
        self.label_variable_type(argv, 'ptr')
        self.label_variable_type(envp, 'ptr')
        self.label_return_type('N')
