
import dataflow

class fdopen(dataflow.SimProcedure):
    """
    FILE *fdopen(int fd, const char *modes)
    """
    def run(self, fd, modes):
        r = 1
        if self.flow_dir == 'B' and self.purpose == 0:
            r = self.process_open_handle(fd, 0, 8)
        return r

    def infer_type(self, fd, modes):
        self.label_variable_type(fd, 'N')
        self.label_variable_type(modes, 'ptr')
        self.label_return_type('ptr')
