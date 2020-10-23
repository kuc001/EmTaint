
import dataflow

class malloc(dataflow.SimProcedure):
    """
    void *malloc(size_t size)
    """
    def run(self, size):
        r = 1
        if self.flow_dir == 'B' and self.purpose == 0:
            r = self.update_with_heap(size)
        return r

    def infer_type(self, nptr):
        self.label_variable_type(nptr, 'ptr')
        self.label_return_type('ptr')
