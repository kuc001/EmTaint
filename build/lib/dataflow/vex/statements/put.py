from . import SimIRStmt
from angr import sim_options as o

class SimIRStmt_Put(SimIRStmt):
    def _execute(self):
        # value to put
        data = self._translate_expr(self.stmt.data)

        # do the put (if we should)
        if o.DO_PUTS in self.state.options:
            self.state.registers.store(self.stmt.offset, data.expr, action=None)
