from . import SimIRStmt
from angr import sim_options as o


class SimIRStmt_Store(SimIRStmt):
    def _execute(self):
        # first resolve the address and record stuff
        addr = self._translate_expr(self.stmt.addr)

        # now get the value and track everything
        data = self._translate_expr(self.stmt.data)
        expr = data.expr.raw_to_bv()

        # Now do the store (if we should)
        if o.DO_STORES in self.state.options:
            self.state.memory.store(addr.expr, data.expr, action=None, endness=self.stmt.endness)
