from . import SimIRStmt
from angr import sim_options as o


class SimIRStmt_StoreG(SimIRStmt):
    def _execute(self):
        addr = self._translate_expr(self.stmt.addr)
        data = self._translate_expr(self.stmt.data)
        expr = data.expr.raw_to_bv()
        guard = self._translate_expr(self.stmt.guard)

        if o.DO_STORES in self.state.options:
            self.state.memory.store(addr.expr, expr, condition=guard.expr == 1, endness=self.stmt.end, action=None)
