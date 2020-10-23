from .base import SimIRExpr
from angr import sim_options as o
from angr.state_plugins.sim_action import SimActionData

class SimIRExpr_RdTmp(SimIRExpr):
    def _execute(self):
        if self._expr.tmp not in self.state.scratch.temps:
            self.expr = self.state.solver.BVS('t%d' % self._expr.tmp, self.size_bits(), explicit_name=True)
        else:
            self.expr = self.state.scratch.tmp_expr(self._expr.tmp)

        # finish it and save the tmp reference
        self._post_process()
        if o.TRACK_TMP_ACTIONS in self.state.options:
            r = SimActionData(self.state, SimActionData.TMP, SimActionData.READ, tmp=self._expr.tmp, size=self.size_bits(), data=self.expr)
            self.actions.append(r)
