from . import SimIRStmt
from .. import translate_irconst


class SimIRStmt_Exit(SimIRStmt):
    def __init__(self, stmt, state):
        SimIRStmt.__init__(self, stmt, state)

        self.guard = None
        self.target = None
        self.jumpkind = None

    def _execute(self):
        guard_irexpr = self._translate_expr(self.stmt.guard)
        self.guard = guard_irexpr.expr != 0

        # get the destination
        self.target = translate_irconst(self.state, self.stmt.dst)
        self.jumpkind = self.stmt.jumpkind
