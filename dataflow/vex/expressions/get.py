from .base import SimIRExpr

class SimIRExpr_Get(SimIRExpr):
    def _execute(self):
        size = self.size_bytes(self._expr.type)
        size_in_bits = self.size_bits(self._expr.type)
        self.type = self._expr.type

        self.expr = self.state.se.BVS('r%d' %self._expr.offset, size*8, explicit_name=True)

        # if self.type.startswith('Ity_F'):
        #     self.expr = self.expr.raw_to_fp()
