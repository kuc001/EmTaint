from .base import SimIRExpr
import logging
l = logging.getLogger("SimIRExpr_GetI")
l.setLevel("INFO")

class SimIRExpr_GetI(SimIRExpr):
    def _execute(self):
        l.info("Has a GetI stmt: %s" % (self._expr))
        self.ix = self._translate_expr(self._expr.ix)  # pylint:disable=attribute-defined-outside-init
        size = self.size_bytes(self._expr.descr.elemTy)
        size_in_bits = self.size_bits(self._expr.descr.elemTy)
        self.type = self._expr.descr.elemTy
        self.array_base = self._expr.descr.base  # pylint:disable=attribute-defined-outside-init
        self.array_index = (self.ix.expr + self._expr.bias) % self._expr.descr.nElems  # pylint:disable=attribute-defined-outside-init
        self.offset = self.array_base + self.array_index*size  # pylint:disable=attribute-defined-outside-init

        # get it!
        self.expr = self.state.registers.load(self.offset, size)

        # if self.type.startswith('Ity_F'):
        #     self.expr = self.expr.raw_to_fp()
