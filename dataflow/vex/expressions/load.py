from .base import SimIRExpr, _nonset
import claripy

from ...parse_ast import get_mem_permission


class SimIRExpr_Load(SimIRExpr):
    def _execute(self):
        # size of the load
        size = self.size_bytes(self._expr.type)
        self.type = self._expr.type

        # get the address expression and track stuff
        addr = self._translate_expr(self._expr.addr)

        load_flag = False
        if addr.expr.concrete:
            addr_valu = self.state.solver.eval(addr.expr)
            pm = get_mem_permission(addr_valu)
            # print("SimIRExpr_Load: 0x%x %s" % (addr_valu, pm))
            if pm == 'ro':
                self.expr = self.state.memory.load(addr.expr, size, endness=self._expr.endness)

            elif pm == 'rw':
                value = self.state.memory.load(addr.expr, size, endness=self._expr.endness)
                if value.concrete and value.args[0] > 0:
                    self.expr = value

                else:
                    load_flag = True

            else:
                load_flag = True

        else:
            load_flag = True

        if load_flag:
            self.expr = claripy.Load(addr.expr, size*8)

        # if self.type.startswith('Ity_F'):
        #     self.expr = self.expr.raw_to_fp()
