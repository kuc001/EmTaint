from . import SimIRStmt
from angr.errors import UnsupportedDirtyError

import logging
l = logging.getLogger("dataflow.vex.statements.dirty")
l.setLevel("INFO")

class SimIRStmt_Dirty(SimIRStmt):
    # Example:
    # t1 = DIRTY 1:I1 ::: ppcg_dirtyhelper_MFTB{0x7fad2549ef00}()
    def _execute(self):
        l.info("Unsupported dirty ...")
