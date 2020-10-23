class CFGBlock(object):
    def __init__(self, addr,
                 cfg,
                 target=0,
                 irsb=None,
                 func_addr=None,
                 node_type=None):

        self.addr = addr
        self._cfg = cfg
        self.target = target
        self.irsb = irsb
        self.func_addr = func_addr
        self.node_type = node_type

        self.end = 0
        self.jumpkind = None
        self.is_loop = False

        # self.sp_tmp_offset = None
        self.stack_tmps = set()

        self.actions = {}
        self.code_locations = []
        self.live_defs = {}
        self.live_uses = {}
        self.live_stores = {}
        self.tmp_info = {}
        self.reg_defs = {}

        self.f_reg_alias = {}
        self.b_reg_alias = {}
        self.tmp_alias = {}

        self.stack_registers = {}

        self.forward_exprs = []
        self.backward_exprs = []
        self.done_exprs = []
        self.input_exprs = []
        self.traced_iids = set()

        self.callsite_exprs = []
        self.arg_ptr_alias = {}

        self.inc_info = {}

        self.constraints = []
        self.jump_guard = None
        self.guard = {}

        self.taint_constraints = {}

        # record the tainted tmp var in a block. In encryption may generate
        # much tainted tmp and causes memory consumption.
        self.taint_tmps = set()

        self.global_addrs = set()
        self.global_defs = set()

        self.exec_taint = 0

        self.analyzed_flag = 0

        self.format_args = None

        # The constraint type
        self.cons_type = 0

        self.is_tainted = 0

        self.has_callsite = 0
        self.icall_flag = 0

        """
        Record a block's state:
            0000 0001 : start block
            0000 0010 : end block
            0000 0100 : block is a callsite, contain context
        """
        self.special_flag = 0

    # private method

    def __repr__(self):
        if isinstance(self.target, int):
            if self.target:
                return "<Block 0x%x->0x%x (0x%x)>" % (self.addr, self.target, self.func_addr)

            else:
                return "<Block 0x%x (0x%x)>" % (self.addr, self.func_addr)

        elif isinstance(self.target, str):
            return "<Block 0x%x->%s (0x%x)>" % (self.addr, self.target, self.func_addr)

    def __eq__(self, other):
        if not isinstance(other, CFGBlock):
            return False
        return (self.addr == other.addr and self.target == other.target)

    def __hash__(self):
        return hash((self.addr, self.target))

    @property
    def successors(self):
        return self._cfg.get_successors(self)

    @property
    def predecessors(self):
        return self._cfg.get_predecessors(self)

    def get_block(self, addr):
        return self._cfg.get_node_by_addr(addr)

    # public method

    def print_backward_exprs(self, debug_type=0):
        for b_expr in self.backward_exprs:
            print("  -->(B%d-%x) %s" % (debug_type, self.addr, b_expr))

    def print_forward_exprs(self, debug_type=0):
        for f_expr in self.forward_exprs:
            print("  -->(B%d-%x) %s" % (debug_type, self.addr, f_expr))

    def print_trace_expr(self):
        print("DEBUG-trace-%x" % (self.addr))
        print("  --> backward-exprs:")
        for b_expr in self.backward_exprs:
            print("  %s 0x%x with-cons- %s ptr-id- %x source- %s alias_id- %s-%s"
                  % (b_expr, b_expr.expr.flag, b_expr.constraints, b_expr.expr.ptr_id, b_expr.expr.source, b_expr.expr.data_type, b_expr.expr.alias_id))

        print("\n  --> forward-exprs:")
        for fe in self.forward_exprs:
            print("  %s 0x%x with-cons- %s ptr-id- %x source- %s alias_id- %s-%s" %
                  (fe, fe.expr.flag, fe.constraints, fe.expr.ptr_id, fe.expr.source, fe.expr.data_type, fe.expr.alias_id))

    def shallow_copy(self):
        new_block = CFGBlock(self.addr, target=self.target, irsb=self.irsb, func_addr=self.func_addr, node_type=self.node_type)
        return new_block

    def collect_completed_exprs(self, expr):
        if expr not in self.done_exprs:
            self.done_exprs.append(expr)

    def contain_exprs(self, trace_expr):
        for input_expr in self.input_exprs:
            if input_expr == trace_expr and input_expr.expr.trace_dir == trace_expr.expr.trace_dir:
                return True

        self.input_exprs.append(trace_expr)
        # print("xxx->add %s" % (trace_expr))
        return False

    def judge_pointer_guard_forward(self, succ_block, trace_ptrs):
        if len(trace_ptrs) == 0:
            return True

        if self.addr not in succ_block.guard:
            return True

        guard = succ_block.guard[self.addr]
        arg0, arg1 = guard.args
        if guard.op == '__eq__' and arg0.op == 'BVS' and arg1.op == 'BVV' and arg1.args[0] == 0:
            var0 = arg0.args[0]
            if 't' in var0 and var0 in self.tmp_alias:
                for var in self.tmp_alias[var0]:
                    if var in trace_ptrs:
                        return False

            elif 'r' in var0 and var0 in trace_ptrs:
                return False
        return True

