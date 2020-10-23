
class IDABlock(object):
    def __init__(self, addr,
                 block_end,
                 funcea,
                 ):
        self.addr = addr
        self.block_end = block_end
        self.funcea = funcea

        self.contain_blocks = []
        self.callsites = {}

    def __repr__(self):
        return "<IDABlock 0x%x (0x%x, 0x%x)>" % (self.funcea, self.addr, self.block_end)

    def __eq__(self, other):
        if not isinstance(other, IDABlock):
            return False
        return (self.addr == other.addr)

    def __hash__(self):
        return hash(self.addr)


class FuncNode(object):
    def __init__(self, addr):
        self.addr = addr
        self.forward_exprs = []
        self.backward_exprs = []
        self.done_exprs = []

    def __repr__(self):
        return "<FuncNode 0x%x>" % (self.addr)

    def __eq__(self, other):
        if not isinstance(other, FuncNode):
            return False
        return self.addr == other.addr

    def __hash__(self):
        return self.addr


class ExternFuncNode(object):
    def __init__(self, simprocedure_name, addr=0):
        self.addr = addr
        self.simprocedure_name = simprocedure_name
        self.forward_exprs = []
        self.backward_exprs = []
        self.done_exprs = []

    def __repr__(self):
        return "<ExternNode %s>" % (self.simprocedure_name)

    def __eq__(self, other):
        if not isinstance(other, ExternFuncNode):
            return False
        return hash(self.simprocedure_name) == hash(other.simprocedure_name)

    def __hash__(self):
        return hash(self.simprocedure_name)


class TmpNode(object):
    def __init__(self, addr):
        self.addr = addr
        self.forward_exprs = []
        self.backward_exprs = []
        self.done_exprs = []

    def __repr__(self):
        return "<TmpNode 0x%x>" % (self.addr)

    def __eq__(self, other):
        if not isinstance(other, TmpNode):
            return False
        return self.addr == other.addr

    def __hash__(self):
        return self.addr
