import claripy

class BinaryInfo(object):

    def __init__(self, project):
        self.proj = project

        self.state = self.proj.factory.blank_state()
        self.solver = claripy.Solver()

        # Initialize some property of arch
        self.arch_bits = self.proj.arch.bits
        self.arch_bytes = self.proj.arch.bytes
        self.ret_offset = self.proj.arch.ret_offset
        self.sp_offset = self.proj.arch.sp_offset
        self.bp_offset = self.proj.arch.bp_offset

        self.max_offset = self._get_max_reg_offset()

        self.arguments = self.proj.arch.argument_registers
        self.argument_vars = ['r%d' % o for o in self.arguments]

        self.sp_name = 'r%d' % (self.sp_offset)
        self.bp_name = 'r%d' % (self.bp_offset)
        self.ret_name = 'r%d' % (self.ret_offset)

        if 'MIPS' in self.proj.arch.name:
            self.gp_name = 'r%d' % (self.proj.arch.registers['gp'][0])
            self.base_stack_offset = 0x10
            self.t9_name = 'r%d' % (self.proj.arch.registers['t9'][0])
        else:
            self.gp_name = None
            self.base_stack_offset = 0
            self.t9_name = None

        self.base_stack = 0x7fffffff + self.base_stack_offset

        # These ops are the claripy operators.
        self.add_ops = ['__add__']
        self.offset_ops = ['__add__', '__sub__']
        # self.ignore_ops = ['Extract', 'Concat', 'ZeroExt', 'SignExt']
        self.ignore_ops = []
        self.shift_ops = ['__lshift__']
        # self.shift_ops = ['__lshift__', '__rshift__']
        self.simplify_ops = ['__add__', '__sub__', '__mul__']


        # These ops are the type 'pyvex.expr.Binop'.
        self.complex_binops = []
        self.simple_binops = []
        self.ignore_binops = ['Iop_Sar64', 'Iop_Shr64']
        self.add_binops = ['Iop_Add64']
        self.sub_binops = ['Iop_Sub64']

        # self.concrete_ops = claripy.operations.leaf_operations_concrete
        self.leaf_operations = claripy.operations.leaf_operations

        # Some insignificant symbol ast.
        self.insignificant_symbol = claripy.BVS("U", self.arch_bits, explicit_name=True)

        self.ignore_regs = self._get_ignore_regs()

    def _get_ignore_regs(self):

        ignore_registers = ['cc_op', 'cc_dep1', 'cc_dep2', 'cc_ndep', 'rip', 'ip']

        ignore_reg_offsets = []
        for reg in ignore_registers:
            if reg not in self.proj.arch.registers:
                continue
            reg_offset = self.proj.arch.registers[reg][0]
            ignore_reg_offsets.append(reg_offset)

        return ignore_reg_offsets

    def _get_max_reg_offset(self):
        arch_name = self.proj.arch.name
        if arch_name == 'MIPS64':
            self.max_offset = 0x200

        elif arch_name == 'ARMEL' or arch_name == 'AMD64':
            self.max_offset = self.proj.arch.registers['cc_op'][0]

        else:
            self.max_offset = 0x200
