#!/usr/bin/env python
import claripy

# ro_region_names = ['.rodata', '.rdata', '.text', '.got']
code_region_names = ['.text']
ro_region_names = ['.rodata', '.rdata', '.got', '.init_array', '.plt']
rw_region_names = ['.data', '.data.rel.ro', '.data.rel.ro.local',]
bss_region_names = ['.bss', '.sbss']
choose_region_names = ro_region_names + rw_region_names + bss_region_names + code_region_names

struct_component = [0x3, 0x5, 0x7, 0x11, 0x13, 0x17, 0x19, 0x23, 0x29, 0x31, 37, 41]

simplify_ops = ['__add__', '__sub__', '__mul__']
atoms_ops = ['BVS', 'BVV']

basic_types = {
    1: 'bit',
    8: 'char',
    16: 'short',
    32: 'int',
    64: 'long',
    128: 'llong',
    25: 'float',
    53: 'double'
}

# uninitialized global variables, should initialized them before analyze binary.
section_regions = {}
argument_vars = []
arch_info = {}
default_arguments = []
fp_default_arguments = []
default_arg_names = []
default_stack_arg_names = ['s0', 's1', 's2', 's3']

# These ops are the claripy operators.
add_ops = ['__add__']
offset_ops = ['__add__', '__sub__']
# ignore_ops = ['Extract', 'Concat', 'ZeroExt', 'SignExt']
ignore_ops = []
shift_ops = ['__lshift__']
# shift_ops = ['__lshift__', '__rshift__']
simplify_ops = ['__add__', '__sub__', '__mul__']
ls_ops = ['Load', 'Store']


# These ops are the type 'pyvex.expr.Binop'.
complex_binops = []
simple_binops = []
ignore_binops = ['Iop_Sar64', 'Iop_Shr64']
add_binops = ['Iop_Add64']
sub_binops = ['Iop_Sub64']

# concrete_ops = claripy.operations.leaf_operations_concrete
leaf_operations = claripy.operations.leaf_operations


def initialize_global_config(proj):
    """
    Initialize all global variables which from the binary.
    """
    main_object = proj.loader.main_object

    # initial section regions
    for section in main_object.sections:
        region_name = section.name
        # start = section.vaddr
        # end = start + section.memsize
        # print("region_name: %s" % (region_name))
        if region_name in choose_region_names:
            start = section.vaddr
            end = start + section.memsize
            section_regions[region_name] = (start, end)
            print("section: %s %x - %x" % (region_name, start, end))

    min_addr, max_addr = proj.loader.min_addr, proj.loader.max_addr
    # if min_addr < 0x400000:
    #     min_addr = section_regions['.text'][1]
    section_regions['.loader'] = (min_addr, max_addr)

    extern_object = proj.loader.extern_object
    section_regions['.extern'] = (extern_object.min_addr, extern_object.max_addr)

    # initial argument vars
    arguments = proj.arch.argument_registers
    for o in arguments:
        argument_vars.append('r%d' % (o))

    arch_name = proj.arch.name
    if arch_name == 'AMD64':
        for arg in [72, 64, 32, 24, 80, 88]:
            default_arguments.append(arg)
        for arg in [224, 256, 288, 320, 352, 384, 416, 448]:
            fp_default_arguments.append(arg)

    elif arch_name == 'ARMEL':
        for arg in [8, 12, 16, 20]:
            default_arguments.append(arg)

    elif arch_name == 'MIPS64':
        for arg in [48, 56, 64, 72]:
            default_arguments.append(arg)

    elif arch_name == 'MIPS32':
        for arg in [24, 28, 32, 36]:
            default_arguments.append(arg)

    for i in default_arguments:
        arg_name = 'r%d' % (i)
        default_arg_names.append(arg_name)

    # initial architecture bits
    arch_info['bits'] = proj.arch.bits
    arch_info['ret'] = 'r%d' % (proj.arch.ret_offset)
    basic_types['default'] = basic_types[proj.arch.bits]

def initialize_global_config_with_default():
    section_regions = {
        'ro': (0xaaaaaaaa, 0xbbbbbbbb),
        'rw': (0xbbbbbbbb, 0xcccccccc),
        'bss': (0xcccccccc, 0xdddddddd),
    }

    arch_info = {
        'bits': 32,
    }
