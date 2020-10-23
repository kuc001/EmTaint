#!/usr/bin python
import sys
import os

from idc import *
from idautils import *
from idaapi import *

from struct import pack
from ctypes import c_uint32, c_uint64
import subprocess
from collections import defaultdict
import json

base = get_imagebase()
plt_start, plt_end = 0, 0
segments = list(Segments())

dump_vtables = True
vtable_section_names = [".rodata",
    ".data.rel.ro",
    ".data.rel.ro.local",
    ".rdata"]


got_file = ""
blocks_record = {}
vtables_ptrs = set()

pure_virtual_addr = 0x7F8894 # libwx_gtk2u_core-3.1.so.0.0.0


# gives the number of allowed zero entries in the beginning of
# a vtable candidate
number_allowed_zero_entries = 2

is_linux = None
is_windows = None

# extracts all relocation entries from the ELF file
# (needed for vtable location heuristics)
def get_relocation_entries_gcc64(elf_file):

    relocation_entries = set()

    try:
        result = subprocess.check_output(
            ['readelf', '--relocs', elf_file])
    except:
        raise Exception("Not able to extract relocation entries.")

    for line in result.split('\n')[3:]:
        line = line.split()

        try:
            rel_offset = int(line[0], 16)
            relocation_entries.add(rel_offset)
        except:
            continue

    return relocation_entries


def data_xref(ea):
    return [x for x in DataRefsFrom(ea)]


def get_vptr_xref(address):
    vtable_ptr = None
    for curr_addr in data_xref(address):
        may_vptr = curr_addr
        if got_start <= curr_addr < got_end:
            may_vptr = Qword(curr_addr)

        if any(map(lambda x: SegStart(x) <= may_vptr <= SegEnd(x), vtable_sections)):
            # print("may_vptr: 0x%x" % (may_vptr))

            # This is a direct xref to vtable ptr.
            if (may_vptr in vtables_ptrs or
                    (may_vptr+16) in vtables_ptrs or
                    (may_vptr+8) in vtables_ptrs):
                vtable_ptr = may_vptr
                print("Find vptr 1: %x" % (vtable_ptr))
                break

            # This is a indirect xref to vtable ptr.
            else:
                ptr2data = Qword(may_vptr)
                if ptr2data in vtables_ptrs:
                    vtable_ptr = may_vptr
                    print("Find vptr 2: %x" % (vtable_ptr))

    return vtable_ptr

def get_plt_jmp_addr_gcc64(funcea):
    for ea in FuncItems(funcea):
        if (GetMnem(ea) == 'jmp' and GetOpType(ea, 0) == 2):
            for data in data_xref(ea):
                return Qword(data)
    return None

def test_jmp():
    ea = 0x404078
    print "OpTye: ", GetOpType(ea, 0)
    v_opnd1 = GetOperandValue(ea, 0)
    addr = GetFunctionAttr(v_opnd1, 0)
    if addr != BADADDR:
        print("Jmp function: 0x%x" % (addr))


def get_function_ptr(address, bb_info):
    for curr_addr in data_xref(address):
        # print("data xref: %x" % (curr_addr))
        # may_ptr = curr_addr
        if text_start <= curr_addr <= text_end:
            func_addr = GetFunctionAttr(curr_addr, 0)
            if func_addr == curr_addr:
                print("%x has func pointer: %x" % (address, func_addr))
                info = (address, func_addr, 'func_ptr')
                bb_info.append(info)

        elif got_start <= curr_addr < got_end:
            may_ptr = Qword(curr_addr)
            func_addr = may_ptr
            if plt_start <= may_ptr <= plt_end:
                func_addr = get_plt_jmp_addr_gcc64(may_ptr)

            if func_addr:
                if extern_start <= func_addr <= extern_end:
                    start_addr = GetFunctionAttr(func_addr, 0)
                    if func_addr == start_addr:
                        func_name = GetFunctionName(func_addr)
                        info = (address, func_name, 'ext_ptr')
                        bb_info.append(info)
                        print("%x has extern func: %x, %s" % (address, func_addr, func_name))
                    else:
                        extern_name = Name(func_addr)
                        info = (address, extern_name, 'ext_data')
                        bb_info.append(info)
                        print("%x has extern data: %x, %s" % (address, func_addr, extern_name))

                elif text_start <= func_addr <= text_end:
                    start_addr = GetFunctionAttr(func_addr, 0)
                    if func_addr == start_addr:
                        info = (address, func_addr, 'func_ptr')
                        bb_info.append(info)
                        print("%x has func pointer: %x" % (address, func_addr))

def generate_cg(funcea, block, func_info):
    bb_info = []
    find_switch = None
    ins_addrs = set()
    block_start, block_end = block.startEA, block.endEA
   	# find_switch = None
    # func_start = GetFunctionAttr(funcea, FUNCATTR_START)
    # func_end = GetFunctionAttr(funcea, FUNCATTR_END)
    ea = block_start
    ins_addrs.add(ea)
    while ea != BADADDR and ea < block_end:
        # print("Analysis: 0x%x" % (ea))
        mnem = GetMnem(ea)
        if mnem == 'call':
            v_opnd1 = GetOperandValue(ea, 0)
            if data_start <= v_opnd1 < data_end:
            	v_opnd1 = Qword(v_opnd1)
            # opnd1 = GetOpnd(ea, 0)
            addr = GetFunctionAttr(v_opnd1, 0)
            if addr != BADADDR:
                if plt_start <= addr <= plt_end:
                    # print("Call to addr: %x" % (addr))
                    func_addr = get_plt_jmp_addr_gcc64(addr)
                    # print("plt functon: 0x%x" % (func_addr))
                    if func_addr:
                        # func_info['call'].append((block_start, ea, func_addr))
                        if extern_start <= func_addr <= extern_end:
                            func_name = GetFunctionName(func_addr)
                            func_info['call'].append((block_start, ea, func_name))
                            # print("Has extern func: %x, %s" % (func_addr, func_name))
                        else:
                            func_info['call'].append((block_start, ea, func_addr))

                # elif text_start <= addr <= text_end:
            	else:
                    func_info['call'].append((block_start, ea, addr))

            else:
                bb_info.append((ea, None, 'iCall'))

        elif mnem == 'jmp':
            opnd0_type = GetOpType(ea, 0)
            if opnd0_type == 7:
                v_opnd1 = GetOperandValue(ea, 0)
                addr = GetFunctionAttr(v_opnd1, 0)
                if addr != BADADDR and addr != funcea:
                    if plt_start <= addr <= plt_end:
                        func_addr = get_plt_jmp_addr_gcc64(addr)
                        if func_addr:
                            if extern_start <= func_addr <= extern_end:
                                func_name = GetFunctionName(func_addr)
                                func_info['call'].append((block_start, ea, func_name))

                            else:
                                func_info['call'].append((block_start, ea, func_addr))

                    elif text_start <= addr <= text_end:
                        func_info['call'].append((block_start, ea, addr))

            elif opnd0_type == 1:
                opnd1 = GetOpnd(ea, 0)
                bb_info.append((ea, None, 'iCall'))

            elif opnd0_type == 2:
            	find_switch = ea

        vtable_ptr = get_vptr_xref(ea)
        # print("vtable ptr: ", vtable_ptr)
        if vtable_ptr:
            bb_info.append((ea, vtable_ptr, 'xref_vptr'))

        get_function_ptr(ea, bb_info)

        ea = NextHead(ea)
        if ea in ins_addrs:
            break
        else:
            ins_addrs.add(ea)
    # print(call_edge)
    # if bb_info:
    #     blocks_record[block_start] = bb_info

    func_name = '%x' % (funcea)
    if func_name not in blocks_record:
        blocks_record[func_name] = {}

    if bb_info:
        blocks_record[func_name][block_start] = bb_info

    return find_switch

def generate_cg_ARM(funcea, block, func_info):
    bb_info = []
    find_switch = None
    ins_addrs = set()
    block_start, block_end = block.startEA, block.endEA
    ea = block_start
    ins_addrs.add(ea)

    while ea != BADADDR and ea < block_end:
        print("Analysis: 0x%x" % (ea))
        mnem = GetMnem(ea)
        if 'BL' in mnem and mnem[:2] == 'BL':
            v_opnd1 = GetOperandValue(ea, 0)
            # print('%x' % v_opnd1)
            addr = GetFunctionAttr(v_opnd1, 0)
            # print("addr: %x" % (addr))

            if addr != BADADDR and v_opnd1 == addr:
                if plt_start <= addr <= plt_end:
                    print("Call to addr (PLT): %x" % (addr))
                    func_name = GetFunctionName(addr)
                    func_info['call'].append((block_start, ea, func_name))
                    print("Has extern func: %x, %s" % (addr, func_name))

                elif text_start <= addr <= text_end:
                    print("Has a (%s Call) in 0x%x to 0x%x" % (mnem, ea, addr))
                    func_info['call'].append((block_start, ea, addr))

                elif extern_start <= addr <= extern_end:
                    func_name = GetFunctionName(addr)
                    func_info['call'].append((block_start, ea, func_name))
                    print("Has a (%s Extern call) in 0x%x to %s" % (mnem, ea, func_name))

            elif addr == BADADDR:
                opnd0 = GetOpnd(ea, 0)
                if opnd0 not in ['LR']:
                    print("Has a indirect (%s Call) in 0x%x" % (mnem, ea))
                    bb_info.append((ea, None, 'iCall'))

        elif mnem in ['B']:
            opnd0_type = GetOpType(ea, 0)
            if opnd0_type == 7:
                v_opnd1 = GetOperandValue(ea, 0)
                addr = GetFunctionAttr(v_opnd1, 0)
                if addr != BADADDR and addr != funcea:
                    if plt_start <= addr <= plt_end:
                        func_name = GetFunctionName(addr)
                        func_info['call'].append((block_start, ea, func_name))
                        print("Has a extern (%s Call) in 0x%x to %s" % (mnem, ea, func_name))

                    elif text_start <= addr <= text_end:
                        print("Has a (B Call) to 0x%x" % (addr))
                        func_info['call'].append((block_start, ea, addr))

                    elif extern_start <= addr <= extern_end:
                        func_name = GetFunctionName(addr)
                        func_info['call'].append((block_start, ea, func_name))
                        print("Has a (%s Extern call) in 0x%x to %s" % (mnem, ea, func_name))

            elif opnd0_type == 1:
                opnd1 = GetOpnd(ea, 0)
                bb_info.append((ea, None, 'iCall'))

            elif opnd0_type == 2:
            	find_switch = ea

        elif mnem in ['MOV', 'LDR']:
            opnd0 = GetOpnd(ea, 0)
            if opnd0 == 'PC':
                print("Find move icall in %x" % (ea))
                bb_info.append((ea, None, 'iCall'))

        vtable_ptr = get_vptr_xref(ea)
        # print("vtable ptr: ", vtable_ptr)
        if vtable_ptr:
            bb_info.append((ea, vtable_ptr, 'xref_vptr'))

        get_function_ptr(ea, bb_info)

        ea = NextHead(ea)
        if ea in ins_addrs:
            break
        else:
            ins_addrs.add(ea)

    func_name = '%x' % (funcea)
    if func_name not in blocks_record:
        blocks_record[func_name] = {}

    if bb_info:
        blocks_record[func_name][block_start] = bb_info

    return find_switch


def memory_accessible(addr):
    for segment in segments:
        if SegStart(segment) <= addr < SegEnd(segment):
            return True
    return False


# check the given vtable entry is valid
def check_entry_valid_gcc64(addr, qword):

    # is qword a pointer into the text section?
    ptr_to_text = (text_start <= qword < text_end)

    # is qword a function's start addr, not a loc_xxx?
    if ptr_to_text:
    	func_addr = GetFunctionAttr(qword, 0)
    	ptr_to_text = (qword == func_addr)
    	# if qword != func_addr:
    		# ptr_to_text = False

    # is qword a pointer to the extern section?
    ptr_to_extern = (extern_start <= qword < extern_end)

    # is qword a pointer to the plt section?
    ptr_to_plt = (plt_start <= qword < plt_end)

    # is the current entry a relocation entry
    # (means the value is updated during startup)
    # But ignore relocation entries that point to a vtable section
    # (relocated RTTI entries do that).
    is_relocation_entry = ((addr in relocation_entries)
        and not any(map(
        lambda x: SegStart(x) <= qword <= SegEnd(x), vtable_sections)))

    if (ptr_to_text
        or ptr_to_extern
        or ptr_to_plt
        or qword == pure_virtual_addr
        or is_relocation_entry):
        return True
    return False


# returns a dict with key = vtable address and value = set of vtable entries
def get_vtable_entries_gcc64(vtables_offset_to_top):

    global vtables_ptrs
    vtable_entries = dict()

    # get all vtable entries for each identified vtable
    for vtable_addr in vtables_offset_to_top.keys():

        curr_addr = vtable_addr
        curr_qword = Qword(curr_addr)
        entry_ctr = 0
        vtable_entries[vtable_addr] = list()
        vtables_ptrs.add(vtable_addr)

        # get all valid entries and add them as vtable entry
        # (ignore the first x zero entries)
        while (check_entry_valid_gcc64(curr_addr, curr_qword)
            or (entry_ctr < number_allowed_zero_entries and curr_qword == 0)):

            vtable_entries[vtable_addr].append(curr_qword)

            curr_addr += 8
            entry_ctr += 1
            curr_qword = Qword(curr_addr)

    return vtable_entries


# returns a dict with key = vtable address and value = offset to top
def get_vtables_gcc64():

    vtables_offset_to_top = dict()

    # is it preceded by a valid offset to top and rtti entry?
    # heuristic value for offset to top taken from vfguard paper
    def check_rtti_and_offset_to_top(rtti_candidate, ott_candidate, addr):
        ott_addr = addr - 16
        offset_to_top = ctypes.c_longlong(ott_candidate).value
        ott_valid = (-0xFFFFFF <= offset_to_top and offset_to_top <= 0xffffff)
        rtti_valid = (rtti_candidate == 0
            or (not text_start <= rtti_candidate < text_end
            and memory_accessible(rtti_candidate)))

        # offset to top can not be a relocation entry
        # (RTTI on the other hand can be a relocation entry)
        # => probably a vtable beginning
        ott_no_rel = (not ott_addr in relocation_entries)

        if ott_valid and rtti_valid and ott_no_rel:
            return True
        return False


    for vtable_section in vtable_sections:
        i = SegStart(vtable_section)
        qword = 0
        prevqword = 0

        while i <= SegEnd(vtable_section) - 8:

            pprevqword = prevqword
            prevqword = qword
            qword = Qword(i)

            # heuristic that we also find vtables that have a zero
            # entry as first entry (libxul.so has some of them which
            # are not abstract classes, so we have to find them)
            is_zero_entry = (qword == 0)

            # Could entry be a valid vtable entry?
            if check_entry_valid_gcc64(i, qword):

                # is it preceded by a valid offset to top and rtti entry?
                if check_rtti_and_offset_to_top(prevqword, pprevqword, i):

                    # extract offset to top value for this vtable
                    offset_to_top = ctypes.c_longlong(pprevqword).value
                    vtables_offset_to_top[i] = offset_to_top

                # skip succeeding function pointers of the vtable
                while (check_entry_valid_gcc64(i, qword)
                    and i < (SegEnd(vtable_section) - 8)):

                    i += 8
                    prevqword = qword
                    qword = Qword(i)

            # Allow the first x vtable entries to be a zero entry
            # and check if it is preceded by a valid
            # offset to top and RTTI entry
            elif (is_zero_entry
                and (i-16) >= SegStart(vtable_section)
                and check_rtti_and_offset_to_top(prevqword, pprevqword, i)):

                for j in range(1, number_allowed_zero_entries+1):

                    if (i+(j*8)) <= (SegEnd(vtable_section)-8):

                        nextqword = Qword(i+(j*8))

                        # skip if next entry is a zero entry
                        if nextqword == 0:
                            continue

                        # if entry is a valid vtable entry add it
                        if check_entry_valid_gcc64(i+(j*8), nextqword):

                            # extract offset to top value for this vtable
                            offset_to_top = ctypes.c_longlong(pprevqword).value
                            vtables_offset_to_top[i] = offset_to_top
                            break

                        # do not check further if it is an invalid vtable entry
                        else:
                            break

                    # break if we would check outside of the section
                    else:
                        break

            i += 8

    # Heuristic to filter out vtable candidates (like wrong candidates
    # because of the allowed 0 entries in the beginning):
    # If vtable + 8 or vtable + 16 is also considered a vtable,
    # check if they have Xrefs => remove candidates if they do not have Xrefs.
    # Same goes for wrongly detected vtables that reside before the actual
    # vtable.
    for vtable in list(vtables_offset_to_top.keys()):
        for i in range(1, number_allowed_zero_entries+1):
            if (vtable + i*8) in vtables_offset_to_top.keys():

                if not list(XrefsTo(vtable + i*8)):
                    if (vtable + i*8) in vtables_offset_to_top.keys():
                        del vtables_offset_to_top[(vtable + i*8)]
                    continue

                if not list(XrefsTo(vtable)):
                    if vtable in vtables_offset_to_top.keys():
                        del vtables_offset_to_top[vtable]
                    continue

    return vtables_offset_to_top

def process_function(function):
    dump = pack('<I', function - base)
    flow = FlowChart(get_func(function))
    assert len(dump) == 4

    block_dump, block_count = '', 0
    for block in flow:
        block_start = block.startEA
        block_end = block.endEA

        if plt_start <= block_start < plt_end:
            continue

        address, instruction_count = block_start, 0
        while address != BADADDR and address < block_end:
            instruction_count += 1
            address = NextHead(address)

        block_dump += pack('<I', block_start - base)
        block_dump += pack('<I', block_end - block_start)
        block_dump += pack('<H', instruction_count)

        block_count += 1

    dump += pack('<H', block_count)
    dump += block_dump
    return dump

def get_all_functions():

    global plt_start, plt_end, segments
    funcs = set()
    function_count = 0

    for segment in segments:
        permissions = getseg(segment).perm
        if not permissions & SEGPERM_EXEC:
            continue

        if SegStart(segment) == plt_start:
            continue

        print('\nProcessing segment %s.' % SegName(segment))
        for i, function in enumerate(Functions(SegStart(segment), SegEnd(segment))):
            funcs.add(function)

            # functions_dump += process_function(function)
            function_count += 1

            if i & (0x100 - 1) == 0 and i > 0:
                print('Function %d.' % i)

    print('\nExported %d functions.' % function_count)
    return funcs


def main():

    # save_path = ARGV[1]

    # DEBUG
    save_path = '/media/work/binary_info/'

    # Windows does only work if the image base is set to 0x0.
    if is_windows and get_imagebase() != 0x0:
        print("Image base has to be 0x0.")
        return

    global plt_start, plt_end, segments

    # for segment in segments:
    #     if SegName(segment) == '.plt':
    #         plt_start = SegStart(segment)
    #         plt_end = SegEnd(segment)
    #         break

    function_count = 0
    funcs = set()
    for segment in segments:
        permissions = getseg(segment).perm
        if not permissions & SEGPERM_EXEC:
            continue

        if SegStart(segment) == plt_start:
            continue

        print('\nProcessing segment %s.' % SegName(segment))
        for i, function in enumerate(Functions(SegStart(segment),
            SegEnd(segment))):

            funcs.add(function)

            function_count += 1

            if i & (0x100 - 1) == 0 and i > 0:
                print('Function %d.' % i)

    print('\nExported %d functions.' % function_count)

    # Export vtables.
    if dump_vtables:

        if is_linux:
            vtables_offset_to_top = get_vtables_gcc64()
            vtable_entries = get_vtable_entries_gcc64(vtables_offset_to_top)

        elif is_windows:
            vtables_offset_to_top = get_vtables_msvc64()
            vtable_entries = get_vtable_entries_msvc64(vtables_offset_to_top)

        else:
            raise Exception("Do not know underlying architecture.")

        # with open(GetInputFile() + '_vtables.txt', 'w') as f:

        #     # Write Module name to file.
        #     # NOTE: We consider the file name == module name.
        #     f.write("%s\n" % GetInputFile())

        #     for k in vtables_offset_to_top:
        #         f.write("%x %d" % (k, vtables_offset_to_top[k]))

        #         # write vtable entries in the correct order
        #         for vtbl_entry in vtable_entries[k]:
        #             f.write(" %x" % vtbl_entry)

        #         f.write("\n")

        print('\nExported %d vtables.' % len(vtables_offset_to_top))

    # Export .cfg entries.
    cfg_record = {}
    generate_cfg(cfg_record, funcs)
    # print(cfg_record)
    # json.dump(cfg_record, open(save_path + file_name + '_cfg.json', 'w'), indent=4)
    json.dump(cfg_record, open(save_path + file_name + '_cfg.json', 'w'), indent=4)
    json.dump(blocks_record, open(save_path + file_name + '_block_info.json', 'w'), indent=4)
    # json.dump(cfg_record, open(GetInputFile() + '_cfg.json', 'w'))
    # json.dump(blocks_record, open(GetInputFile() + '_block_info.json', 'w'))
    print('\nExported cfg and block data entries.')


def run_debug():

    global file_name, work_path

    funcs = get_all_functions()
    cfg_record = {}
    generate_cfg(cfg_record, funcs)
    print("cfg record:\n%s" % (cfg_record))
    print("block record:\n%s" % (blocks_record))


def import_got(target_file):
    fp = open(target_file)
    for line in fp.readlines():
        print(line)


def generate_cg_bak():
    cg_record = {}
    # register_list = GetRegisterList()
    # print register_list
    # print Functions()
    # for funcea in Functions():
    for funcea in [0x5f25d0]:
        func_start = GetFunctionAttr(funcea, 0)
        func_end = GetFunctionAttr(funcea, 4)
        call_edge = []
        for ea in FuncItems(funcea):
            ins = GetDisasm(ea)
            mnem = GetMnem(ea)
            if mnem == 'call':
                v_opnd1 = GetOperandValue(ea, 0)
                opnd1 = GetOpnd(ea, 0)
                # print ins, opnd1, v_opnd1
                addr = GetFunctionAttr(v_opnd1, 0)
                if addr != BADADDR:
                    call_edge.append((ea, addr, 'Call'))
                    # print addr
                else:
                    call_edge.append((ea, opnd1, 'iCall'))
            elif mnem == 'jmp':
                v_opnd1 = GetOperandValue(ea, 0)
                opnd1 = GetOpnd(ea, 0)
                # print ins, opnd1, v_opnd1
                if 'loc' in opnd1 or '*' in opnd1:
                    continue
                else:
                    addr = GetFunctionAttr(v_opnd1, 0)
                    if addr != BADADDR and addr != funcea:
                        # print 'addr: ', addr
                        call_edge.append((ea, addr, 'Call'))
                    else:
                        call_edge.append((ea, opnd1, 'iCall'))
        cg_record[funcea] = call_edge
    # print cg_record

def generate_cfg_bak2(cfg_record, funcs):
    node_list = []
    ea = SegByBase(SegByName(".text"))
    # for funcea in [0x25a9c0]:
    for funcea in Functions(SegStart(ea), SegEnd(ea)):
        func_info = {'block': [], 'jmp': [], 'call': []}
        node_record = set()
        func = idaapi.get_func(funcea)
        fc = idaapi.FlowChart(func)
        init_block = fc[0]
        node_list.append(init_block)
        node_record.add(init_block.startEA)
        func_info['block'].append((init_block.startEA, init_block.endEA))

        while node_list:
            n = node_list.pop()
            generate_cg(funcea, n, func_info)
            # print n, '0x%x 0x%x' % (n.startEA, n.endEA)
            for succ_bl in n.succs():
                if plt_start <= succ_bl.startEA <= plt_end:
                    continue
                if succ_bl.startEA in funcs:
                    continue
                func_info['jmp'].append((n.startEA, succ_bl.startEA))
                if succ_bl.startEA not in node_record:
                    node_record.add(succ_bl.startEA)
                    node_list.append(succ_bl)
                    func_info['block'].append((succ_bl.startEA, succ_bl.endEA))
                    # print("Add block (%x %x)" % (succ_bl.startEA, succ_bl.endEA))

        funcea_name = '%x' % funcea
        cfg_record[funcea_name] = func_info

def generate_cfg(cfg_record, funcs):
    node_list = []
    ea = SegByBase(SegByName(".text"))
    # for funcea in [0x65f0]:
    for funcea in Functions(SegStart(ea), SegEnd(ea)):
        # print("funcea: %x" % (funcea))
        # continue
        func_info = {'block': [], 'jmp': [], 'call': []}
        node_record = set()
        function_name = GetFunctionName(funcea)
        func_info['name'] = function_name

    	flow = FlowChart(get_func(funcea))
        for block in flow:
        	func_info['block'].append((block.startEA, block.endEA))

        	# find_switch = generate_cg(funcea, block, func_info)
        	find_switch = generate_cg_ARM(funcea, block, func_info)

        	succ_blocks = set()
        	for succ_block in block.succs():
        		succ_blocks.add(succ_block)

        	if len(succ_blocks) == 0:
        		if find_switch is not None:
        			switch_targets = resolve_switch(find_switch)
        			for switch_target in switch_targets:
        				func_info['jmp'].append((block.startEA, switch_target))

        	else:
        		for succ_block in succ_blocks:
        			func_info['jmp'].append((block.startEA, succ_block.startEA))

        funcea_name = '%x' % funcea
        cfg_record[funcea_name] = func_info


def test_path():
    global work_path
    print("work path: %s" % (work_path))


def resolve_switch(ea):
	ins = GetDisasm(ea)

	mnem = GetMnem(ea)

	opnd1 = GetOpnd(ea, 0)

	opnd_value = GetOperandValue(ea, 0)

	switch_targets = set()
	if mnem == 'jmp' and ('*' in opnd1 and 'ds' in opnd1):
		# print("%x %s" % (ea, ins))
		# return
		if any(map(lambda x: SegStart(x) <= opnd_value <= SegEnd(x), vtable_sections)):
			print("%x %s" % (ea, ins))
			xref_falg = False
			addr = opnd_value
			while True:
				r_value = Qword(addr)
				if text_start <= r_value < text_end:
					switch_targets.add(r_value)
					# print("Find loc_%x" % (r_value))
					addr += 8
					for xref in XrefsTo(addr, 0):
						xref_falg = True
						# print xref.type, XrefTypeName(xref.type), 'from', hex(xref.frm), 'to', hex(xref.to)
						break

					if xref_falg:
						break

				else:
					break

	for target in switch_targets:
		print("switch_target: %x" % (target))
	return switch_targets


def resolve_call_target(ea):
	mnem = GetMnem(ea)

	opnd1 = GetOpnd(ea, 0)

	opnd_value = GetOperandValue(ea, 0)

	print("%s" % (opnd1))
	print("%x" % (opnd_value))

	if data_start <= opnd_value < data_end:
		qdata = Qword(opnd_value)
		print("%x" % (qdata))


file_name = GetInputFile()
file_path = GetInputFilePath()
# work_path = os.path.dirname(file_path)

info = get_inf_structure()
# if not info.is_64bit():
#     raise Exception("Only 64 bit architecture is supported.")

if info.ostype == idc.OSTYPE_WIN and info.filetype == 11:
    is_windows = True
    is_linux = False
elif info.ostype == 0 and info.filetype == 18:
    is_windows = False
    is_linux = True
else:
    raise Exception("OS type not supported.")

# global variables that are needed for multiple C++ algorithms
if dump_vtables:
    extern_seg = None
    extern_start = 0
    extern_end = 0
    text_seg = None
    text_start = 0
    text_end = 0
    plt_seg = None
    plt_start = 0
    plt_end = 0
    got_seg = None
    got_start = 0
    got_end = 0
    idata_seg = None
    idata_start = 0
    idata_end = 0
    data_seg = None
    data_start = 0
    data_end = 0
    vtable_sections = list()
    for segment in segments:
        if SegName(segment) == "extern":
            extern_seg = segment
            extern_start = SegStart(extern_seg)
            extern_end = SegEnd(extern_seg)
        elif SegName(segment) == ".text":
            text_seg = segment
            text_start = SegStart(text_seg)
            text_end = SegEnd(text_seg)
        elif SegName(segment) == ".plt":
            plt_seg = segment
            plt_start = SegStart(plt_seg)
            plt_end = SegEnd(plt_seg)
        elif SegName(segment) == ".got":
            got_seg = segment
            got_start = SegStart(got_seg)
            got_end = SegEnd(got_seg)
        elif SegName(segment) == ".idata":
            idata_seg = segment
            idata_start = SegStart(idata_seg)
            idata_end = SegEnd(idata_seg)
        elif SegName(segment) == ".data":
                data_seg = segment
                data_start = SegStart(data_seg)
                data_end = SegEnd(data_seg)
        elif SegName(segment) in vtable_section_names:
            vtable_sections.append(segment)

    if is_linux:
        relocation_entries = get_relocation_entries_gcc64(GetInputFilePath())

    print("vtable sectons: %s" % (vtable_sections))

main()
# Exit(0)
