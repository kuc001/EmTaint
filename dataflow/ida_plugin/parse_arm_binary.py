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

dump_vtables = False
vtable_section_names = [".rodata",
    ".data.rel.ro",
    ".data.rel.ro.local",
    ".rdata"]


got_file = ""
vtables_ptrs = set()
data_xref_addrs = {}

pure_virtual_addr = 0x7F8894 # libwx_gtk2u_core-3.1.so.0.0.0


# gives the number of allowed zero entries in the beginning of
# a vtable candidate
number_allowed_zero_entries = 2

is_linux = None
is_windows = None


def data_xref_from(ea):
    return [x for x in DataRefsFrom(ea)]

def data_xref_to(ea):
    return [x for x in DataRefsTo(ea)]

def collect_data_xref_to(xref_addrs, xref_type=None):
    for xref_addr, data in xref_addrs.items():
        if xref_type == 'func' and not is_code_region(xref_addr):
            continue

        if xref_addr not in data_xref_addrs:
            data_xref_addrs[xref_addr] = data

def is_code_region(addr):
    if sections['.text'][0] <= addr < sections['.text'][1]:
        return True
    return False


def is_rodata_region(addr):

    for data_section in data_sections:
        seg_name = SegName(data_section)
        if seg_name == '.rodata' and SegStart(data_section) <= addr <= SegEnd(data_section):
            return True
    return False


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
                return Qword(data) if arch_bits == 64 else Dword(data)
    return None

def test_jmp():
    ea = 0x404078
    print "OpTye: ", GetOpType(ea, 0)
    v_opnd1 = GetOperandValue(ea, 0)
    addr = GetFunctionAttr(v_opnd1, 0)
    if addr != BADADDR:
        print("Jmp function: 0x%x" % (addr))


def get_function_ptr(address, bb_info):
    for curr_addr in data_xref_from(address):
        # print("data xref: %x" % (curr_addr))
        # may_ptr = curr_addr
        if text_start <= curr_addr <= text_end:
            func_addr = GetFunctionAttr(curr_addr, 0)
            if func_addr == curr_addr:
                print("%x has func pointer: %x" % (address, func_addr))
                info = (address, func_addr, 'func_ptr')
                bb_info.append(info)

        elif got_start <= curr_addr < got_end:
            may_ptr = Qword(curr_addr) if arch_bits == 64 else Dword(curr_addr)
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

    global segments

    if '.plt' in sections:
        plt_start, plt_end = sections['.plt']
    else:
        plt_start, plt_end = 0, 0

    code_start, code_end = 0xF000000000000000, 0x0
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

            function_count += 1
            if function < code_start:
                code_start = function
            if function > code_end:
                code_end = function

            # if i & (0x100 - 1) == 0 and i > 0:
            #     print('Function %d.' % i)

    print('\nExported %d functions.' % function_count)
    if '.text' not in sections:
        end_func = get_func(code_end)
        code_end = end_func.end_ea
        sections['.text'] = (code_start, code_end)

    return funcs


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


def recognise_function_gcc32_v1(functions):
    """
    Read data section and recovery functions.
    """
    global segments, sections
    choose_areas = []
    if '.data' in choose_areas:
        choose_areas.append(sections['.data'])
    else:
        for segment in segments:
            permissions = getseg(segment).perm
            if permissions == 6:
                choose_areas.append((SegStart(segment), SegEnd(segment)))

    for start, end in choose_areas:
        xref_addrs = {}
        i = start
        while i <= end:
            dword = Dword(i)
            xrefs_to = data_xref_to(i)
            if xrefs_to:
                xref_addrs.clear()
                for xref_addr in xrefs_to:
                    xref_addrs[xref_addr] = i

            if is_code_region(dword):
                if dword in functions:
                    print(" 0x%x : %x" % (i, dword))
                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, xref_type='func')

                else:
                    mnem = GetMnem(dword)
                    opnd0_name = GetOpnd(dword, 0)
                    ins = GetDisasm(dword)
                    print(" 0x%x : %x" % (i, dword))
                    # print("%s" % (ins))
                    func = get_func(dword)
                    if func is None:
                        MakeFunction(dword)
                        func = get_func(dword)
                        print("Get-func: %s" % (func))

                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, xref_type='func')

            i += 4


def recognise_functions(functions):
    """
    Read the data region and recovery functions.
    """
    print("Arch-bits: %s" % (arch_bits))
    # print(info.is_32bit(), info.is_64bit())
    if arch_bits == 32:
        recognise_function_gcc32_v1(functions)

    elif arch_bits == 64:
        raise Exception("64-bits ARM not complete recognise_function_gcc64")
        # recognise_function_gcc64_v1(functions)

def functon_match_v32(ea):
    """
    Judge whether the address ea is a start of function.
    """
    mnem = GetMnem(ea)
    # ins = GetDisasm(ea)
    if mnem in ['STMFD', 'MOV', 'CMP', 'SUB', 'ADD']:
        return True
    return False

def recovery_functoin_by_traverse_code32(functions, text_start, text_end):
    # print("recovery function in section (%x %x)" % (text_start, text_end))
    ea = text_start
    analyzed_funcs = set()
    while ea < text_end:
        # func = GetFunctionAttr(ea, 0)
        func = get_func(ea)
        # print(" --> %x %s" % (ea, func))
        if func and func.start_ea not in analyzed_funcs:
            analyzed_funcs.add(func.start_ea)
            ea = func.end_ea
            # ea = GetFunctionAttr(ea, 4)
            # print("jmp-> %x" % (ea))
        else:
            flag = functon_match_v32(ea)
            if flag:
                MakeFunction(ea)
            ea += 4

# def recovery_functoin_by_traverse_code32(functions, text_start, text_end):
#     # print("recovery function in section (%x %x)" % (text_start, text_end))
#     ea = text_start
#     start = GetFunctionAttr(ea, 0)
#     end = GetFunctionAttr(ea, 4)
#     analyzed_funcs = set()
#     # print("%x %x" % (start, end))
#     while ea < text_end:
#         func = GetFunctionAttr(ea, 0)
#         # print(" --> %x %x" % (ea, func))
#         if func != BADADDR and func not in analyzed_funcs:
#             analyzed_funcs.add(func)
#             ea = GetFunctionAttr(ea, 4)
#             # print("jmp-> %x" % (ea))
#         else:
#             flag = functon_match_v32(ea)
#             if flag:
#                 MakeFunction(ea)
#             ea += 4

def recognise_functions_v2(functions):
    """
    Recovery function by traverse the .text section.
    """
    if '.text' not in sections:
        print("Could not find text section!")
        return
    text_start, text_end = sections['.text']
    if arch_bits == 32:
        recovery_functoin_by_traverse_code32(functions, text_start, text_end)

    elif arch_bits == 64:
        raise Exception("64-bits ARM not complete recognise_function_gcc64")

def get_switch_block(blocks):

    switch_blocks = {}
    for block in blocks:
        block_start, block_end = block.startEA, block.endEA
        ea = block_start
        ins_addrs = {ea}
        print("exit-block: %x" % (block_start))

        while ea != BADADDR and ea < block_end:
            mnem = GetMnem(ea)
            opnd0_name = GetOpnd(ea, 0)

            if 'LDR' in mnem and opnd0_name in ['PC']:
                switch_blocks[block] = ea

            ea = NextHead(ea)
            if ea in ins_addrs:
                break
            else:
                ins_addrs.add(ea)

    debug
    return switch_blocks


def get_block_info_arm(funcea, func_end, block, funcs, func_info, blocks_record):
    bb_info = []
    find_switch = None
    ins_addrs = set()
    block_start, block_end = block.startEA, block.endEA
    ea = block_start
    ins_addrs.add(ea)
    text_start, text_end = sections['.text']
    # print(".text (%x %x)" % (text_start, text_end))
    while ea != BADADDR and ea < block_end:
        # print("Analysis: 0x%x" % (ea))
        mnem = GetMnem(ea)
        if mnem[:2] == 'BL':
            v_opnd1 = GetOperandValue(ea, 0)
            # print('%x' % v_opnd1)
            addr = GetFunctionAttr(v_opnd1, 0)
            attr = GetFunctionAttr(v_opnd1, 8)
            # print("addr: %x" % (addr))

            if addr != BADADDR and v_opnd1 == addr:
                if plt_start <= addr <= plt_end or attr == 0x4c0:
                    # print("Call to addr (PLT): %x" % (addr))
                    func_name = GetFunctionName(addr)
                    func_info['call'].append((block_start, ea, func_name))
                    # print("Has extern func: %x, %s" % (addr, func_name))

                elif text_start <= addr <= text_end:
                    # print("Has a (%s Call) in 0x%x to 0x%x" % (mnem, ea, addr))
                    func_info['call'].append((block_start, ea, addr))

                elif extern_start <= addr <= extern_end:
                    func_name = GetFunctionName(addr)
                    func_info['call'].append((block_start, ea, func_name))
                    # print("Has a (%s Extern call) in 0x%x to %s" % (mnem, ea, func_name))

            elif addr == BADADDR:
                opnd0 = GetOpnd(ea, 0)
                if opnd0 not in ['LR']:
                    # print("Has a indirect (%s Call) in 0x%x" % (mnem, ea))
                    bb_info.append((ea, None, 'iCall'))

        elif mnem in ['B']:
            opnd0_type = GetOpType(ea, 0)
            # print("opnd0_type: %s" % (opnd0_type))
            if opnd0_type == 7:
                v_opnd1 = GetOperandValue(ea, 0)
                addr = GetFunctionAttr(v_opnd1, 0)
                if addr != BADADDR and addr != funcea:
                    if plt_start <= addr <= plt_end:
                        func_name = GetFunctionName(addr)
                        func_info['call'].append((block_start, ea, func_name))
                        # print("Has a extern (%s Call) in 0x%x to %s" % (mnem, ea, func_name))

                    elif text_start <= addr <= text_end:
                        # print("Has a (B Call) to 0x%x" % (addr))
                        func_info['call'].append((block_start, ea, addr))

                    elif extern_start <= addr <= extern_end:
                        func_name = GetFunctionName(addr)
                        func_info['call'].append((block_start, ea, func_name))
                        # print("Has a (%s Extern call) in 0x%x to %s" % (mnem, ea, func_name))

            elif opnd0_type == 1:
                opnd1 = GetOpnd(ea, 0)
                bb_info.append((ea, None, 'iCall'))

        elif mnem in ['MOV', 'LDR']:
            opnd0 = GetOpnd(ea, 0)
            opnd1 = GetOpnd(ea, 1)
            if opnd0 == 'PC':
                tmp_ea = NextHead(ea)
                if tmp_ea >= block_end and 'SP' in opnd1:
                    print("It's a tail return call, ingore!!!")
                else:
                    # print("Find move icall in %x %x" % (ea, block_end))
                    bb_info.append((ea, None, 'iCall'))

        # vtable_ptr = get_vptr_xref(ea)
        # print("vtable ptr: ", vtable_ptr)
        # if vtable_ptr:
        #     bb_info.append((ea, vtable_ptr, 'xref_vptr'))

        if ea in data_xref_addrs:
            data = data_xref_addrs[ea]
            # print("  Xref-data: 0x%x to 0x%x" % (ea, data))
            bb_info.append((ea, data, 'data'))

        get_function_ptr(ea, bb_info)

        ea = NextHead(ea)
        if ea in ins_addrs:
            break
        else:
            ins_addrs.add(ea)

    funcea_str = '%x' % (funcea)
    if funcea_str not in blocks_record:
        blocks_record[funcea_str] = {}

    if bb_info:
        blocks_record[funcea_str][block_start] = bb_info


def generate_cfg_arm(funcs, cfg_record, blocks_record, switch_record):
    node_list = []
    # for funcea in [0x198f0]:
    for funcea in funcs:
        # print("funcea: %x" % (funcea))
        try:
            attr = GetFunctionAttr(funcea, 8)
        except:
            attr = 0
        if attr == 0x4c0:
            print("Lib func: %x" % (funcea))
            continue
        else:
            print("%x has attr %x" % (funcea, attr))
        func_info = {'block': [], 'jmp': [], 'call': []}
        node_record = set()
        function_name = GetFunctionName(funcea)
        func_info['name'] = function_name
        funcea_name = '%x' % funcea
        # print("func: 0x%x %s" % (funcea, function_name))

        xref_funcptrs = []
        all_blocks = set()
        exit_blocks = []
        link_blocks = set()
        link_blocks.add(funcea)
        function_obj = get_func(funcea)
        func_end = function_obj.end_ea
        flow = FlowChart(function_obj)

        for block in flow:
            func_info['block'].append((block.startEA, block.endEA))
            # print("Block: 0x%x" % (block.startEA))

            get_block_info_arm(funcea, func_end, block, funcs, func_info, blocks_record)

            succ_blocks = list(block.succs())
            for succ_block in succ_blocks:
                func_info['jmp'].append((block.startEA, succ_block.startEA))
                link_blocks.add(succ_block.startEA)
                # print(" Link block: 0x%x" % (succ_block.startEA))

            all_blocks.add(block.startEA)

            if len(succ_blocks) == 0 and block.endEA != function_obj.end_ea:
                # print(" Exit-block: 0x%x" % (block.startEA))
                exit_blocks.append(block)

        if len(link_blocks) != len(all_blocks):
            switch_blocks = get_switch_block(exit_blocks)
            # print("func: 0x%x %s" % (funcea, function_name))

            if len(switch_blocks) == 1:
                for addr in all_blocks:
                    if addr not in link_blocks:
                        for switch_block in switch_blocks:
                            func_info['jmp'].append((switch_block.startEA, addr))
                        # print("Unlink block: 0x%x" % (addr))

            elif len(switch_blocks) > 1:
                for switch_block, jmp_ea in switch_blocks.items():
                    # print(" Switch-block: 0x%x, jmp_ea: 0x%x" % (switch_block.startEA, jmp_ea))
                    sblock_start = switch_block.startEA
                    if funcea_name not in switch_record:
                        switch_record[funcea_name] = []

                    switch_record[funcea_name].append((sblock_start, jmp_ea))

        cfg_record[funcea_name] = func_info

        block_xrefs_info = {}
        for (bb_addr, ea, func_ptr) in xref_funcptrs:
            if func_ptr not in callees:
                if bb_addr not in block_xrefs_info:
                    block_xrefs_info[bb_addr] = []

                info = (ea, func_ptr, 'func_ptr')
                block_xrefs_info[bb_addr].append(info)

        if len(block_xrefs_info):
            if funcea_name not in blocks_record:
                blocks_record[funcea_name] = {}

            for bb_addr, xref_infos in block_xrefs_info.items():
                # print("Add func-ptr xref: 0x%x %s" % (bb_addr, xref_infos))
                blocks_record[funcea_name][bb_addr] = xref_infos


def get_cfg_block_info():
    """
    Parse the binary and get each function's cfg and block info.
    """
    # save_path = ARGV[1]
    # DEBUG
    # save_path = '/mnt/e/Ubuntu/work/binary_info/'
    save_path = 'E:\IDABinaryInfo\\'

    functions = get_all_functions()
    # function_names = get_function_names(functions)

    # Export .cfg entries.
    cfg_record, blocks_record, switch_record = {}, {}, {}

    generate_cfg_arm(functions, cfg_record, blocks_record, switch_record)

    json.dump(cfg_record, open(save_path + file_name + '_cfg.json', 'w'), indent=4)
    json.dump(blocks_record, open(save_path + file_name + '_block_info.json', 'w'), indent=4)
    json.dump(switch_record, open(save_path + file_name + '_switch.json', 'w'), indent=4)

    # json.dump(cfg_record, open(GetInputFile() + '_cfg.json', 'w'))
    # json.dump(blocks_record, open(GetInputFile() + '_block_info.json', 'w'))

    print('\nExported cfg and block data entries.')


file_name = GetInputFile()
file_path = GetInputFilePath()

info = get_inf_structure()
if info.is_64bit():
    arch_bits = 64
elif info.is_32bit():
    arch_bits = 32
else:
    raise Exception("Only support 32 or 64 bit arch.")

# print(info.is_64bit(), info.is_32bit())

if info.ostype == idc.OSTYPE_WIN and info.filetype == 11:
    is_windows = True
    is_linux = False

elif info.ostype == 0 and info.filetype == 18:
    is_windows = False
    is_linux = True

else:
    raise Exception("OS type not supported.")

# Windows does only work if the image base is set to 0x0.
if is_windows and get_imagebase() != 0x0:
    print("Image base has to be 0x0.")
    Exit(0)



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

sections = {}
for segment in segments:
    name = SegName(segment)
    sections[name] = (SegStart(segment), SegEnd(segment))

print(sections)

if '.text' not in sections:
    print("Couldn't found text segment, should custom label!!!")
    # sections['.text'] = (0x4054a0, 0x4b1f00) # xxx
    # sections['.text'] = (0x401cb0, 0x4a03f4) # dir823 goahead

if '.rodata' not in sections:
    print("Couldn't found rodata segment, should custom label!!!")
    # sections['.rodata'] = (0x4b1f04, 0x4db790) # xxx
    # sections['.rodata'] = (0x4a03f8, 0x589514) # dir823 goahead

if '.data' not in sections:
    print("Couldn't found data segment, should custom label!!!")
    # sections['.data'] = (0x4eb794, 0x5094d4) # xxx
    # sections['.data'] = (0x4afba0, 0x5895ab) # dir823 goahead

if '.bss' not in sections:
    print("Couldn't found bss segment, should custom label!!!")
    # sections['.bss'] = (0x5094d8, 0x1e5383b) # xxx
    # sections['.bss'] = (0x5895ac, 0x598763) # dir823 goahead


def main():

    # addr = 0xA938
    # func = get_func(addr)
    # print(type(func))
    # t = GetFunctionAttr(addr, 8)
    # print(hex(t))
    # t = GetFunctionAttr(0xA890, 8)
    # print(hex(t))
    # t = GetFunctionAttr(0x1E8EC, 8)
    # print(hex(t))
    # t = GetFunctionAttr(0x1f4f4, 8)
    # print(hex(t))
    # return

    functions = get_all_functions()

    recognise_functions(functions)

    recognise_functions_v2(functions)

    get_cfg_block_info()

main()
# Exit(0)
