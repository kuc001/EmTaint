#!/usr/bin/env python
import sys
import os
import re

from idc import *
from idautils import *
from idaapi import *

from struct import pack
from ctypes import c_uint32, c_uint64
import subprocess
from collections import defaultdict
import json

base = get_imagebase()
segments = list(Segments())

data_xref_addrs = {}

vtable_section_names = [".rodata",
    ".data.rel.ro",
    ".data.rel.ro.local",
    ".rdata"]


is_linux = None
is_windows = None

def data_xref_from(ea):
    return [x for x in DataRefsFrom(ea)]

def data_xref_to(ea):
    return [x for x in DataRefsTo(ea)]

def collect_data_xref_to(xref_addrs, xref_type=None):
    # print("collect_data_xref_to: %s" % (xref_type))
    for xref_addr, data in xref_addrs.items():
        # print("%x %x" % (xref_addr, data))
        if xref_type == 'func' and not is_code_region(xref_addr):
            continue

        if xref_addr not in data_xref_addrs:
            data_xref_addrs[xref_addr] = data
            print("Get-data-xref: %x -> %x" % (xref_addr, data))

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


def read_function_model_mips(functions):
    """
    The function start model.
    """
    for funcea in functions:
        # for ea in range(funcea, funcea+8):
        #     byte = get_many_bytes(ea, 1)
        #     print('%s' % byte[2:])
        qword = Qword(funcea)
        # print("0x%x %x" % (funcea, qword))

        byte = get_many_bytes(funcea, 1)
        if byte not in ['\x67', '\xdf', '\x24']:
            print("0x%x %x" % (funcea, qword))

        # break


def recognise_function_gcc32_v1(functions):
    """
    Read data section and recovery functions.
    """
    choose_sections = ['.data'] # '.rodata'?
    for name, (start, end) in sections.items():
        if name not in choose_sections:
            continue

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
                    print(" 0x%x : %x" % (i, dword))
                    func = get_func(dword)
                    if func is None:
                        MakeFunction(dword)
                        func = get_func(dword)

                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, xref_type='func')

            i += 4

def recognise_function_gcc32_v2(functions):
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
        error_count = 0
        while i <= end:
            dword = Dword(i)
            if error_count > 50:
                break
            if dword == 0xffffffff:
                error_count += 1
            else:
                error_count = 0
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
                    if ((mnem in ['li', 'lui'] and opnd0_name == '$gp') or
                            (mnem == 'addiu' and opnd0_name == '$sp')):
                        print(" 0x%x : %x" % (i, dword))
                        func = get_func(dword)
                        if func is None:
                            MakeFunction(dword)
                            func = get_func(dword)
                            # print("Get-func: %s" % (func))

                        if xref_addrs:
                            collect_data_xref_to(xref_addrs, xref_type='func')
                    else:
                        print(" Unsure 0x%x : %x" % (i, dword))

            i += 4

def recognise_function_gcc64_v1(functions):
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
            qword = Qword(i)
            xrefs_to = data_xref_to(i)
            if xrefs_to:
                xref_addrs.clear()
                for xref_addr in xrefs_to:
                    xref_addrs[xref_addr] = i

            if is_code_region(qword):
                if qword in functions:
                    print(" 0x%x : %x" % (i, qword))
                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, xref_type='func')

                else:
                    print(" 0x%x : %x" % (i, qword))
                    func = get_func(qword)
                    if func is None:
                        MakeFunction(qword)
                        func = get_func(qword)

                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, xref_type='func')

            i += 8


def recovery_data(start, end):

    ea = start

    while ea <= end:
        dword = Dword(ea)
        if is_rodata_region(dword):
            con_str = GetString(dword)
            print("0x%x : %s" % (ea, con_str))

        else:
            print("0x%x : %x" % (ea, dword))


        ea += 4


def test_xref(ea):

    for xref_addr in DataRefsFrom(ea):
        print("xref_from: 0x%x -> 0x%x" % (ea, xref_addr))

    for xref_addr in DataRefsTo(ea):
        print("xref_to: 0x%x <- 0x%x" % (ea, xref_addr))

def functon_match_v32(ea):
    """
    Judge whether the address ea is a start of function.
    """
    mnem = GetMnem(ea)
    opnd0_name = GetOpnd(ea, 0)
    # ins = GetDisasm(ea)
    if ((mnem in ['li', 'lui', 'la'] and opnd0_name == '$gp') or
            ('add' in mnem and opnd0_name == '$sp')):
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

def recognise_functions(functions):
    """
    Read the data region and recovery functions.
    """
    print("Arch-bits: %s" % (arch_bits))
    if arch_bits == 32:
        # recognise_function_gcc32_v1(functions)
        recognise_function_gcc32_v2(functions)

    elif arch_bits == 64:
        recognise_function_gcc64_v1(functions)



def data_xref(ea):
    return [x for x in DataRefsFrom(ea)]


def get_plt_jmp_addr_gcc64(funcea):
    for ea in FuncItems(funcea):
        if (GetMnem(ea) == 'jmp' and GetOpType(ea, 0) == 2):
            for data in data_xref(ea):
                return Qword(data)
    return None


def get_function_ptr_mips_64(address, bb_info):
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

def get_xref_function_ptr_mips(ea, bb_addr, functions, xref_funcptrs):
    """
    Get the function pointer xref in function.
    """
    xrefs_from = data_xref_from(ea)

    for data in xrefs_from:
        if data in functions:
            info = (bb_addr, ea, data)
            xref_funcptrs.append(info)
            # print("Found func-ptr xref: 0x%x to 0x%x" % (ea, data))

def get_block_info_mips(funcea, block, functions, function_names, func_info, blocks_record, xref_funcptrs, callees):
    bb_info = []
    find_switch = None
    ins_addrs = set()
    block_start, block_end = block.startEA, block.endEA
    ea = block_start
    ins_addrs.add(ea)

    while ea != BADADDR and ea < block_end:
        # print("Analysis: 0x%x" % (ea))
        mnem = GetMnem(ea)
        opnd0_name = GetOpnd(ea, 0)
        ins = GetDisasm(ea)
        call_mnems = ['jalr', 'jr', 'j', 'jal']
        if mnem in call_mnems and opnd0_name == '$t9':
            # print("Call: 0x%x %s" % (ea, ins))
            ins_list = ins.split(" ;")
            ins_list = filter(None, re.split(r'[; \s]\s*', ins))
            # print(ins_list)
            if len(ins_list) >= 3 and ins_list[1] == opnd0_name:
                func_name = ins_list[2]
                func_addr = LocByName(func_name)
                if func_addr != BADADDR:
                    if extern_start <= func_addr <= extern_end:
                        # print("  Lib function: %s" % (func_name))
                        func_info['call'].append((block_start, ea, func_name))
                    else:
                        callees.add(func_addr)
                        # print("  D-Call: 0x%x" % (func_addr))
                        func_info['call'].append((block_start, ea, func_addr))
                else:
                    # print("  I-Call:")
                    bb_info.append((ea, None, 'iCall'))
                # f_id = hash(func_name)
                # print("ins-list: %s, id %s" % (ins_list, f_id))
                # if f_id in function_names:
                #     func_addr = function_names[f_id]
                #     callees.add(func_addr)
                #     print("  D-Call: 0x%x" % (function_names[f_id]))
                #     func_info['call'].append((block_start, ea, func_addr))

                # else:
                #     print("  Lib function: %s" % (func_name))
                #     func_info['call'].append((block_start, ea, func_name))

            else:
                # print("  I-Call:")
                bb_info.append((ea, None, 'iCall'))

        elif mnem in call_mnems:
            opnd0_value = GetOperandValue(ea, 0)
            addr = GetFunctionAttr(opnd0_value, 0)
            if addr != BADADDR and addr != funcea:
                attr = GetFunctionAttr(opnd0_value, 8)
                if attr == 0xc0:
                    func_name = GetFunctionName(opnd0_value)
                    func_info['call'].append((block_start, ea, func_name))
                    # print("  Lib function: %s" % (func_name))
                else:
                    callees.add(opnd0_value)
                    func_info['call'].append((block_start, ea, opnd0_value))
                    # print("  D-Call: 0x%x" % (opnd0_value))

        elif mnem == 'bal':
            opnd0_value = GetOperandValue(ea, 0)
            # print("bal : %x" % (opnd0_value))
            addr = GetFunctionAttr(opnd0_value, 0)
            if addr != BADADDR and addr != funcea:
                attr = GetFunctionAttr(opnd0_value, 8)
                if attr == 0xc0:
                    func_name = GetFunctionName(opnd0_value)
                    func_info['call'].append((block_start, ea, func_name))
                    # print("  Lib function: %s" % (func_name))
                else:
                    callees.add(opnd0_value)
                    func_info['call'].append((block_start, ea, opnd0_value))
                    # print("  D-Call: 0x%x" % (opnd0_value))

        if ea in data_xref_addrs:
            data = data_xref_addrs[ea]
            print("  Xref-data: 0x%x to 0x%x" % (ea, data))
            bb_info.append((ea, data, 'data'))

        get_xref_function_ptr_mips(ea, block_start, functions, xref_funcptrs)

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


def memory_accessible(addr):
    for segment in segments:
        if SegStart(segment) <= addr < SegEnd(segment):
            return True
    return False


def create_sections(code_start, code_end):
    global sections
    print("Create sections!")
    sections['.text'] = (code_start, code_end)
    for segment in segments:
        permissions = getseg(segment).perm
        segg = getseg(segment)
        print(type(segg), segg.name, segg.perm)
        print("%x %x" % (segment, permissions))
        print("start and end: (%x %x)" % (SegStart(segment), SegEnd(segment)))

def get_all_functions():

    global segments, sections

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

        # print('\nProcessing segment %s.' % SegName(segment))
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

def get_function_names(functions):
    """
    Get all function's name.
    """
    function_names = {}
    for funcea in functions:
        function_name = GetFunctionName(funcea)
        name_id = hash(function_name)
        function_names[name_id] = funcea
        # print("Function: 0x%x %s %s" % (funcea, function_name, name_id))
    return function_names




def get_cfg_block_info():
    """
    Parse the binary and get each function's cfg and block info.
    """
    # save_path = ARGV[1]
    # DEBUG
    # save_path = '/media/work/binary_info/'
    save_path = 'E:\IDABinaryInfo\\'

    functions = get_all_functions()
    function_names = get_function_names(functions)

    # Export .cfg entries.
    cfg_record, blocks_record, switch_record = {}, {}, {}

    generate_cfg_mips(functions, function_names, cfg_record, blocks_record, switch_record)

    json.dump(cfg_record, open(save_path + file_name + '_cfg.json', 'w'), indent=4)
    json.dump(blocks_record, open(save_path + file_name + '_block_info.json', 'w'), indent=4)
    json.dump(switch_record, open(save_path + file_name + '_switch.json', 'w'), indent=4)

    # json.dump(cfg_record, open(GetInputFile() + '_cfg.json', 'w'))
    # json.dump(blocks_record, open(GetInputFile() + '_block_info.json', 'w'))

    print('\nExported cfg and block data entries.')


def generate_cfg_mips(funcs, function_names, cfg_record, blocks_record, switch_record):
    node_list = []
    # for funcea in [0x49ef04]:
    for funcea in funcs:
        # print("funcea: %x" % (funcea))
        function_name = GetFunctionName(funcea)
        try:
            attr = GetFunctionAttr(funcea, 8)
        except:
            attr = 0
        if attr == 0xc0:
            print("Lib func: %x %s" % (funcea, function_name))
            continue
        else:
            print("%x %s has attr %x" % (funcea, function_name, attr))

        func_info = {'block': [], 'jmp': [], 'call': []}
        node_record = set()
        # function_name = GetFunctionName(funcea)
        func_info['name'] = function_name
        # print("func: 0x%x %s" % (funcea, function_name))

        if '.' in function_name:
            # print("It is a libc function: %s" % (function_name))
            continue

        funcea_name = '%x' % funcea

        xref_funcptrs = []
        callees = set()
        all_blocks = set()
        exit_blocks = []
        link_blocks = set()
        link_blocks.add(funcea)
        function_obj = get_func(funcea)
        flow = FlowChart(function_obj)

        for block in flow:
            func_info['block'].append((block.startEA, block.endEA))
            # print("Block: 0x%x" % (block.startEA))

            get_block_info_mips(funcea, block, funcs, function_names, func_info, blocks_record, xref_funcptrs, callees)

            succ_blocks = list(block.succs())
            for succ_block in succ_blocks:
                func_info['jmp'].append((block.startEA, succ_block.startEA))
                link_blocks.add(succ_block.startEA)
                # print(" Link block: 0x%x" % (succ_block.startEA))

            all_blocks.add(block.startEA)

            # pre_blocks = list(block.preds())
            # for pre_block in pre_blocks:
            #     print(" pre block: 0x%x" % (pre_block.startEA))
            # if len(pre_blocks) == 0 and block.startEA != funcea:
            #     print(" Un-link block: 0x%x" % (block.startEA))

            if len(succ_blocks) == 0 and block.endEA != function_obj.end_ea:
                # print(" Exit-block: 0x%x %x %x" % (block.startEA, block.endEA, function_obj.end_ea))
                exit_blocks.append(block)

        # print("all_blocks: %d" % (len(all_blocks)))
        # print("link_blocks: %d" % len(link_blocks))
        # print("function_end: %x" % (function_obj.end_ea))
        # for exit_block in exit_blocks:
        #     print("exit-block: %x %x" % (exit_block.startEA, exit_block.endEA))

        if len(link_blocks) != len(all_blocks):
            switch_blocks = get_switch_block(exit_blocks)
            # print("func: 0x%x %s has switch %s" % (funcea, function_name, switch_blocks))
            # print("No-succs %s" % (exit_blocks))

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
                if bb_addr not in blocks_record[funcea_name]:
                    blocks_record[funcea_name][bb_addr] = []
                blocks_record[funcea_name][bb_addr].extend(xref_infos)


def get_switch_block(blocks):

    switch_blocks = {}
    for block in blocks:
        block_start, block_end = block.startEA, block.endEA
        ea = block_start
        ins_addrs = {ea}

        while ea != BADADDR and ea < block_end:
            mnem = GetMnem(ea)
            opnd0_name = GetOpnd(ea, 0)

            if mnem == 'jr' and opnd0_name not in ['$ra', '$t9']:
                switch_blocks[block] = ea

            ea = NextHead(ea)
            if ea in ins_addrs:
                break
            else:
                ins_addrs.add(ea)

    return switch_blocks


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

# global variables that are needed for multiple C++ algorithms
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

    # func = get_func(0x408470)
    # print(func)
    # print('%x %x' % (func.start_ea, func.end_ea))
    # return

    functions = get_all_functions()

    recognise_functions(functions)

    recognise_functions_v2(functions)

    get_cfg_block_info()

main()
# Exit(0)
