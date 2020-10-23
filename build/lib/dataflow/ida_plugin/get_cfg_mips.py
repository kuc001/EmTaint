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

vtable_section_names = [".rodata",
    ".data.rel.ro",
    ".data.rel.ro.local",
    ".rdata"]


is_linux = None
is_windows = None


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


def get_block_info_mips(funcea, block, function_names, func_info, blocks_record):
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
            print("Call: 0x%x %s" % (ea, ins))
            ins_list = ins.split(" ;")
            ins_list = filter(None, re.split(r'[; \s]\s*', ins))
            if ins_list[-1] != opnd0_name:
                func_name = ins_list[-1]
                f_id = hash(func_name)
                print("ins-list: %s, id %s" % (ins_list, f_id))
                if f_id in function_names:
                    func_addr = function_names[f_id]
                    print("  D-Call: 0x%x" % (function_names[f_id]))
                    func_info['call'].append((block_start, ea, func_addr))

                else:
                    print("  Lib function: %s" % (func_name))
                    func_info['call'].append((block_start, ea, func_name))

            else:
                print("  I-Call:")
                bb_info.append((ea, None, 'iCall'))

        elif mnem == 'bal':
            opnd0_value = GetOperandValue(ea, 0)
            # print("bal : %x" % (opnd0_value))
            addr = GetFunctionAttr(opnd0_value, 0)
            if addr != BADADDR and addr != funcea:
                print("  D-Call: 0x%x" % (opnd0_value))
                func_info['call'].append((block_start, ea, opnd0_value))

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

    function_names = {}
    for funcea in funcs:
        function_name = GetFunctionName(funcea)
        name_id = hash(function_name)
        function_names[name_id] = funcea
        # print("Function: 0x%x %s %s" % (funcea, function_name, name_id))

    # Export .cfg entries.
    cfg_record, blocks_record = {}, {}
    switch_record = {}

    generate_cfg_mips(funcs, function_names, cfg_record, blocks_record, switch_record)

    json.dump(cfg_record, open(save_path + file_name + '_cfg.json', 'w'), indent=4)
    json.dump(blocks_record, open(save_path + file_name + '_block_info.json', 'w'), indent=4)
    json.dump(switch_record, open(save_path + file_name + '_switch.json', 'w'), indent=4)

    # json.dump(cfg_record, open(GetInputFile() + '_cfg.json', 'w'))
    # json.dump(blocks_record, open(GetInputFile() + '_block_info.json', 'w'))

    print('\nExported cfg and block data entries.')


def generate_cfg_mips(funcs, function_names, cfg_record, blocks_record, switch_record):
    node_list = []
    # for funcea in [0x43d7f4]:
    for funcea in funcs:
        # print("funcea: %x" % (funcea))
        # continue
        func_info = {'block': [], 'jmp': [], 'call': []}
        node_record = set()
        function_name = GetFunctionName(funcea)
        func_info['name'] = function_name
        # print("func: 0x%x %s" % (funcea, function_name))

        funcea_name = '%x' % funcea

        all_blocks = set()
        exit_blocks = []
        link_blocks = set()
        link_blocks.add(funcea)

    	flow = FlowChart(get_func(funcea))
        for block in flow:
            func_info['block'].append((block.startEA, block.endEA))
            # print("Block: 0x%x" % (block.startEA))

            get_block_info_mips(funcea, block, function_names, func_info, blocks_record)

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

            if len(succ_blocks) == 0:
                # print(" Exit-block: 0x%x" % (block.startEA))
                exit_blocks.append(block)

        if len(link_blocks) != len(all_blocks):
            switch_blocks = get_switch_block(exit_blocks, '$a0')
            print("func: 0x%x %s" % (funcea, function_name))

            if len(switch_blocks) == 1:
                for addr in all_blocks:
                    if addr not in link_blocks:
                        for switch_block in switch_blocks:
                            func_info['jmp'].append((switch_block.startEA, addr))
                        print("Unlink block: 0x%x" % (addr))

            elif len(switch_blocks) > 1:
                for switch_block, jmp_ea in switch_blocks.items():
                    print(" Switch-block: 0x%x, jmp_ea: 0x%x" % (switch_block.startEA, jmp_ea))
                    sblock_start = switch_block.startEA
                    if funcea_name not in switch_record:
                        switch_record[funcea_name] = []

                    switch_record[funcea_name].append((sblock_start, jmp_ea))

        cfg_record[funcea_name] = func_info


def get_switch_block(blocks, switch_reg):

    switch_blocks = {}
    for block in blocks:
        block_start, block_end = block.startEA, block.endEA
        ea = block_start
        ins_addrs = {ea}

        while ea != BADADDR and ea < block_end:
            mnem = GetMnem(ea)
            opnd0_name = GetOpnd(ea, 0)

            if mnem == 'jr' and opnd0_name == switch_reg:
                switch_blocks[block] = ea

            ea = NextHead(ea)
            if ea in ins_addrs:
                break
            else:
                ins_addrs.add(ea)

    return switch_blocks


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

    print("vtable sectons: %s" % (vtable_sections))

main()
# Exit(0)
