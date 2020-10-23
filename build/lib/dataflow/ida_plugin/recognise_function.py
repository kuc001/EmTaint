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
segments = list(Segments())

data_section_names = [
    ".data",
    ".rodata",
    ".data.rel.ro",
    ".data.rel.ro.local",
    ".rdata"]


is_linux = None
is_windows = None


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
data_sections = list()
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
    elif SegName(segment) in data_section_names:
        data_sections.append(segment)

if text_end == 0:
    # raise Exception("Couldn't found text segment!!!")
    print("Couldn't found text segment, should custom label!!!")
    text_start, text_end = 0x4054a0, 0x4b1f00

print("data sectons: %s" % (data_sections))


def data_xref(ea):
    return [x for x in DataRefsFrom(ea)]

def data_xref_to(ea):
    return [x for x in DataRefsTo(ea)]

def collect_data_xref_to(xref_addrs, data_xref_addrs, xref_type=None):
    for xref_addr in xref_addrs:
        if xref_type == 'func' and not is_code_region(xref_addr):
            continue

        if xref_addr not in data_xref_addrs:
            data_xref_addrs.append(xref_addr)

def is_code_region(addr):
    if text_start <= addr < text_end:
        return True
    return False


def is_rodata_region(addr):

    for data_section in data_sections:
        seg_name = SegName(data_section)
        if seg_name == '.rodata' and SegStart(data_section) <= addr <= SegEnd(data_section):
            return True
    return False


def get_functions():

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
    return funcs


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


def recognise_function_gcc(functions):

    for data_section in data_sections:
        i = SegStart(data_section)

        while i <= SegEnd(data_section) - 4:
            dword = Dword(i)
            print(" 0x%x : %x" % (i, dword))
            if is_code_region(dword) and dword not in functions:
                func = get_func(dword)
                if func is None:
                    MakeFunction(dword)
                    func = get_func(dword)
                    print("Get-func: %s" % (func))


            i += 4


def recognise_function_gcc_custom(functions, data_xref_addrs):

    for name, (start, end) in custom_data_sections.items():
        if name not in ['.data']:
            continue

        xref_addrs = []
        i = start
        while i <= end:
            dword = Dword(i)
            xrefs_to = data_xref_to(i)
            if xrefs_to:
                xref_addrs = xrefs_to

            if is_code_region(dword) and dword not in functions:
                # print(" 0x%x : %x" % (i, dword))
                # ins = GetDisasm(dword)
                # print("Ins: %s" % (ins))
                mnem = GetMnem(dword)
                opnd0_name = GetOpnd(dword, 0)
                # print("%s %s" % (mnem, opnd0_name))
                if mnem == 'li' and opnd0_name == '$gp':
                    print(" 0x%x : %x" % (i, dword))
                    if xref_addrs:
                        collect_data_xref_to(xref_addrs, data_xref_addrs, xref_type='func')

                    # func = get_func(dword)
                    # if func is None:
                    #     MakeFunction(dword)
                    #     func = get_func(dword)
                    #     print("Get-func: %s" % (func))


            i += 4


def recognise_function_gcc_64(functions):

    for data_section in data_sections:
        i = SegStart(data_section)

        while i <= SegEnd(data_section) - 4:
            qword = Qword(i)
            if is_code_region(qword) and qword not in functions:
                print(" 0x%x : %x" % (i, qword))
                # start_bytes = Qword(qword)
                # byte = get_many_bytes(qword, 1)
                # if byte not in ['\x67', '\xdf', '\x24', '\x3c']:
                #     print("0x%x %x" % (qword, start_bytes))

                # func = get_func(qword)
                # if func is None:
                #     MakeFunction(qword)
                #     func = get_func(qword)
                #     print("Get-func: %s" % (func))


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


custom_data_sections = {
    '.rodata': (0x4b1f04, 0x4db790),
    '.data': (0x4eb794, 0x5094d4),
    '.bss': (0x5094d8, 0x1e5383b),
}


def main():
    data_xref_addrs = []

    # functions = get_functions()
    functions = []
    # recognise_function_gcc_64(functions)
    # recognise_function_gcc(functions)
    # recognise_function_gcc_custom(functions, data_xref_addrs)

    # read_function_model_mips(functions)

    # recovery_data(0x10000060, 0x10002b88)

    # for xref_addr in data_xref_addrs:
    #     print("xref-addr: 0x%x" % (xref_addr))

    # test_xref(0x42dc94)


main()
# Exit(0)
