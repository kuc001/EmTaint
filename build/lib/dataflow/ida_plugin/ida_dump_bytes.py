#!/usr/bin/env python

import os

from idc import *
from idaapi import *
from idautils import *

base = get_imagebase()
segments = list(Segments())

is_linux = None
is_windows = None


def get_ida_bytes(save_file):

    # Windows does only work if the image base is set to 0x0.
    if is_windows and get_imagebase() != 0x0:
        print("Image base has to be 0x0.")
        return

    # print("Image base: %s" % (base))

    ida_bytes = get_many_bytes(text_start, text_end-text_start)

    with open(save_file, 'wb') as f:
        f.write(ida_bytes)

    print("Load all text bytes!")


def main():
    # save_path=ARGV[1]
    save_path = '/home/kai/Test/ida_resutl/'
    save_file = save_path + file_name + '.bytes'
    print("save_file: %s" % (save_file))

    get_ida_bytes(save_file)


file_name = GetInputFile()
info = get_inf_structure()
# print("structure info: %s" % (info))
# print(info.ostype, info.filetype)

if info.ostype == idc.OSTYPE_WIN and info.filetype == 11:
    is_windows = True
    is_linux = False
elif info.ostype == 0 and info.filetype == 18:
    is_windows = False
    is_linux = True
else:
    raise Exception("OS type not supported.")

# global variables that are needed for multiple C++ algorithms
if info.is_32bit():
    arch_words = 4
elif info.is_64bit():
    arch_words = 8
else:
    raise Exception("Only support the 32bit and 64bit arch.")
# print("arch words: %d" % (arch_words))

text_seg = None
text_start = 0
text_end = 0
for segment in segments:
    if SegName(segment) == ".text":
        text_seg = segment
        text_start = SegStart(text_seg)
        text_end = SegEnd(text_seg)


main()
# Exit(0)
