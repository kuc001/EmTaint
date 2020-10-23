#!/usr/bin/env python3


class BIO_read(object):

    def __init__(self, addr, name, src=None, dst=None, length=None):
        # self.arg_num = 3
        # self.src = src
        # self.dst = dst
        # self.length = length
        self.addr = addr
        self.name = name
        self.describe = {0: 'src', 1: 'dst', 2: 'length'}

    def __repr__(self):
        return '< BIO_read (3)>'


class TaintSource(object):
    """
    Initialize the taint source function.
    For example, recv, recvfrom, read, etc.
    """
    def __init__(self):

        self.source_functions = ['BIO_read']
        self.custom_functions = {}

        # self._initialize_source_functions()

        # self._initialize_procedural_function()

    # def _initialize_source_functions(self):
    #     self.source_functions = ['BIO_read']

    def _initialize_procedural_function(self):

        func = BIO_read(0x10be8, 'BIO_read')
        self.custom_functions['BIO_read'] = func
