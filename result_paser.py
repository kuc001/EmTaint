#!/usr/bin/env python


import pickle
import sys

import claripy
from dataflow.variable_expression import TraceExpr, RecursiveExpr


_data_path = '/home/kai/Work/angr-work/exp_data/'


def load_icall_results(binary):
    with open(_data_path + '%s.icall.txt' % (binary), 'rb') as f:
        icall_results = pickle.load(f)

    for funcea, icall_exprs in icall_results.items():
        print("function: %x" % (funcea))
        for expr in icall_exprs:
            print(" %s" % (expr))
    return icall_results


def load_ptr_results(binary):
    with open(_data_path + '%s.ptr.txt' % (binary), 'rb') as f:
        ptr_results = pickle.load(f)

    for funcea, ptr_exprs in ptr_results.items():
        print("function: %x" % (funcea))
        for expr in ptr_exprs:
            print(" %s" % (expr))
    return ptr_results


if __name__ == "__main__":
    binary = sys.argv[1]

    icall_results = load_icall_results(binary)

    ptr_results = load_ptr_results(binary)

    for funcea, icall_exprs in icall_results.items():
        # print("Function %x" % (funcea))
        for icall_expr in icall_exprs:
            # print("\nicall expr: %s" % (icall_expr))
            source = icall_expr.expr.source
            icall_data = icall_expr.expr.ast
            if icall_data.op != 'Load':
                continue

            icall_ptr = icall_data.args[0]
            vtable_ptr, offset = None, None
            if icall_ptr.op == '__add__' and len(icall_ptr.args) == 2:
                arg1 = icall_ptr.args[0]
                arg2 = icall_ptr.args[1]
                if arg1.concrete:
                    vtable_ptr = arg2
                    offset = arg1.args[0]

                elif arg2.concrete:
                    vtable_ptr = arg1
                    offset = arg2.args[0]

            elif icall_ptr.op == 'Load':
                vtable_ptr = icall_ptr
                offset = 0

            if offset is None:
                print("Complex icall expr: %s" % (icall_expr))
                continue

            # print("Vtable ptr: %s, offset: %d" % (vtable_ptr, offset))

            for ptr_exprs in ptr_results.values():
                for ptr_expr in ptr_exprs:
                    # print(ptr_expr)
                    ptr_data = ptr_expr.expr.ast
                    if vtable_ptr.__hash__() == ptr_data.__hash__():
                        print("Lucky!!! %s\n %s %d" % (source, ptr_expr, offset))
