#!/usr/bin/env python

from .data_collector import weaks_copy, weaks_command_exec, weaks_copy_length, weaks_only_length, weaks_loop

class SecurityCheck(object):

    def __init__(self, collector):
        self.collector = collector

        self.weaks = {}
        self.weaks_exec = set()
        self.weaks_length = set()

    # DEUBG
    def print_weaks(self):
        for addr, stack_offsets in self.weaks.items():
            print("weak-copy: 0x%x %s" % (addr, stack_offsets))

        for addr in self.weaks_exec:
            print("weak-system: 0x%x" % (addr))

        # for addr in tainted_length_locs:
        #     print("weak-copy-length: 0x%x" % (addr))


    def check_taint_security(self):
        """
        Check the taint security for different vulnerability model.
        """
        self.filter_fake_source()

        self.check_weaks_copy()

        self.check_weaks_command_exec()


    def check_weaks_copy(self):

        for loc, weak_exprs in weaks_copy.items():
            for weak_expr in weak_exprs:
                min_constraint = self.get_min_constraint(weak_expr.expr.constraints)
                print("check-weak-copy: %s with %s" % (weak_expr, min_constraint))
                taint_ast = weak_expr.expr.ast
                stack_addr = taint_ast.args[0]
                stack_offset = 0x7fffffff - stack_addr
                if min_constraint is None or min_constraint >= stack_offset:
                    if loc not in self.weaks:
                        self.weaks[loc] = set()
                    self.weaks[loc].add(stack_offset)

    def check_weaks_command_exec(self):

        for loc, weak_exprs in weaks_command_exec.items():
            if len(weak_exprs):
                self.weaks_exec.add(loc)

    def get_min_constraint(self, constraints):

        concret_cons = [c for c in constraints if type(c) is int]
        return min(concret_cons) if len(concret_cons) else None

    def filter_fake_source(self):
        """
        Filter the fake taint source in fread/read/fgets while the stream if from fopen.
        """
        print("Filter-fake-source")
        fake_sources = self.get_file_open_taint_sources()

        for loc, taint_exprs in weaks_copy.items():
            # print("weak-copy: %s" % (taint_expr))
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_copy_length.items():
            # print("weak-copy: %s" % (taint_expr))
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_only_length.items():
            # print("weak-copy: %s" % (taint_expr))
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_command_exec.items():
            # print("weak-copy: %s" % (taint_expr))
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        print("weaks-copy: %s" % (weaks_copy))
        print("weaks-copy: %s" % (weaks_copy_length))

    def get_file_open_taint_sources(self):
        """
        Get the source fread/read/fgets's stream.
        """
        taint_sources = []
        udata_info = self.collector.datas['uData']

        for funcea, udata_exprs in udata_info.items():
            # print("udata-expr: %s" % udata_exprs)
            for udata_expr in udata_exprs:
                taint_src = udata_expr.expr.taint_source
                if udata_expr.expr.flag & 0x4000 and taint_src:
                    print("udata-expr: %s %x" % (udata_expr, udata_expr.expr.flag))
                    ast = udata_expr.expr.ast
                    if 'open' in str(ast) and taint_src not in taint_sources:
                        print("Found open-file source: %x" % (taint_src))
                        taint_sources.append(taint_src)

        return taint_sources
