#!/usr/bin/env python

from .data_collector import weaks_copy, weaks_command_exec, weaks_copy_length, weaks_only_length, weaks_loop


class SecurityCheck(object):

    def __init__(self, collector):
        self.collector = collector

        self.max_length = 0

        self.weaks = {}
        self.weaks_exec = set()
        self.weaks_length = set()

        self.sinks = ['strcpy', 'strncpy', 'memcpy', 'memmove', 'sprintf', 'sscanf', 'strcat', 'strncat', 'system', 'popen', 'execve', '_system']
        self.weaks_info = {}

    # DEUBG
    def print_weaks(self):
        for addr, stack_offsets in self.weaks.items():
            print("weak-copy: 0x%x %s" % (addr, stack_offsets))

        for addr in self.weaks_exec:
            print("weak-system: 0x%x" % (addr))

        for addr, cons_exprs in weaks_only_length.items():
            for cons_expr in cons_exprs:
                print("weak-copy-length: 0x%x %s with-ocns: %s" % (addr, cons_expr, cons_expr.constraints))


    def check_taint_security(self):
        """
        Check the taint security for different vulnerability model.
        """
        # print(weaks_copy)
        # print(weaks_copy_length)
        self.filter_fake_source()

        self.guess_max_taint_length()

        self.check_weaks_copy()

        self.check_weaks_command_exec()

        print("Guess-max-length: %d" % (self.max_length))


    def check_weaks_copy(self):
        for loc, weak_exprs in weaks_copy.items():
            for weak_expr in weak_exprs:
                self.check_cons_expr(weak_expr)
                try:
                    print("check-weak-copy: 0x%x %s (%s) with %s %x inter-level(icall): %d(%d) %s" %
                          (loc, weak_expr, id(weak_expr), weak_expr.constraints, weak_expr.expr.taint_source, len(weak_expr.inter_funcs), weak_expr.inter_icall_level, weak_expr.inter_funcs))
                except:
                    print("ERROR-%x %s" % (loc, weak_expr))
                print("  with-cons: %s" % (weak_expr.cons_ids))
                has_sym_cons = self.get_symbol_constraint(weak_expr.constraints)
                if has_sym_cons:
                    continue
                min_constraint = self.get_min_constraint(weak_expr.constraints)
                print("  -->min_constraint: %s" % (min_constraint))
                taint_ast = weak_expr.expr.ast

                # stack_addr = taint_ast.args[0]
                # stack_offset = 0x7fffffff - stack_addr
                # if stack_offset >= 0xffff or stack_offset < 0:
                #     continue

                memory_size = weak_expr.expr.memory_size
                if taint_ast.op == 'BVV':
                    stack_addr = taint_ast.args[0]
                    offset = 0x7fffffff - stack_addr
                elif memory_size:
                    offset = memory_size
                else:
                    continue
                if offset > 0xfffff or offset < 0:
                    continue

                # if min_constraint is None or min_constraint >= stack_offset:
                if ((min_constraint is None and len(weak_expr.cons_ids) == 0) or
                        (min_constraint is None and self.max_length and self.max_length >= offset) or
                        (min_constraint is None and self.max_length == 0) or
                        (min_constraint and min_constraint >= offset)):
                    if loc not in self.weaks:
                        self.weaks[loc] = set()
                    self.weaks[loc].add(offset)

                    if loc not in self.weaks_info:
                        self.weaks_info[loc] = (len(set(weak_expr.inter_funcs)), weak_expr.inter_icall_level, weak_expr.taint_propagaton_level, weak_expr.loop_num)

        for loc, weak_exprs in weaks_copy_length.items():
            for weak_expr in weak_exprs:
                self.check_cons_expr(weak_expr)
                print("check-weak-copy-with-lenth: 0x%x %s with %s" % (loc, weak_expr, weak_expr.constraints))
                print("  with-cons: %s" % (weak_expr.cons_ids))
                has_sym_cons = self.get_symbol_constraint(weak_expr.constraints)
                if has_sym_cons:
                    continue
                min_constraint = self.get_min_constraint(weak_expr.constraints)
                # print("get-min-cons: 0x%x %s with %s" % (loc, weak_expr, min_constraint))
                taint_ast = weak_expr.expr.ast
                memory_size = weak_expr.expr.memory_size
                if taint_ast.op == 'BVV':
                    stack_addr = taint_ast.args[0]
                    offset = 0x7fffffff - stack_addr
                elif memory_size:
                    offset = memory_size
                else:
                    continue
                if offset > 0xfffff or offset < 0:
                    continue

                # print("offset: %d" % (offset))
                # if min_constraint is None or min_constraint >= offset:
                if ((min_constraint is None and len(weak_expr.cons_ids) == 0) or
                        (min_constraint is None and self.max_length and self.max_length >= offset) or
                        (min_constraint is None and self.max_length == 0) or
                        (min_constraint and min_constraint >= offset)):
                    if loc not in self.weaks:
                        self.weaks[loc] = set()
                    self.weaks[loc].add(offset)

                    if loc not in self.weaks_info:
                        self.weaks_info[loc] = (len(set(weak_expr.inter_funcs)), weak_expr.inter_icall_level, weak_expr.taint_propagaton_level, weak_expr.loop_num)

    def check_cons_expr(self, trace_expr):
        """
        Check the string copy's length.
        """
        if len(trace_expr.cons_ids) == 0:
            return

        for cons_id in trace_expr.cons_ids:
            if cons_id in self.collector.constraints:
                cons_exprs = self.collector.constraints[cons_id]
                for cons_expr in cons_exprs:
                    cons_ast = cons_expr.expr.ast
                    if cons_ast.op == 'BVV':
                        cons_value = cons_ast.args[0]
                        if cons_value:
                            trace_expr.constraints.append(cons_value)
                    elif 'S' not in trace_expr.constraints:
                        trace_expr.constraints.append('S')

    def check_weaks_command_exec(self):

        for loc, weak_exprs in weaks_command_exec.items():
            if len(weak_exprs):
                self.weaks_exec.add(loc)

                weak_expr = weak_exprs[0]
                if loc not in self.weaks_info:
                    self.weaks_info[loc] = (len(set(weak_expr.inter_funcs)), weak_expr.inter_icall_level, weak_expr.taint_propagaton_level, weak_expr.loop_num)
                    print("check-command-injection: %x %s" % (loc, weak_expr.inter_funcs))

    def get_min_constraint(self, constraints):

        concret_cons = [c for c in constraints if type(c) is int and c != 0 and c != 1]
        return min(concret_cons) if len(concret_cons) else None

    def get_symbol_constraint(self, constraints):

        return any([c for c in constraints if type(c) is str and c != 'Y'])

    def guess_max_taint_length(self):
        """
        Guess the max tainted data read length.
        This may affect true vulnerability discovery.
        We set the min length = 0x2000
        """
        min_length = 0x2000
        for alias_id, cons_exprs in self.collector.constraints.items():
            for cons_expr in cons_exprs:
                print("collector-cons: %s %s %s %s" % (alias_id, cons_expr, cons_expr.expr.source, cons_expr.expr.invariant_loc))
                cons_ast = cons_expr.expr.ast
                if cons_ast.op == 'BVV':
                    cons_value = cons_ast.args[0]
                    if cons_value and cons_value >= min_length and cons_value >= self.max_length:
                        self.max_length = cons_value

    def filter_fake_source(self):
        """
        Filter the fake taint source in fread/read/fgets while the stream if from fopen.
        """
        print("\nStart-filter-fake-source")
        fake_sources = self.get_file_open_taint_sources()

        for loc, taint_exprs in weaks_copy.items():
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    # print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_copy_length.items():
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                # print("weak-copy-with-length: %s" % (taint_expr))
                if taint_expr.expr.taint_source in fake_sources:
                    # print("Found-fake-taint: %s %x" % (taint_expr, taint_expr.expr.taint_source))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_only_length.items():
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                if taint_expr.expr.taint_source in fake_sources:
                    # print("Found-fake-taint: %s %x" % (taint_expr, loc))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        for loc, taint_exprs in weaks_command_exec.items():
            fake_taint_exprs = []
            for taint_expr in taint_exprs:
                print("command-expr: %s %x" % (taint_expr, taint_expr.expr.taint_source))
                if taint_expr.expr.taint_source in fake_sources:
                    print("Found-fake-taint: %s %x" % (taint_expr, taint_expr.expr.taint_source))
                    fake_taint_exprs.append(taint_expr)

            for fake_expr in fake_taint_exprs:
                taint_exprs.remove(fake_expr)
            fake_taint_exprs.clear()

        # print("weaks-copy: %s" % (weaks_copy))
        # print("weaks-copy-with-length: %s" % (weaks_copy_length))

    def get_file_open_taint_sources(self):
        """
        Get the source fread/read/fgets's stream.
        """
        fake_sources = set()
        true_sources = set()
        udata_info = self.collector.datas['uData']

        for funcea, udata_exprs in udata_info.items():
            for udata_expr in udata_exprs:
                print("%x-has-source %s flag %x" % (funcea, udata_expr, udata_expr.expr.flag))
                taint_src = udata_expr.expr.taint_source
                taint_srcs = udata_expr.expr.taint_sources
                if taint_src:
                    taint_srcs.add(taint_src)
                cons_type = udata_expr.expr.cons_type
                ast = udata_expr.expr.ast
                if taint_srcs:
                    for src in taint_srcs:
                        print("  -->taint-src:%x" % (src))
                else:
                    print("Error")
                if udata_expr.expr.flag & 0x4000 and len(taint_srcs):
                    # print("udata-expr: %s %x %d" % (udata_expr, udata_expr.expr.flag, udata_expr.expr.cons_type))
                    if cons_type == 0x11:
                        true_sources |= taint_srcs
                        # true_sources.add(taint_src)
                        # print("Found socket source: %s" % (taint_srcs))
                    elif (cons_type == 0x8 or 'open' in str(ast)):
                        # print("Found open-file source: %s" % (taint_srcs))
                        fake_sources |= taint_srcs
                        # fake_sources.add(taint_src)

        for t_source in true_sources:
            if t_source in fake_sources:
                fake_sources.remove(t_source)
        for fake_src in fake_sources:
            print("Fake-source: %x" % (fake_src))
        return fake_sources
