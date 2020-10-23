#!/usr/bin/env python

import claripy
import pyvex
import time
import json
import string
import hashlib
from collections import defaultdict
import itertools

from .binary_info import BinaryInfo
from .variable_expression import VarExpr, TraceExpr, RecursiveExpr
from .function_object import FunctionAttribute
from .loopfinder import LoopFinder
from .graph_method import GraphMethod, TemporaryNode, ContainerNode
from .code_location import CodeLocation
from .generate_cfg import FunctionCFG
from .data_process import DataParser
from .parse_ast import *
from .vex_process import EngineVEX, Action
from .accurate_data_flow import function_store_defs, backward_tmp_exprs, record_backward_exprs, record_remaining_exprs, record_redef_labels, symbolic_count
from .taint_source_config import TaintSource
from dataflow.procedures import SIM_PROCEDURES
from .variable_type import *
from .merge_expressions import *
from .call_context import *
from .global_config import *

import logging
l = logging.getLogger("data_trace")
# l.setLevel('INFO')
# l.setLevel('DEBUG')


# DEUBG - ignore functions
ignore_function = [0x12194, 0x1607c, ]


# OPTIONS
# DEBUG = False
DEBUG = True
TEST_RET = False
alias_check = False
icall_check = False
user_check = False
taint_check = False
trace_heap_ptr = False

push_use_level = 0    # (0: None, 1: partial, 2: all)
push_def_level = 0    # (0: None, 1: partial, 2: all)


MAX_LOOPS = 40
B_MAX_LOOPS = 3
F_MAX_LOOPS = 3

FUNC_MAX_TIMES = 15
function_analyzed_times = defaultdict(int)

support_data_types = ['Vptr', 'Iptr', 'Fptr', 'Arg', 'Aptr', 'Ret', 'Rptr']

collect_summary_use_exprs = defaultdict(list)
collect_summary_def_exprs = defaultdict(list)


# collect_vptr_exprs = {}
# collect_fptr_exprs = {}
# collect_exprs = {}

# function_record_new_backward = defaultdict(int)
# function_record_new_forward = defaultdict(int)
function_trace_record = defaultdict(int)

custom_block_trace_record = set()

# custom_sources = ['FCGX_GetParam', 'hdf_get_value', 'httpGetEnv']
custom_sources = []

class FastSearch(BinaryInfo):
    def __init__(self, project, binary_parser,
                 ida_object,
                 accurate_dataflow,
                 fast_dataflow,
                 collector,
                 call_graph,
                 start_functions=None,
                 blocks_data_info=None,
                 search_locations=None,
                 user_sinks=None,
                 libary_objects=None,
                 icall_check=False,
                 taint_check=False,
                 switch_check=False,
                 debug=False,
                 **kwargs):

        super(FastSearch, self).__init__(project)

        self._binary_parser = binary_parser
        self._ida_object = ida_object
        self._accurate_dataflow = accurate_dataflow
        self._fast_dataflow = fast_dataflow

        self._libary_objects = libary_objects if libary_objects else {}

        self.collector = collector
        self._call_graph = call_graph

        self.icall_check = icall_check
        self.taint_check = taint_check
        self.switch_check = switch_check
        self.debug = debug

        self.options = kwargs

        self._start_functions = start_functions

        self._blocks_data_info = blocks_data_info

        self._search_locations = search_locations if search_locations else {}
        self._user_sinks = user_sinks if user_sinks else {}

        self._source_initial = None

        self._loop_parser = LoopFinder()

        self._traces_block = defaultdict(int)
        self._function_start_nodes = {}

        self._sim_procedures = {}
        self.new_operators = ['_Znwm', '_Znam', 'malloc']
        self.function_return_exprs = defaultdict(list)
        self.libc_functions = ['strpbrk', 'strsep', 'strlen', 'BIO_read', 'fread', 'strncpy', 'strcmp', 'j___aeabi_uidivmod', 'strcpy', 'memmove']
        self.ignore_lib_functions = ['syslog']
        self.taint_source = ['BIO_read', 'recv', 'recvfrom', 'SSL_read', 'fgets', 'fread', 'read', 'BIO_gets', 'getenv']
        self.taint_source += custom_sources

        self.record_new_forward_nodes = []
        self.record_new_backward_nodes = []

        # Start search variable expression
        time_start = time.time()
        self._analyze()
        print("Total time ---> %lf" % (time.time()-time_start))

    # DEBUG

    def _debug_print_results(self):
        print("#"*30 + "Result!" + "#"*30)
        for funcea, exprs in collect_icall_exprs.items():
            print("  Icall: %x" % (funcea))
            for expr in exprs:
                print("%s %s" % (expr.expr.source, expr))

        for funcea, exprs in collect_ptr_exprs.items():
            print("  Ptr: %x" % (funcea))
            for expr in exprs:
                print("%s %s" % (expr.expr.source, expr))

    def _test_function_result(self, function):
        for addr, node in function.cfg._nodes.items():
            print(node)
            for expr in node.done_exprs:
                print("Block 0x%x has %s" % (addr, expr))
                if hasattr(expr, "base"):
                    print("expr %s has base %s" % (expr, expr.base))

    def _test_graph_method(self):
        addr = 0x2d7cf0
        function = self._cfg.functions_manager[addr]
        func_cfg = function.cfg
        time_start = time.time()
        graph_parser = GraphMethod(func_cfg, addr)
        # print("Parse graph cost time: %lf" % (time.time() - time_start))
        pdom_tree = graph_parser.get_post_dominators()
        # for edge in pdom_tree.edges():
        #     print edge
        start_node = func_cfg.get_node_by_addr(0x2d7cf0)
        # for node in pdom_tree.nodes():
        #     if node._obj == start_node:
        #         print node, node.index

        # start_node = TemporaryNode("start_node")
        post_doms = graph_parser.get_node_pdom(start_node)
        # print post_doms

        test_node1 = func_cfg.get_node_by_addr(0x2d8e3f)
        test_node2 = func_cfg.get_node_by_addr(0x2d8e84)

        r = graph_parser.judge_post_dome(start_node, test_node1)
        # print r
        r = graph_parser.judge_post_dome(test_node1, test_node2)
        # print r

    def _test_print_argument_define(self, argument_def_exprs):
        print("\nDEBUG test --> argument define --")
        for expr in argument_def_exprs:
            print(expr.source, expr)

    def _test_function_return_value(self):
        for addr, ret_exprs in self.function_return_exprs.items():
            print("0x%x has ret %s" % (addr, ret_exprs))

    def _test_context_infect(self, function, exprs, text):
        print("\n" + "#"*10 + text + " %x " % (function.addr) + "#"*10)
        for expr in exprs:
            print("%s %s" % (expr, expr.expr.sims))
        print("")

    def _save_tmp_result(self, file_name, results):
        with open(file_name, "w") as fp:
            json.dump(results, fp, indent=4)

    def _test_taint(self, function):

        print("custome initial %s" % (function))
        input_taints = []
        funcea = function.addr
        # <T-Expr <BV32 Store(((Load(0xa89b8) + 0xc) + 0x4))> (F-0)>
        # value = BVV(0xa89b8)
        # ld_ptr = claripy.Load(value, 32)
        # offset = BVS('o')
        # data_ast = claripy.Store(ld_ptr+0x8, 32)
        # data_ast = data_ast.replace(ld_ptr, ld_ptr+offset)
        # data_ast2 = data_ast.replace(BVV(0x8, 32), BVV(0x4, 32))
        # print(data_ast, data_ast2)

        # data_ast = BVS('r8')
        # data_ast = claripy.Store(data_ast, 32)

        # <T-Expr <BV64 Load(Store(Load(Load(Load(0x124333790) + 0x18) + o4) + 0x8) + 0x10)> (4902303632) (ptr) (B-75)>
        value = BVV(0x124333790, 64)
        data_ast = claripy.Load(value, 64)
        data_ast = claripy.Load(data_ast+BVV(0x18, 64), 64)
        data_ast = claripy.Load(data_ast+BVS('o4', 64), 64)
        data_ast = claripy.Store(data_ast+BVV(0x8, 64), 64)
        data_ast = claripy.Load(data_ast+BVV(0x10, 64), 64)

        base_ptr = 0x124333790
        # base_ptr = 'r8'
        loc = CodeLocation(funcea, 0)
        expr = VarExpr(data_ast, pattern='SLBF', trace_dir='F', data_type='Tdata', var_type='ptr', base_ptr=base_ptr)

        expr.initial_sims()
        # expr.sims['r8'].var_type = 'ptr'
        sim_actions = self._accurate_dataflow.create_sim_actions(data_ast, loc, 'ptr')
        expr.sim_actions = sim_actions
        # print(sim_actions)

        expr.source = loc
        expr.alias_id = hash((loc, 'SLBF'))
        expr.flag |= 0x100

        trace_expr = TraceExpr(expr, 0)
        # start_block.forward_exprs.append(trace_expr)
        input_taints.append(trace_expr)
        # function.input_global_taints[base_ptr] = input_taints
        # print("cus-initial: %s %s" % (function, trace_expr))

        # trace_expr2 = trace_expr.replace('r8', 'r12', rep_type='ptr', base_ptr='r12')
        # sim_actions = self._accurate_dataflow.create_sim_actions(data_ast2, loc, 'ptr')
        # trace_expr2 = trace_expr.replace(data_ast, data_ast2, sim_actions, base_ptr=0xa89b8, rep_info={0xa89b8: 'ptr'})
        # trace_expr2.expr.sim_actions = sim_actions
        # trace_expr2.index = 0
        # trace_expr2.expr.trace_dir = 'F'
        # start_block.forward_exprs.append(trace_expr2)

        data_ast = BVS('r24') + 0x36c
        base_ptr = 'r24'
        loc = CodeLocation(funcea, 0)
        expr = VarExpr(data_ast, pattern='SLBF', trace_dir='F', data_type='Tdata', var_type='ptr', base_ptr=base_ptr)
        expr.initial_sims(var_type='ptr')
        expr.source = loc
        expr.alias_id = hash((loc, 'SLBF'))
        expr.flag |= 0x100
        expr.taint_source = 0
        trace_expr = TraceExpr(expr, 0)
        function.start_node.forward_exprs.append(trace_expr)

        # data_ast = BVS('r24')
        # base_ptr = 'r24'
        # loc = CodeLocation(funcea, 0)
        # expr = VarExpr(data_ast, value=data_ast, pattern='SLBF', trace_dir='F', data_type='Aptr', var_type='ptr', base_ptr=base_ptr)
        # expr.initial_sims(var_type='ptr')
        # expr.source = loc
        # expr.alias_id = hash((loc, 'SLBF'))
        # # expr.flag |= 0x100
        # trace_expr = TraceExpr(expr, 0)
        # function.start_node.forward_exprs.append(trace_expr)



    #
    # private method
    #

    def _custom_reconstruct_cfg(self):
        """
        After infer all idirect call, then re-construct the control flow graph.
        """
        # Icall in 0x1f9a0
        # <Block 0x2115c->iCall (0x1f9a0)>
        # <Block 0x212d8->iCall (0x1f9a0)> -> 0x2cd44

        self._ida_object.icall_targets[0x65f0][0x6710] = 0x895c
        # self._ida_object.icall_targets[0x1f9a0][0x212d8] = 0x2cd44

        ida_cfg = self._ida_object.ida_cfg
        call_graph = self._ida_object.cg

        # for func in call_graph.graph.nodes():
        #     print(func)

        function = call_graph.get_function_by_addr(0x65f0)
        print(function)

        # function.icall_targets[0x2120c] = 0x2d228

        callees = call_graph.graph.successors(function)
        # for callee in callees:
        #     print(callee)

        icall_func = call_graph.get_function_by_addr(0x895c)
        print(icall_func)

        kwargs = {'jumpkind': 'Call'}
        call_graph.graph.add_edge(function, icall_func, **kwargs)

    def _reconstruct_cfg(self):
        """
        After infer all idirect call, then re-construct the control flow graph.
        """
        self._ida_object.load_icall_info()
        self._ida_object.add_icall_edge()

    def _analyze(self):

        self._initial_lib_procedures()

        if self.icall_check:
            self._reconstruct_cfg()
            self._analyze_binary(do_recursive_call=True)
            self.collector.parse_icall_targets_v1()
            # self.collector.parse_function_ptr()
            # self.collector.parse_simple_function_ptr(self.proj)

        elif self.switch_check:
            self._analyze_binary(do_recursive_call=False)
            self.collector.parse_switch_targets(self._ida_object.cg, self.proj)

        elif self.taint_check:
            do_recursive_flag = False
            self._reconstruct_cfg()
            self._analyze_binary(do_recursive_call=True)

        else:
            return

    def _analyze_binary(self, do_recursive_call=True):

        if not self._start_functions:
            self._start_functions = self._ida_object.cg.get_start_nodes()

        call_graph = self._ida_object.cg
        # for function in call_graph.graph.nodes():
        #     print("Has-function: %s" % (function))
        # return

        if do_recursive_call:
            self._loop_parser.get_loops_from_call_graph(call_graph)
            for call_loop in call_graph.loops:
                if len(call_loop.start_nodes) == 0:
                    self._start_functions.add(call_loop.first_node)
                # print(call_loop, call_loop.first_node, call_loop.start_nodes)

        data_parser = DataParser(self._accurate_dataflow)
        alias_check_functions = set()

        icall_functions = set()
        analyzed_functions = set()

        for start_function in self._start_functions:

            print("\nStart-analyze: %s\n" % (start_function))
            # if start_function.addr not in [0x1e1b0]:
            #     continue

            tree_nodes = call_graph.get_all_nodes_by_root(start_function)
            # for node in tree_nodes:
            #     print("  Has-tree-node: %s" % (node))
            # continue

            worklist = []
            call_graph.get_pre_sequence_call_graph(start_function, tree_nodes, worklist)
            # for node in worklist:
            #     print(" ->worklist has: %s" % (node))
            # print("From-start-func: %s has %d" % (start_function, len(worklist)))
            # continue

            for i in range(len(worklist)-1, -1, -1):
                function = worklist[i]

                # DEBUG
                print("Analyze-%x" % (function.addr))
                # print("name: %s" % (function.procedural_name))
                # continue

                # should_check_alias = False
                funcea = function.addr
                # if function_analyzed_times[funcea] >= FUNC_MAX_TIMES:
                if funcea in analyzed_functions:
                    # print("Has-analyzed-%x" % (funcea))
                    continue

                # DEBUG
                if funcea in ignore_function:
                    continue

                function_block_info = self._blocks_data_info.get(funcea)
                search_info = self._search_locations.get(funcea)
                user_sinks = self._user_sinks.get(funcea)
                contain_source = self._get_taint_sources(function)
                # print("containt-taint-source: %s" % (contain_source))
                # print("block-info: %s" % (function_block_info))

                if self.debug:
                    # if funcea not in [0x1cfb4]:
                    #     continue
                    self._pre_process_function(function)
                    # print("Done: %s" % (function))

                    continue
                    # if funcea in [0x120075ca8, 0x12009F308, 0x1200955D4, 0x7c064, 0x4cee0, 0x52db4]:
                    if funcea in [0x416468]:
                        self._test_taint(function)
                        # debug
                    # else:
                    #     continue

                elif alias_check and function.procedural_name in ['NOALIAS', 'MAYALIAS', 'MUSTALIAS']:
                    if funcea not in alias_check_functions:
                        self._initialize_alias_check(function, data_parser)
                        alias_check_functions.add(funcea)

                    continue

                elif (self.icall_check or self.switch_check) and function_block_info:
                    self._pre_process_function(function)

                elif user_check and (search_info or user_sinks):
                    self._pre_process_function(function)

                elif TEST_RET:
                    self._pre_process_function(function)

                elif self.taint_check and contain_source:
                    self._pre_process_function(function)

                elif function.cfg is None:
                    continue

                if (self.icall_check or self.switch_check) and function_block_info and funcea not in icall_functions:
                    data_parser.pre_process_function_data(function_block_info)
                    icall_functions.add(funcea)

                if user_check:
                    if search_info:
                        self._initialize_custom_search(function, search_info, data_parser)

                    if user_sinks:
                        self._initialize_custom_sinks(function, user_sinks, data_parser)

                if TEST_RET and function.cfg:
                    self.backward_trace_ret(function)

                if function.cfg is None:
                    continue

                analyzed_functions.add(funcea)
                self._execute_function(function, execute_flag=0x1)


    def _execute_function(self, function, callsite=None, collect_ret=False, execute_flag=0):

        # print("Execute-function: %s %d" % (function, execute_flag))
        funcea = function.addr
        function_analyzed_times[funcea] += 1
        function_trace_record[funcea] = 0
        function.flag = execute_flag
        function.trace_dir = None

        # DEBUG
        if funcea in ignore_function:
            return

        # for node in function.cfg.pre_sequence_nodes:
        #     print("node: %s" % (node))
        # return

        # print("OOO-analyze function %s" % (function))
        analyzed_count = function_analyzed_times[funcea]

        self.collector.analyzed_functions.add(funcea)

        if self.taint_check:
            print("\nGTaint in %s" % (function))
            for base_addr, taint_exprs in function.input_global_taints.items():
                for g_taint_expr in taint_exprs:
                    print(" -->global-taint: %x %s %s" % (base_addr, g_taint_expr, g_taint_expr.constraints))
            # if len(function.input_global_taints) > 300:
            #     print("Too many tiants")
            #     debug

        count = 1
        while True:
            print("="*55 + "analyze-function %x - %d (all-%d - flag-%x)" % (funcea, count, analyzed_count, execute_flag) + '='*55)

            """
            Let's do a forward analysis, then we do a backward analysis.
            """
            if execute_flag != 0x1:
                function.trace_dir = 'F'
                self._forward_data_flow_analysis(function)
                function_trace_record[funcea] &= 0x1

                if (function_trace_record[funcea] & 0x3):
                    function.trace_dir = 'B'
                    self._backward_data_flow_analysis(function)
                    function_trace_record[funcea] &= 0x2

                count += 1
                if count > 10:
                    break
                if function_trace_record[funcea] & 0x2 == 0:
                    break
            else:

                """
                Let's do a backward analysis, then we do a forward analysis.
                """
                function.trace_dir = 'B'
                self._backward_data_flow_analysis(function)
                function_trace_record[funcea] &= 0x2

                if (function_trace_record[funcea] & 0x3):
                    function.trace_dir = 'F'
                    self._forward_data_flow_analysis(function)
                    function_trace_record[funcea] &= 0x1

                count += 1
                if count > 10:
                    break
                if function_trace_record[funcea] & 0x1 == 0:
                    break

        for loop in function.loops:
            loop.analyzed_times = 0

        # self._remove_incorrect_exprs(function)

        if self.switch_check:
            self._collect_switch_analysis_results(function)
            return

        self._collect_analysis_results(function, execute_flag)
        self._collect_result_in_exit_blocks(function, execute_flag)

        # self._update_expr_from_callees(function)

        if self.icall_check:
            self._update_value(function)

        # Kai add in 2019/10/08
        if execute_flag == 0x1:
            self._push_callee_exprs_to_callsite(function)
            # self._push_callee_exprs_to_caller(function)


        # Clear the function's flag while the function has been analyzed done.
        function.flag = 0

        if self.taint_check:
            self._ida_object.cg.push_global_info(function)

        # if push_use_level == 0:
        #     self._push_function_use_expr_to_callsite(function)

        # if push_def_level == 0:
        #     self._push_funciton_def_expr_to_callsite(function)

        # if push_use_level or push_def_level:
        #     self._push_function_expr_to_caller(function)

        # self._parser_icall_expr(function)

        # if collect_ret:
        #     self._collect_ret_def_in_function(function)
            # ret_exprs = self.function_return_exprs.get(funcea)
            # if ret_exprs:
            #     self._merge_exprs(ret_exprs)

    def _initial_lib_procedures(self):
        for lib, procs in SIM_PROCEDURES.items():
            for name, proc in procs.items():
                # print(name, proc)
                self._sim_procedures[name] = proc()

    def _initial_stack_in_function_start(self, function):
        """
        pass
        """
        stack_reg = self._accurate_dataflow.sp_name
        arch_bits = self._accurate_dataflow.arch_bits
        start_block = function.start_node
        loc = CodeLocation(start_block.addr, 0)
        initial_action = Action('w', loc, stack_reg, stack_reg, arch_bits)
        initial_action.value = 0x7fffffff
        initial_action.src_type = 'S'
        initial_action.var_type = 'ptr'
        start_block.live_defs[stack_reg] = initial_action

        if self.proj.arch.name in ['MIPS64', 'MIPS32']:
            reg_offset = self.proj.arch.registers['t9'][0]
            value = function.addr
            self._initial_reg_value(start_block, reg_offset, value, 'ptr', 'G')

    def _initial_reg_value(self, block, reg_offset, value, var_type, src_type):
        """
        Initial register value.
        """
        reg_name = 'r%d' % (reg_offset)
        loc = CodeLocation(block.addr, 0)
        initial_action = Action('w', loc, reg_name, reg_name, self.arch_bits)
        initial_action.value = value
        initial_action.src_type = src_type
        initial_action.var_type = var_type
        block.live_defs[reg_name] = initial_action

    def _pre_process_function_vex(self, function):

        function_reg_defs = {}
        function_stack_defs = {}
        analyzed_blocks = set()
        analyzed_loops = set()
        pre_sequence_nodes = function.cfg.pre_sequence_nodes
        arguments = function.arguments

        # print("\npsu-debug: sequence %s\n" % (pre_sequence_nodes))
        self._initial_stack_in_function_start(function)

        for block in pre_sequence_nodes:
            # if block.addr not in [0x1cf1c, 0x1cf44]:
            #     continue
            if block in analyzed_blocks:
                continue

            # print("\ntest_block: %s in %s" % (block, function))
            # print(block.live_defs)

            if block.is_loop:
                loop = function.determine_node_in_loop(block)
                for block in loop.body_nodes:
                    if block in analyzed_blocks:
                        continue

                    analyzed_blocks.add(block)
                    if block.irsb:
                        self._accurate_dataflow.execute_block_irsb_v4(function, block, function_reg_defs, function_stack_defs, arguments)

                    else:
                        if block.node_type in ['Call', 'iCall', 'Extern']:
                            self._execute_callsite_node(function, block)
                            # self._execute_libc_callee_to_infer_type(function, block)

                    backward_trace_variable_type(function, block)
                    # function.sort_arguments()
                    # self._transfer_live_definitions(block, function)
                    self._accurate_dataflow.transfer_live_definitions(block)

                if loop not in analyzed_loops:
                    # print("Fast-analyze-loop: %s" % (loop))
                    analyzed_loops.add(loop)
                    ddg_graph = self._fast_dataflow.execute_loop(loop, loop_execute_times=3)
                    self._fast_dataflow.label_inc_flag_in_loop(function, ddg_graph)

            else:
                analyzed_blocks.add(block)
                if block.irsb:
                    self._accurate_dataflow.execute_block_irsb_v4(function, block, function_reg_defs, function_stack_defs, arguments)

                else:
                    if block.node_type in ['Call', 'iCall', 'Extern']:
                        self._execute_callsite_node(function, block)
                        # self._execute_libc_callee_to_infer_type(function, block)

                backward_trace_variable_type(function, block)
                # function.sort_arguments()
                # self._transfer_live_definitions(block, function)
                self._accurate_dataflow.transfer_live_definitions(block)

        function.correct_arguments()

        # for block in function.cfg.graph.nodes():
        #     print("vex-text: %s" % (block))
        #     for var, at in block.live_defs.items():
        #         print("%s  %s" % (var, at))

    def _initialize_custom_search(self, function, search_info, data_parser):
        """
        User custom data trace search point. the point is CodeLocation.
        """
        cfg = function.cfg

        for user_loc in search_info:
            block = cfg.get_node_by_addr(user_loc.block_addr)
            # print("block: %s" % (block))

            data_parser.inital_user_search(block, user_loc)

    def _initialize_custom_sinks(self, function, user_sinks, data_parser):
        """
        Initialize the sink function's arguments and trace them.
        """
        # print("psu-debug: user_sinks %s" % (user_sinks))
        cfg = function.cfg

        for callsite, arg_num in user_sinks.items():
            block = cfg.get_node_by_addr(callsite)
            # print("sink callsite block %s" % (block))

            data_parser.inital_user_sink_arguments(block, arg_num)

    def _initialize_alias_check(self, function, data_parser):
        """
        Initialize alias check, for example, the function MAYALIAS's arg.
        """
        callsites = self._get_all_callsites_to_function(function)
        # print("function %s has been called by %s" % (function, callsites))
        for callsite in callsites:
            # if not callsite.addr in [0xcff, 0xcd9]:
            if not callsite.addr in [0x98e]:
                continue
            data_parser.inital_alias_check_variables(callsite)

    def _get_pre_sequence_in_function(self, function):
        pre_sequence_nodes = []

        def _should_add_loop(cfg, loop, pre_sequence_nodes):
            # print("add_loop %s" % (pre_sequence_nodes))
            for s_node in loop.start_nodes:
                in_nodes = cfg.graph.predecessors(s_node)
                # print(in_nodes)
                for in_node in in_nodes:
                    if in_node not in pre_sequence_nodes and in_node not in loop.body_nodes:
                        return False
            return True

        cfg = function.cfg
        start_node = function.start_node
        pre_sequence_nodes.append(start_node)
        traversed_nodes = set()
        traversed_nodes.add(start_node)

        analyzed_loops = []
        worklist = [start_node]
        while worklist:
            block = worklist.pop()
            succ_blocks = cfg.graph.successors(block)
            for succ_block in succ_blocks:
                # print("psu-debug: %s has succ %s %s" % (block, succ_block, succ_block.is_loop))
                if succ_block.is_loop:
                    loop = function.determine_node_in_loop(succ_block)
                    if loop in analyzed_loops:
                        continue

                    # print("psu-debug: analyze loop %s" % (loop))
                    # analyzed_loops.append(loop)
                    choosed = _should_add_loop(cfg, loop, pre_sequence_nodes)
                    # print("loop %s %s, choosed %s" % (succ_block, loop, choosed))
                    if choosed:
                        analyzed_loops.append(loop)
                        for n in loop.start_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                        for n in loop.end_nodes:
                            if n not in traversed_nodes:
                                pre_sequence_nodes.append(n)
                                traversed_nodes.add(n)
                        # pre_sequence_nodes.extend(loop.start_nodes)
                        # pre_sequence_nodes.extend(loop.end_nodes)
                        worklist.extend(loop.end_nodes)

                else:
                    choosed = True
                    # pre_blocks = cfg.graph.predecessors(succ_block)
                    in_edges = cfg.graph.in_edges(succ_block)
                    if len(in_edges) >= 2:
                        for pre_block, _ in in_edges:
                            if pre_block not in pre_sequence_nodes:
                                choosed = False
                                break
                    if choosed:
                        # if succ_block.addr == 0x2bc5db:
                        #     print("add succ node %s" % (succ_block))
                        #     print("block %s, pre blocks %s" % (block, pre_blocks))
                        if succ_block not in traversed_nodes:
                            pre_sequence_nodes.append(succ_block)
                            worklist.append(succ_block)
                            # print("node %s has in sequence" % (succ_block))
                            traversed_nodes.add(succ_block)

        # print("Function: %s get sequences:\n %s" % (function, pre_sequence_nodes))
        return pre_sequence_nodes

    def _initialize_context_in_callsites(self, function):

        self._initialize_callsite_arguments(function)

        self._initialize_callsite_ret_pointer(function)

    def _initialize_callsite_arguments(self, function):
        callsite_arg_definitions = function.callsite_arg_definitions

        if len(callsite_arg_definitions) == 0:
            return

        for callsite, arg_definitions in callsite_arg_definitions.items():

            argument_info = self._get_argument_info_from_callee_definition(arg_definitions)
            trace_arguments = self._initialize_trace_argument(callsite, argument_info, trace_dir='B')
            callsite.backward_exprs.extend(trace_arguments)

    def _initialize_callsite_ret_pointer(self, function):
        callsite_ret_ptr_definitions = function.callsite_ret_definitions

        if len(callsite_ret_ptr_definitions) == 0:
            return

        for callsite in callsite_ret_ptr_definitions:

            # TODO
            # trace_ret_register = self._initialize_trace_ret_register(callsite)
            # callsite.forward_exprs.append(trace_ret_register)
            pass

    def _callsites_preprocess(self, function):
        """
        Preprocess all callsite in the function. Trace the arguments in callsite.
        """
        pre_sequence = function.cfg.pre_sequence_nodes

        for block in pre_sequence:
            # print("block: %s %s" % (block, block.node_type))

            if block.node_type == 'Call':
                callee_addr = block.target
                # if isinstance(callee_addr, int):
                    # print("%s call function 0x%x" % (block, callee_addr))

                # else:
                #     print("%s has icall" % (block))

            elif block.node_type == 'Extern':
                callee_addr = block.target
                # if isinstance(callee_addr, str):
                #     print("%s call lib %s" % (block, callee_addr))

                # else:
                #     pass

    def _update_expr_from_callees(self, function):
        """
        Update all expr from callee with the alias.
        """

        funcea = function.addr
        argument_use_alias = context_use_exprs.get(funcea)

        if argument_use_alias:
            self._update_use_expr_from_callee(function, argument_use_alias)

        argument_def_alias = context_def_exprs.get(funcea)

        if argument_def_alias:
            self._update_def_expr_from_callee(function, argument_def_alias)

    def _update_use_expr_from_callee(self, function, argument_use_alias):

        funcea = function.addr
        callsite_alias_info = {}

        for use_alias in argument_use_alias:
            # print("use_alias: %s " % (use_alias))
            value = use_alias.expr.value
            use_ast = use_alias.expr.ast
            cs_addr = use_alias.expr.source.block_addr

            if value is None or value.op != 'BVS':
                continue

            if cs_addr not in callsite_alias_info:
                callsite_alias_info[cs_addr] = {}

            if value.__hash__() != use_ast.__hash__():
                alias_info = callsite_alias_info[cs_addr]
                alias_name = value.args[0]

                if alias_name not in alias_info:
                    alias_info[alias_name] = []

                alias_info[alias_name].append(use_alias)

        # for addr, alias_info in callsite_alias_info.items():
            # print("%x has alias_info: %s" % (addr, alias_info))

        for addr, callsite_use_exprs in function.callee_use_exprs.items():
            # print("%x has callee exprs: " % (addr))

            arg_alias_info = callsite_alias_info.get(addr)

            if arg_alias_info is None:
                l.info("In calliste %x not found argument use alias, do it future!" % (addr))
                continue

            elif arg_alias_info:
                new_use_exprs = self._update_exprs_with_alias(arg_alias_info, callsite_use_exprs)

                # if len(new_use_exprs):
                #     print("%x the argument changed!" % (addr))

            else:
                # print("%x the argument not change!" % (addr))
                new_use_exprs = callsite_use_exprs

            function_use_exprs = collect_icall_exprs[funcea]
            for new_expr in new_use_exprs:
                # print("%x get new_expr: %s" % (addr, new_expr))
                function_use_exprs.append(new_expr)

    def _update_def_expr_from_callee(self, function, argument_def_alias):

        funcea = function.addr
        callsite_arg_alias_info = {}
        callsite_ls_alias_info = {}

        for def_alias in argument_def_alias:
            # print("def_alias: %s " % (def_alias))
            value = def_alias.expr.value

            if value is None:
                continue

            def_ast = def_alias.expr.ast
            cs_addr = def_alias.expr.source.block_addr

            if value.op == 'BVS':

                if cs_addr not in callsite_arg_alias_info:
                    callsite_arg_alias_info[cs_addr] = {}

                if value.__hash__() != def_ast.__hash__():
                    alias_info = callsite_arg_alias_info[cs_addr]
                    alias_name = value.args[0]

                    if alias_name not in alias_info:
                        alias_info[alias_name] = []

                    alias_info[alias_name].append(def_alias)

            else:

                if cs_addr not in callsite_ls_alias_info:
                    callsite_ls_alias_info[cs_addr] = {}

                if value.__hash__() != def_ast.__hash__():
                    alias_info = callsite_ls_alias_info[cs_addr]
                    alias_hash = value.__hash__()

                    if alias_hash not in alias_info:
                        alias_info[alias_hash] = []

                    alias_info[alias_hash].append(def_alias)

        if len(callsite_arg_alias_info):

            self._update_def_expr_with_arg_alias()

        if len(callsite_ls_alias_info):

            self._update_def_expr_with_ls_alias()

    def _update_def_expr_with_arg_alias(self, callee_trace_exprs, callsite_arg_alias_info, callsite_ls_alias_info):

        for addr, callsite_def_exprs in callee_trace_exprs.items():
            # print("callsite %x has callee exprs: " % (addr))

            arg_alias_info = callsite_arg_alias_info.get(addr)

            if arg_alias_info:
                new_def_exprs = self._update_exprs_with_alias(arg_alias_info, callsite_def_exprs)

            if arg_alias_info is None:
                l.info("In calliste %x not found argument def alias, do it future!" % (addr))
                continue

            elif arg_alias_info:
                new_def_exprs = self._update_exprs_with_alias(arg_alias_info, callsite_def_exprs)

                # if len(new_def_exprs):
                #     print("%x the argument changed!" % (addr))

            else:
                # print("%x the argument not change!" % (addr))
                new_def_exprs = callsite_def_exprs

            function_def_exprs = collect_ptr_exprs[funcea]
            for new_expr in new_def_exprs:
                # print("%x get new_expr: %s" % (addr, new_expr))
                function_def_exprs.append(new_expr)

    def _update_def_expr_with_ls_alias(self):
        pass

    def _update_expr_with_alias_bak(self, trace_expr, arg_alias, ls_alias):
        """
        Update a trace expr with arg alias and ls (load/store) alias.
        :param trace_expr: the data trace expr
        :param arg_alias: alias info of the arguments (rdi, rsi, rbx ...)
        :param ls_alias: alias info of the load/store data (load(rdi + 0x8))
        """
        # print("updata expr %s" % (trace_expr))

        sims = trace_expr.expr.sims
        trace_data = trace_expr.expr.ast
        choose_arg_name = [a for a in arg_alias if a in sims]
        choose_ls_hash = self._get_ls_hash_with_ls_alias(trace_data, ls_alias)

        arg_new_datas = []

        if len(choose_arg_name):

            all_alias_pairs = self._get_all_alias_pairs(choose_arg_name, arg_alias)

            # print("All alias pairs: %s" % (all_alias_pairs))

            for alias_info in all_alias_pairs:

                new_trace_data = trace_data
                replace_count = 0

                for alias_name, alias_expr in alias_info:
                    arg_ast = alias_expr.expr.value
                    alias_data = alias_expr.expr.ast
                    new_trace_data = new_trace_data.replace(arg_ast, alias_data)
                    replace_count += 1

                if replace_count == len(alias_info):
                    arg_new_datas.append(new_trace_data)

                else:
                    l.info("Update expr %s with alias %s error!" % (trace_expr, alias_info))

        new_trace_datas = []

        if len(arg_new_datas) == 0:
            new_trace_datas.append(trace_data)

        else:
            new_trace_datas = arg_new_datas

        ls_new_datas = []

        if len(choose_ls_hash):
            for new_data in new_trace_datas:

                all_alias_pairs = self._get_all_alias_pairs(choose_ls_hash, arg_alias)

                for alias_info in all_alias_pairs:

                    new_trace_data = new_data
                    replace_count = 0

                    for alias_hash, alias_expr in alias_info:
                        value = alias_expr.expr.value
                        alias_data = alias_expr.expr.ast
                        new_trace_data = new_trace_data.replace(value, alias_data)
                        replace_count += 1

                    if replace_count == len(alias_info):
                        ls_new_datas.append(new_trace_data)

                    else:
                        l.info("Update expr %s with alias %s error!" % (trace_expr, alias_info))

        if len(ls_new_datas):
            result_new_datas = ls_new_datas

        elif len(arg_new_datas):
            result_new_datas = arg_new_datas

        else:
            result_new_datas = []

        new_exprs = []
        for new_data in result_new_datas:

            # TODO
            new_expr = self._get_new_expr_with_ast(trace_expr, new_data)
            new_expr.expr.update_sims()
            new_exprs.append(new_expr)

        return new_exprs

    def _get_ls_hash_with_ls_alias(self, ast_data, ls_alias):

        choose_ls_hash = []

        for child_ast in ast_data.recursive_children_asts:

            if child_ast.op == 'Load':
                child_hash = child_ast.__hash__()

                if child_hash in ls_alias:
                    choose_ls_hash.append(child_hash)

        return choose_ls_hash

    def _pre_process_block_data(self, function, function_block_info):
        pass

    def _parser_icall_expr(self, function):
        funcea = function.addr

        # icall_exprs = collect_icall_exprs.get(funcea)
        # vptr_exprs = collect_ptr_exprs.get(funcea)
        icall_exprs = self.collector.datas['Iptr'].get(funcea)
        vptr_exprs = self.collector.datas['Vptr'].get(funcea)

        # print("psu-parse-icall: %s\n %s" % (icall_exprs, vptr_exprs))

        if icall_exprs is None or vptr_exprs is None:
            return

        for icall_expr in icall_exprs:
            source = icall_expr.expr.source
            icall_target = icall_expr.expr.ast

            func_id, virtual_id = 0, 0

            func_id = calculate_ast_struct_id(icall_target)
            # print("icall target: %s" % (icall_target))
            # print("func_id: %s" % (func_id))

            if icall_target.op == 'Load':
                vptr, offset = extract_vptr_and_offset(icall_target)

                if offset is None:
                    l.info("icall target %s not virtual function!" % (icall_target))

                else:
                    virtual_id = calculate_ast_struct_id(vptr)
                    # print("virtual_id: %s" % (virtual_id))

            for vptr_expr in vptr_exprs:
                vptr = vptr_expr.expr.ast
                vptr_id = calculate_ast_struct_id(vptr)
                # print("vptr: %s, with id: %s" % (vptr, vptr_id))

                if vptr_id == virtual_id:
                    l.info("Good, icall in %s find vtalbe %s : %s" % (source, vptr_expr, offset))

                elif vptr_id == func_id:
                    l.info("Good, icall in %s find target function %s" % (source, vptr_expr))

                else:
                    pass

    def _remove_incorrect_exprs(self, function):
        """
        Remove the incorrect exprs that caused by the backward store def.
        """
        may_remove_exprs = []
        alias_ids = set()

        start_node = function.start_node
        for expr in start_node.done_exprs:
            if expr.expr.trace_dir != 'B':
                continue

            flag = expr.expr.flag
            # print("done-expr: %s %s, flag: %x" % (expr.expr.source, expr, expr.expr.flag))

            if flag & 0x80 == 0x80:
                alias_ids.add(expr.expr.alias_id)

            elif flag & 1 == 1:
                may_remove_exprs.append(expr)

        # print("remove_incorrect_exprs:")
        # print(may_remove_exprs)
        # print(alias_ids)
        for r_expr in may_remove_exprs:
            if r_expr.expr.alias_id in alias_ids:
                # print('remove %s' % (r_expr))
                start_node.done_exprs.remove(r_expr)

    def _collect_analysis_results(self, function, execute_flag):

        start_node = function.start_node
        funcea = function.addr

        # print("Collect analysis results in function: %s" % (function))
        for trace_expr in start_node.done_exprs:
            print("start node-%x has: %s" % (start_node.addr, trace_expr))
            if trace_expr.expr.trace_dir != 'B':
                continue

            data_type = trace_expr.expr.data_type
            ast = trace_expr.expr.ast
            base_ptr = trace_expr.expr.base_ptr

            if trace_expr.argument_or_global():
                # print("start node %s collect: %s" % (start_node, trace_expr))
                #DEBUG
                # if data_type == 'Cons':
                #     print("Coll-cons: %s" % (trace_expr))

                if execute_flag == 0x2 and data_type == 'Tdata' and trace_expr.expr.flag & 0x200 == 0:
                    # print("Should collect callee taint (%x): %s, is-ret: %s, flag: %x" % (funcea, trace_expr, trace_expr.expr.is_ret, trace_expr.expr.flag))
                    self._accurate_dataflow.simplify_expr_v2(trace_expr)
                    function.taint_exprs.append(trace_expr)

                elif data_type in self.collector.datas:
                    self.collector.datas[data_type][funcea].append(trace_expr)
                    # print("1 %s" % (trace_expr))
                    # if data_type == 'Ret':
                    #     print("Add-to-collector: 0x%x %s %s" % (funcea, data_type, trace_expr))

                else:
                    l.info("The data type: %s is not support!" % (data_type))

            # elif data_type == 'tmp' and ast.op in ['BVV', 'BVS']:
            elif data_type == 'tmp' and not_contain_ls(ast):
                self.collector.datas[data_type][funcea].append(trace_expr)
                # print("2 %s" % (trace_expr))

            elif self.icall_check and type(base_ptr) is int and get_mem_permission(base_ptr) == 'stack' and data_type != 'Ret':
                self.collector.datas[data_type][funcea].append(trace_expr)
                # print("3 %s" % (trace_expr))

        if self.taint_check:
            self._find_taint_argument_constraint(function)
            merged_exprs = merge_simlilar_exprs_v1(function.taint_exprs)
            function.taint_exprs = merged_exprs
            # print("ooo->merged: %s\n %s" % (function.taint_exprs, merged_exprs))

        # Clear the done_exprs in start node, because the function will be
        # analyzed more times. The old done_exprs will affect analysis.
        if start_node not in function.cfg.exit_blocks:
            start_node.done_exprs.clear()

    def _collect_switch_analysis_results(self, function):
        """
        While analyze switch jmp, collect the results.
        """
        if not function.start_nodes:
            # print("The function %s has no start nodes...")
            return

        funcea = function.addr
        collect_exprs = set()
        for start_node in function.start_nodes:
            for trace_expr in start_node.done_exprs:
                if trace_expr.expr.trace_dir != 'B':
                    continue
                data_type = trace_expr.expr.data_type
                if data_type in self.collector.datas:
                    if trace_expr not in collect_exprs:
                        collect_exprs.add(trace_expr)
                        trace_expr = self._update_switch_trace_expr(function, trace_expr)
                        self.collector.datas[data_type][funcea].append(trace_expr)
                        # print("4 %s" % (trace_expr))

    def _collect_ret_def_in_function(self, function):
        # print("Collct ret def info in function %s" % (function))
        default_arguments = self._binary_parser.argument_vars
        for expr in function.start_node.done_exprs:
            # print("%s has done expr %s" % (function, expr))
            if expr.expr.trace_dir != 'B':
                continue

            if expr.expr.data_type == 'Ret':
                value = expr.expr.value
                if value is None:
                    continue

                if value.op == 'BVS':
                    if expr not in self.function_return_exprs[function.addr]:
                        self.function_return_exprs[function.addr].append(expr)
                else:
                    self.collector.datas['Ret'][function.addr].append(expr)

    def _collect_result_in_exit_blocks(self, function, execute_flag=0):
        """
        Collect ret pointer definition in function's exit blocks.
        """
        funcea = function.addr
        exit_blocks = function.cfg.exit_blocks

        for block in exit_blocks:
            if block.node_type in ['Call', 'iCall', 'Extern']:
                continue

            # print("Collect-Ret: %s" % (block))
            for trace_expr in block.done_exprs:
                sims = trace_expr.expr.sims
                ast = trace_expr.expr.ast
                pattern, data_type = trace_expr.expr.pattern, trace_expr.expr.data_type
                print("Ret-node-%x: has %s %s %s" % (block.addr, trace_expr, sims, data_type))

                if len(sims) == 1 and self.ret_name in sims and sims[self.ret_name].live:
                    if data_type == 'Aptr' and ast.op == 'Store':
                        trace_expr.expr.is_ret = True
                        self.collector.datas['Aptr'][funcea].append(trace_expr)

                    elif data_type == 'Tdata' and execute_flag == 0x2:
                        # print("Ret-taint: %s" % (trace_expr))
                        trace_expr.expr.is_ret = True
                        self._accurate_dataflow.simplify_expr_v2(trace_expr)
                        function.taint_exprs.append(trace_expr)
                        # print("should collect ret taint in (%x): %s" % (funcea, trace_expr))

                    elif data_type == 'Tdata' and execute_flag == 0x1:
                        trace_expr.expr.is_ret = True
                        self.collector.datas[data_type][funcea].append(trace_expr)
                        # print("5 %s" % (trace_expr))

                    elif data_type in ['Vptr', 'Fptr']:
                        trace_expr.expr.is_ret = True
                        self.collector.datas[data_type][funcea].append(trace_expr)
                        # print("6 %s" % (trace_expr))

                        self._collector_fptr_saved_to_sym_ret(funcea, trace_expr)

            block.done_exprs.clear()

    def _find_taint_argument_constraint(self, function):
        """
        In taint flow analysis, the argument in function maybe constraint for a tianted data.
        e.g. function(src, dst, n), the argument n is constraint.
        """
        if len(function.taint_exprs) == 0:
            return

        funcea = function.addr
        cons_exprs = self.collector.datas['Cons'].get(funcea)
        if cons_exprs is None:
            return

        # cons_info = {}
        arguments = function.arguments
        for cons_expr in cons_exprs:
            ast = cons_expr.expr.ast
            if (is_simple_arg_constraint(ast, arguments) and
                    cons_expr not in function.arg_constraints):
                function.arg_constraints.append(cons_expr)
                # cons_info[cons_expr.expr.alias_id] = cons_expr

        # print("Func-cons: %s %s" % (function, cons_info))
        # print("Arguments: %s" % (arguments))
        # for taint_expr in function.taint_exprs:
        #     for cons_id in taint_expr.cons_ids:
        #         print("T-cons: %s %s" % (taint_expr, cons_id))

    def _update_value(self, function):
        """
        Update the Dptr/Fptr expr's value.
        """
        funcea = function.addr
        tmp_info = self.collector.datas['tmp']
        tmp_exprs = tmp_info.get(funcea)
        if tmp_exprs is None or len(tmp_exprs) == 0:
            return

        # for tmp_expr in tmp_exprs:
        #     print("UUU-tmp-expr: %s" % (tmp_expr))

        new_tmp_exprs = simplify_exprs_v1(tmp_exprs)

        dptr_info = self.collector.datas['Dptr']
        dptr_exprs = dptr_info.get(funcea)

        fptr_info = self.collector.datas['Vptr']
        fptr_exprs = fptr_info.get(funcea)

        # if dptr_exprs is not None and len(dptr_exprs):
        #     self._update_ptrs_value(dptr_info, new_tmp_exprs)

        if fptr_exprs is not None and len(fptr_exprs):
            self._update_ptrs_value(fptr_exprs, new_tmp_exprs)

    def _update_ptrs_value(self, ptr_exprs, tmp_exprs):

        def contain_sym(ptr_value, tmp_value):
            if tmp_value.op == 'BVS' and tmp_value.args[0] in ptr_value.variables:
                return True
            return False

        new_exprs = []
        for ptr_expr in ptr_exprs:
            # print("HH-> %s" % (ptr_expr))
            ptr_ast = ptr_expr.expr.ast
            # if ptr_ast.op != 'Store':
            #     continue
            new_values = []
            if ptr_ast.op == 'Store':
                s_action = ptr_expr.expr.sim_actions[0]
                ptr_value = ptr_expr.expr.value
                new_values = []
                for tmp_expr in tmp_exprs:
                    tmp_value = tmp_expr.expr.value
                    tmp_ast = tmp_expr.expr.ast
                    tmp_loc = tmp_expr.expr.source
                    if tmp_loc in s_action.def_locs and contain_sym(ptr_value, tmp_value):
                        new_value = ptr_value.replace(tmp_value, tmp_ast)
                        new_values.append(new_value)
                        # print("HHHH-> %s" % (new_value))

            elif ptr_expr.expr.is_ret:
                ptr_value = ptr_expr.expr.value
                new_values = []
                for tmp_expr in tmp_exprs:
                    tmp_value = tmp_expr.expr.value
                    tmp_ast = tmp_expr.expr.ast
                    if contain_sym(ptr_value, tmp_value):
                        new_value = ptr_value.replace(tmp_value, tmp_ast)
                        new_values.append(new_value)

            if len(new_values) == 1:
                ptr_expr.expr.value = new_values[0]

            elif len(new_values) > 1:
                ptr_expr.expr.value = new_values[0]
                for new_value in new_values[1:]:
                    new_expr = ptr_expr.deep_copy()
                    new_expr.expr.value = new_value
                    new_exprs.append(new_expr)

            else:
                continue

        for new_expr in new_exprs:
            ptr_exprs.append(new_expr)

    def _update_switch_trace_expr(self, function, trace_expr):
        """
        In MIPS arch, the switch target correlate with registers (gp or sp).
        """
        start_block = function.start_node
        live_defs = start_block.live_defs
        trace_sims = trace_expr.expr.sims
        new_expr = trace_expr
        if self.sp_name in trace_sims:
            sp_at = live_defs[self.sp_name]
            sp_value = sp_at.value
            # print("sp_value: 0x%x" % (sp_value))
            new_expr = trace_expr.replace(self.sp_name, sp_value)

            sim_actions = new_expr.expr.sim_actions
            for i, sim_action in sim_actions.items():
                action_data = sim_action.action_data
                ls_addr = action_data.args[0]
                if action_data.op == 'Load' and ls_addr.op == 'BVV':
                    addr_value = ls_addr.args[0]
                    if get_mem_permission(addr_value) == 'stack' and addr_value in live_defs:
                        st_at = live_defs[addr_value]
                        if type(st_at.value) is int:
                            new_expr = new_expr.replace(action_data, st_at.value)

            # print("new_expr: %s" % (new_expr))

        if self.gp_name in trace_sims:
            gp_at = live_defs[self.gp_name]
            gp_value = gp_at.value
            # print("gp_value: 0x%x" % (gp_value))
            new_expr = trace_expr.replace(self.gp_name, gp_value)

        return new_expr

    def _collector_fptr_saved_to_sym_ret(self, funcea, trace_expr):
        """
        Replace the return value in trace_expr with sym funcea.
        :param funcea: the address of function.
        :param trace_expr: the fptr or vptr expr whose base pointer return value of function.
        """
        # print("Func Pointer save in ret pointer:\n %x %s" % (funcea, trace_expr))
        sym = 'ret_%x' % (funcea)
        new_expr = trace_expr.replace(self.ret_name, sym)
        # print("Rnew-> %s %s" % (new_expr, new_expr.expr.is_ret))
        self.collector.datas[trace_expr.expr.data_type][funcea].append(new_expr)

    def _kill_redefined_in_function(self, function, exprs, redefined_exprs, graph_parser):
        """
        In the function, a variable def may be redefined, we will remove teh killed expr.
        """
        func_cfg = function.cfg
        for expr1, expr2 in redefined_exprs:
            # print expr1, expr2
            n1 = func_cfg.get_node_by_addr(expr1.expr.source.block_addr)
            n2 = func_cfg.get_node_by_addr(expr2.expr.source.block_addr)
            killed = graph_parser.judge_post_dome(n1, n2)
            if killed:
                # define in node n1 is redefined in node n2
                # print("%s: %s is redefined by %s: %s" % (n1, expr1, n2, expr2))
                try:
                    exprs.remove(expr1)
                except ValueError:
                    l.info("expr %s has been remove" % (expr1))

            else:
                killed = graph_parser.judge_post_dome(n2, n1)
                if killed:
                    # define in node n2 is redefined in node n1
                    # print("%s: %s is redefined by %s: %s" % (n2, expr2, n1, expr1))
                    try:
                        exprs.remove(expr2)
                    except ValueError:
                        l.info("expr %s has been remove" % (expr2))

    def _get_callsite_arg_and_ret_alias(self, function, callsite_arg_alias, callsite_ret_ptr_alias):

        funcea = function.addr
        vptr_exprs = collect_ptr_exprs.get(funcea)

        if vptr_exprs is not None:
            for expr in vptr_exprs:
                if expr.expr.trace_dir != 'B':
                    continue

                if expr.expr.data_type == 'Arg':
                    callsite = expr.expr.source
                    callsite_arg_alias[callsite.block_addr].append(expr)

                elif expr.expr.data_type == 'Rptr':
                    callsite = expr.expr.source
                    callsite_ret_ptr_alias[callsite.block_addr].append(expr)

        ret_register_name = 'r%d' % (self._binary_parser.ret_offset)
        exit_blocks = function.cfg.exit_blocks
        for block in exit_blocks:
            for expr in block.done_exprs:
                if expr.contain_symbol(ret_register_name):
                    if expr.expr.data_type == 'Arg':
                        callsite = expr.expr.source
                        callsite_arg_alias[callsite.block_addr].append(expr)

                    if expr.expr.data_type == 'Rprt':
                        callsite = expr.expr.source
                        callsite_ret_ptr_alias[callsite.block_addr].append(expr)

    def _get_ret_pointer_defined(self, function):
        ret_def_exprs = []
        ret_register_name = 'r%d' % (self._binary_parser.ret_offset)
        exit_blocks = function.cfg.exit_blocks
        for block in exit_blocks:
            for expr in block.done_exprs:
                if expr.contain_symbol(ret_register_name):
                    ret_def_exprs.append(expr)
                    # print("exit bloks has %s" % (expr))

        return ret_def_exprs

    def _get_argument_defined(self, function):
        argument_def_exprs = []
        default_arguments = self._binary_parser.argument_vars
        for expr in function.start_node.done_exprs:
            if expr.expr.trace_dir != 'B' or expr.expr.data_type == 'Arg':
                continue

            if any([v for v in expr.expr.trace_vars if v in default_arguments]):
                argument_def_exprs.append(expr)

        return argument_def_exprs

    def _get_definiiton_contain_ret_pointer(self, function):
        ret_def_exprs = []
        ret_register_name = 'r%d' % (self._binary_parser.ret_offset)
        exit_blocks = function.cfg.exit_blocks
        for block in exit_blocks:
            for expr in block.done_exprs:
                if expr.expr.trace_dir == 'F' and expr.contain_symbol(ret_register_name):
                    ret_def_exprs.append(expr)

        return ret_def_exprs

    def _get_definition_contain_argument(self, function):

        argument_def_exprs = []
        default_arguments = self._binary_parser.argument_vars

        for expr in function.start_node.done_exprs:
            if expr.expr.trace_dir != 'B' or expr.expr.data_type == 'Arg':
                continue

            if is_argument(expr.expr.ast):
                argument_def_exprs.append(expr)

        #TODO
        # Add callsite update new definitions.

        return argument_def_exprs

    def _get_redefined_exprs(self, exprs):
        tmp_exprs = []
        redefined_exprs = []
        for expr in exprs:
            for tmp_expr in tmp_exprs:
                if expr.is_ast_equal(tmp_expr):
                    redefined_exprs.append((expr, tmp_expr))
            tmp_exprs.append(expr)

        return redefined_exprs

    def _remove_repeat_exprs(self, sim_structure_exprs, trace_exprs):

        check_ids = {}

        for sim_expr in sim_structure_exprs:

            ast_id = sim_expr.expr.ast.__hash__()

            if ast_id not in check_ids:
                check_ids[ast_id] = []

            check_ids[ast_id].append(sim_expr)

        for ast_id, same_exprs in check_ids.items():

            if len(same_exprs) >= 2:
                new_trace_expr = same_exprs[0]
                new_alias_id = 0

                for same_expr in same_exprs:
                    alias_id = same_expr.expr.alias_id
                    new_trace_expr.expr.contain_alias.add(alias_id)

                    new_alias_id += alias_id
                    trace_exprs.remove(same_expr)

                new_trace_expr.alias_id = new_alias_id
                trace_exprs.append(new_trace_expr)

    def _merge_exprs(self, trace_exprs):
        """
        merge the similar exprs and reduce the numbers.
        """

        summary_exprs = []
        same_struct_exprs = defaultdict(list)
        contain_alias_ids = defaultdict(set)
        similar_struct_exprs = defaultdict(list)

        for trace_expr in trace_exprs:
            # print("\nmerge: %s" % (trace_expr))

            ast = trace_expr.expr.ast
            struct_id = calculate_ast_struct_id(ast)

            # leaf_id = calculate_ast_leaf_id(ast)

            # print("struct id: %s" % (struct_id))
            # print("leaf id: %s" % (leaf_id))

            alias_id = trace_expr.expr.alias_id

            same_struct_exprs[struct_id].append(trace_expr)
            contain_alias_ids[struct_id].add(alias_id)

            # similar_struct_exprs[struct_id].append(trace_expr)

        # DEBUG
        # for leaf_id in same_struct_exprs.keys():
        #     print("same leaf id: %s" % (leaf_id))

        # for struct_id in similar_struct_exprs.keys():
        #     print("same struct id: %s" % (struct_id))

        # for leaf_id, sim_structure_exprs in same_struct_exprs.items():
        #     print("\nkai leaf id: %s %d" % (leaf_id, len(sim_structure_exprs)))

        #     for e in sim_structure_exprs:
        #         print(e)

        # for struct_id, sim_structure_exprs in similar_struct_exprs.items():
        #     print("\nkai struct id: %s %d" % (struct_id, len(sim_structure_exprs)))

        #     for e in sim_structure_exprs:
        #         print(e)

        repeat_exprs_ids = []
        summary_info = {}

        for leaf_id, sim_structure_exprs in same_struct_exprs.items():

            struct_contain_ids = contain_alias_ids[leaf_id]
            # print("same: %s\n contain: %s" % (leaf_id, struct_contain_ids))

            summary_asts = self._summary_similar_structure(sim_structure_exprs)
            # print("getnewast: %s" % (summary_asts))

            if len(summary_asts):
                repeat_exprs_ids.append(leaf_id)
                summary_info[leaf_id] = summary_asts

        # print("could remove: %s" % (repeat_exprs_ids))

        for remove_id in repeat_exprs_ids:
            remove_exprs = same_struct_exprs[remove_id]

            for r_expr in remove_exprs:
                trace_exprs.remove(r_expr)

        for leaf_id, summary_asts in summary_info.items():

            struct_contain_ids = contain_alias_ids[leaf_id]
            new_trace_exprs = self._create_summary_expr(summary_asts, struct_contain_ids)

            for new_expr in new_trace_exprs:
                trace_exprs.append(new_expr)

        for leaf_id, sim_structure_exprs in same_struct_exprs.items():

            if leaf_id in repeat_exprs_ids:
                continue

            self._remove_repeat_exprs(sim_structure_exprs, trace_exprs)

    def _summary_exprs(self, trace_exprs):
        """
        In loop, the exprs maybe similar. summary the similar exprs and reduce the numbers.
        """

        summary_exprs = []
        same_id_exprs = defaultdict(list)

        for trace_expr in trace_exprs:
            # print("summary: %s" % (trace_expr))

            source = trace_expr.expr.source
            alias_id = trace_expr.expr.alias_id
            # print("source: %s, id: %s" % (source, alias_id))

            same_id_exprs[alias_id].append(trace_expr)

        for alias_id, sim_exprs in same_id_exprs.items():
            same_exprs = {}
            repeat_exprs_ids = []
            all_summary_asts = []

            if len(sim_exprs) >= 2:
                for sim_expr in sim_exprs:

                    ast = sim_expr.expr.ast
                    leaf_id = calculate_ast_leaf_id(ast)
                    # print("leaf id: %s" % (leaf_id))

                    if leaf_id not in same_exprs:
                        same_exprs[leaf_id] = []

                    same_exprs[leaf_id].append(sim_expr)

            for leaf_id, sim_structure_exprs in same_exprs.items():

                # print("same: %s" % (leaf_id))
                summary_asts = self._summary_similar_structure(sim_structure_exprs)
                # print("getnewast: %s" % (summary_asts))

                if len(summary_asts):
                    repeat_exprs_ids.append(leaf_id)
                    all_summary_asts.extend(summary_asts)

            # print("could remove: %s" % (repeat_exprs_ids))

            for remove_id in repeat_exprs_ids:
                remove_exprs = same_exprs[remove_id]

                for r_expr in remove_exprs:
                    trace_exprs.remove(r_expr)

            if len(all_summary_asts):
                original_expr = sim_exprs[0]

                new_exprs = self._create_summary_expr(original_expr, all_summary_asts)

                for new_expr in new_exprs:
                    trace_exprs.append(new_expr)

    def _summary_similar_structure(self, sim_structure_exprs):

        arch_bits = self._binary_parser.arch_bits
        simplify_ops = ['__add__', '__sub__']
        summary_asts = []

        with_same_base = {}
        hash_to_ast = {}
        for index, expr in enumerate(sim_structure_exprs):

            # ast_len = get_ast_len(ast)
            # print("%d %s\n with len: %d\n" % (index, ast, ast_len))
            # continue

            ast = expr.expr.ast

            simplify_asts = []
            get_simplify_ast(ast, simplify_asts)
            # print("ast: %s" % (ast))
            # print("could simplify: %s" % (simplify_asts))

            base_hash = 0
            bases_and_incs = []
            for sim_ast in simplify_asts:
                inc_info = get_inc_data_info(sim_ast)
                # print("inc info: %s" % (inc_info))

                base_asts = inc_info['base']
                mul_inc = inc_info['mul_inc']
                inc_num = inc_info['inc_num']

                inc_flag = False
                if len(mul_inc) > 0:
                    # print("with inc :%s" % (mul_inc))
                    inc_flag = True

                if len(inc_num):
                    # print("with inc: %s" % (inc_num))

                    maybe_incs = []
                    for inc, num in inc_num.items():
                        if num >= 3:
                            maybe_incs.append(inc)
                            inc_flag = True

                    for inc in maybe_incs:
                        mul_inc.add(inc)
                        inc_num.pop(inc)

                if len(base_asts) == 0:
                    sym_bases = []
                    for inc_sym, num in inc_num.items():
                        if type(inc_sym) is str and num == 1:
                            sym_bases.append(inc_sym)

                        elif type(inc_sym) is int and num == 1:
                            con_type = get_mem_permission(inc_sym)
                            if con_type in ['ro','rw', 'bss']:
                                sym_bases.append(inc_sym)

                    for sym_b in sym_bases:
                        if type(sym_b) is str:
                            sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                        elif type(sym_b) is int:
                            sym_ast = claripy.BVV(sym_b, arch_bits)

                        base_asts.append(sym_ast)
                        inc_num.pop(sym_b)

                if inc_flag:
                    for base_ast in base_asts:
                        base_hash += base_ast.__hash__()

                    info = [sim_ast, base_asts, mul_inc, inc_num]
                    bases_and_incs.append(info)

            if len(bases_and_incs):
                if base_hash in with_same_base:
                    old_bases_and_incs = with_same_base[base_hash]

                    if len(bases_and_incs) > len(old_bases_and_incs):
                        with_same_base[base_hash] = bases_and_incs
                        hash_to_ast[base_hash] = ast

                else:
                    with_same_base[base_hash] = bases_and_incs
                    hash_to_ast[base_hash] = ast

        all_syms = []
        remove_hash = []
        for b_hash, bases_and_incs in with_same_base.items():
            # print("\n%s containt %s" % (b_hash, bases_and_incs))
            # print("ast %s" % (hash_to_ast[b_hash]))

            inc_syms = set()
            for info in bases_and_incs:
                mul_inc, inc_num = info[2], info[3]
                for inc_sym in mul_inc:
                    inc_syms.add(inc_sym)

                for inc_sym in inc_num.keys():
                    inc_syms.add(inc_sym)

            inc_syms = tuple(inc_syms)
            if inc_syms not in all_syms:
                all_syms.append(inc_syms)

            else:
                remove_hash.append(b_hash)

        for r_hash in remove_hash:
            with_same_base.pop(r_hash)

        # print("test: %s\n" % (with_same_base))

        for b_hash, bases_and_incs in with_same_base.items():
            original_ast = hash_to_ast[b_hash]

            new_ast = self._generate_summary_ast(original_ast, bases_and_incs)
            summary_asts.append(new_ast)


        return summary_asts

    def _generate_summary_ast(self, original_ast, simplify_ast_infos):

        new_ast = original_ast

        for simplify_ast_info in simplify_ast_infos:

            summary_ast = self._get_the_summary_ast(original_ast, simplify_ast_info)

            sim_ast = simplify_ast_info[0]

            new_ast = new_ast.replace(sim_ast, summary_ast)

        return new_ast

    def _get_the_summary_ast(self, original_ast, simplify_ast_info):

        # print("old ast: %s" % (original_ast))

        arch_bits = self._binary_parser.arch_bits

        sim_bases = simplify_ast_info[1]

        summary_ast = 0
        for base in sim_bases:

            all_bash_hash, bases_and_incs = self._get_ast_base_and_inc_info(base)

            # print("Get hash: %s\ninfo: %s" % (all_bash_hash, bases_and_incs))

            if len(bases_and_incs) == 0:

                summary_ast += base

            else:
                new_base = base
                for sim_ast_info in bases_and_incs:
                    base_summ_ast = self._get_the_summary_ast(base, sim_ast_info)

                    base_sim_ast = sim_ast_info[0]
                    new_base = new_base.replace(base_sim_ast, base_summ_ast)

                summary_ast += new_base

        mul_inc, inc_num = simplify_ast_info[2], simplify_ast_info[3]

        if len(mul_inc):
            i = claripy.BVS('i', arch_bits, explicit_name=True)

            for inc_o in mul_inc:
                if type(inc_o) is int:
                    inc_ast = claripy.BVV(inc_o, arch_bits)

                elif type(inc_o) is str:
                    inc_ast = claripy.BVS(inc_o, arch_bits, explicit_name=True)

                else:
                    continue

                summary_ast += i * inc_ast

        for inc_o, num in inc_num.items():
            if type(inc_o) is int:
                inc_ast = claripy.BVV(inc_o, arch_bits)

            elif type(inc_o) is str:
                inc_ast = claripy.BVS(inc_o, arch_bits, explicit_name=True)

            else:
                continue

            summary_ast += inc_ast * num

        # print("summary ast: %s" % (summary_ast))
        return summary_ast

    def _get_ast_base_and_inc_info(self, ast):

        simplify_asts = []
        arch_bits = self._binary_parser.arch_bits
        get_simplify_ast(ast, simplify_asts)

        base_hash = 0
        bases_and_incs = []
        for sim_ast in simplify_asts:
            inc_info = get_inc_data_info(sim_ast)

            base_asts = inc_info['base']
            mul_inc = inc_info['mul_inc']
            inc_num = inc_info['inc_num']

            inc_flag = False
            if len(mul_inc) > 0:
                inc_flag = True

            if len(inc_num):
                maybe_incs = []
                for inc, num in inc_num.items():
                    if num >= 3:
                        maybe_incs.append(inc)
                        inc_flag = True

                for inc in maybe_incs:
                    mul_inc.add(inc)
                    inc_num.pop(inc)

            if len(base_asts) == 0:
                sym_bases = []
                for inc_sym, num in inc_num.items():
                    if type(inc_sym) is str and num == 1:
                        sym_bases.append(inc_sym)

                    elif type(inc_sym) is int and num == 1:
                        con_type = get_mem_permission(inc_sym)
                        if con_type in ['ro', 'rw', 'bss']:
                            sym_bases.append(inc_sym)

                for sym_b in sym_bases:
                    if type(sym_b) is str:
                        sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                    elif type(sym_b) is int:
                        sym_ast = claripy.BVV(sym_b, arch_bits)

                    base_asts.append(sym_ast)
                    inc_num.pop(sym_b)

            if inc_flag:
                for base_ast in base_asts:
                    base_hash += base_ast.__hash__()

                info = [sim_ast, base_asts, mul_inc, inc_num]
                bases_and_incs.append(info)

        return base_hash, bases_and_incs

    def _create_summary_expr(self, summary_asts, struct_contain_ids):

        new_trace_exprs = []
        for summary_ast in summary_asts:

            new_expr = VarExpr(summary_ast, pattern='OB', trace_dir='B', data_type='Iptr')
            new_expr.get_trace_variable()
            new_expr.initial_sims()

            alias_id = 0
            for a_id in struct_contain_ids:
                new_expr.contain_alias.add(a_id)
                alias_id += a_id

            new_expr.alias_id = alias_id

            new_trace_expr = TraceExpr(new_expr)

            new_trace_exprs.append(new_trace_expr)

        return new_trace_exprs

    def _reduce_same_exprs(self, same_exprs):

        simplify_ops = ['__add__', '__sub__']
        summary_exprs = []

        for leaf_id, same_asts in same_exprs.items():
            # print("same: %s" % (leaf_id))

            with_same_base = {}
            hash_to_ast = {}
            for ast in same_asts:

                # simplify_asts = get_simplify_ast(ast)
                simplify_asts = []
                get_simplify_ast(ast, simplify_asts)
                # print("ast: %s" % (ast))
                # print("could simplify: %s" % (simplify_asts))

                base_hash = 0
                bases_and_incs = {}
                for sim_ast in simplify_asts:
                    inc_info = get_inc_data_info(sim_ast)
                    # print("inc info: %s" % (inc_info))

                    base_asts = inc_info['base']
                    mul_inc = inc_info['mul_inc']
                    inc_num = inc_info['inc_num']

                    inc_flag = False
                    if len(mul_inc) > 0:
                        # print("with inc :%s" % (mul_inc))
                        inc_flag = True

                    if len(inc_num):
                        # print("with inc: %s" % (inc_num))

                        maybe_incs = []
                        for inc, num in inc_num.items():
                            if num >= 3:
                                maybe_incs.append(inc)
                                inc_flag = True

                        for inc in maybe_incs:
                            mul_inc.add(inc)
                            inc_num.pop(inc)

                    if len(base_asts) == 0:
                        sym_bases = []
                        for inc_sym, num in inc_num.items():
                            if type(inc_sym) is str and num == 1:
                                sym_bases.append(inc_sym)

                            elif type(inc_sym) is int and num == 1:
                                con_type = get_mem_permission(inc_sym)
                                if con_type in ['ro', 'rw', 'bss']:
                                    sym_bases.append(inc_sym)

                        for sym_b in sym_bases:
                            if type(sym_b) is str:
                                sym_ast = claripy.BVS(sym_b, arch_bits, explicit_name=True)

                            elif type(sym_b) is int:
                                sym_ast = claripy.BVV(sym_b, arch_bits)

                            base_asts.append(sym_ast)
                            inc_num.pop(sym_b)

                    if inc_flag:
                        for base_ast in base_asts:
                            base_hash += base_ast.__hash__()

                        info = [sim_ast, base_asts, mul_inc, inc_num]
                        sim_ast_hash = sim_ast.__hash__()
                        bases_and_incs[sim_ast_hash] = info

                if len(bases_and_incs):
                    if base_hash in with_same_base:
                        old_bases_and_incs = with_same_base[base_hash]

                        if len(bases_and_incs) > len(old_bases_and_incs):
                            with_same_base[base_hash] = bases_and_incs
                            hash_to_ast[base_hash] = ast

                    else:
                        with_same_base[base_hash] = bases_and_incs
                        hash_to_ast[base_hash] = ast

                    # simplifiy_ast_with_base.append([sim_ast, base_asts])

                # TODO
                # if len(simplify_asts) >= 2:
                #     self._find_embedded_base(simplify_asts)

            # for b_hash, info in with_same_base.items():
            #     print("\n%s containt %s" % (b_hash, info))
            #     print("ast %s" % (hash_to_ast[b_hash]))


    def _summary_same_base(self, same_bases, hash_to_ast):

        arch_bits = self._binary_parser.arch_bits

        for b_hash, ast_infos in same_bases.items():
            original_ast = hash_to_ast[b_hash]

            if len(ast_infos) >= 2:
                print("There are two or more ast could be simplified!")

            base_with_hash = {}
            sim_ast_hash = ast_infos.keys()
            # print("Contain hash: %s" % (sim_ast_hash))

            for ast_info in ast_infos.values():
                bases = ast_info[1]

                for base in bases:
                    b_hash = base.__hash__()
                    base_with_hash[b_hash] = base

            for ast_info in ast_infos.values():
                simplify_ast = ast_info[0]
                bases = ast_info[1]
                mul_inc = ast_info[2]
                inc_num = ast_info[3]

                # print("simplify_ast: %s" % (simplify_ast))
                # print("bases: %s, mul_inc: %s, inc_num: %s" % (bases, mul_inc, inc_num))

                self._get_the_summary_ast(bases, base_with_hash, ast_infos)

            # simplify_ast = bases + i*mul_inc + inc_num


    def _find_embedded_base(self, simplify_asts):

        pass
        # print("\n")
        # for sim_ast in simplify_asts:
        #     print("sim: %s" % (sim_ast))

    def _get_file_open_taint_sources(self, function):
        """
        Get the source fread/read/fgets's stream.
        """
        fake_sources = set()
        true_sources = set()
        udata_info = self.collector.datas['uData']
        funcea = function.addr
        udata_exprs = udata_info.get(funcea)
        if udata_exprs is None:
            return fake_sources

        for udata_expr in udata_exprs:
            taint_src = udata_expr.expr.taint_source
            cons_type = udata_expr.expr.cons_type
            ast = udata_expr.expr.ast
            if udata_expr.expr.flag & 0x4000 and taint_src:
                # print("udata-expr: %s %x %d" % (udata_expr, udata_expr.expr.flag, udata_expr.expr.cons_type))
                if cons_type == 0x11:
                    true_sources.add(taint_src)
                    # print("Found socket source: %x" % (taint_src))
                elif (cons_type == 0x8 or 'open' in str(ast)):
                    # print("Found open-file source: %x" % (taint_src))
                    fake_sources.add(taint_src)

        for t_source in true_sources:
            if t_source in fake_sources:
                fake_sources.remove(t_source)
        return fake_sources

    def _check_taint_source(self, function, def_exprs):
        remove_exprs = []
        fake_sources = self._get_file_open_taint_sources(function)
        # for fake_src in fake_sources:
        #     print("In-func-%x has %x" % (function.addr, fake_src))
        for define_expr in def_exprs:
            taint_source = define_expr.expr.taint_source
            # print("Define-expr: %s" % (define_expr))
            # if taint_source:
            #     print(" -->taint-source: %x" % (taint_source))
            # else:
            #     print(" --> None")
            if taint_source in fake_sources:
                remove_exprs.append(define_expr)

        for r_expr in remove_exprs:
            def_exprs.remove(r_expr)

    def _push_callee_exprs_to_callsite(self, function):

        self._push_callee_arg_exprs_to_callsite(function)

        self._push_callee_ret_exprs_to_callsite(function)

    # Kai psu add!
    def _push_callee_arg_exprs_to_callsite(self, function):
        """
        Push all trace exprs that contain arguments to corresponding callsites.
        In this model, each updated expr in callsite will trace in caller.
        """
        funcea = function.addr

        # First, push the def exprs!
        argument_def_exprs = self._get_push_arg_def_exprs(function)
        function.set_definition_contexts(argument_def_exprs)

        # Second, push the use exprs!
        argument_use_exprs = self._get_push_use_exprs(function)

        argument_cons_exprs = self._get_push_cons_exprs(function)

        self._check_taint_source(function, argument_def_exprs)

        pre_functions = self._ida_object.cg.graph.predecessors(function)
        for pre_function in pre_functions:
            # print("Push-expr to: %s" % (pre_function))
            self._pre_process_function(pre_function)

            if pre_function.cfg is None:
                continue

            caller_sites = pre_function.cfg.callees.get(funcea)

            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for callsite in caller_sites:
                # print("Csite: %s %s %s" % (function, pre_function, callsite))

                self._make_def_copy_to_callsite(callsite, argument_def_exprs, argument_cons_exprs)

                self._make_use_copy_to_callsite(callsite, argument_use_exprs)

    # Kai psu add!
    def _push_callee_ret_exprs_to_callsite(self, function):
        """
        Push all trace exprs that contain arguments to corresponding callsites.
        In this model, each updated expr in callsite will trace in caller.
        """
        funcea = function.addr

        ret_def_exprs = self._get_push_ret_def_exprs(function)
        # print("ppp->%s" % (ret_def_exprs))

        self._check_taint_source(function, ret_def_exprs)

        pre_functions = self._ida_object.cg.graph.predecessors(function)
        for pre_function in pre_functions:
            self._pre_process_function(pre_function)

            if pre_function.cfg is None:
                continue

            caller_sites = pre_function.cfg.callees.get(funcea)

            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for callsite in caller_sites:
                self._make_ret_def_copy_to_callsite(callsite, ret_def_exprs)

    # Kai psu add!
    def _get_push_use_exprs(self, function):
        """
        Process the use exprs in function and get the argument use exprs which
        should be pushed to callsites or caller.
        """
        use_exprs = []
        funcea = function.addr
        icall_exprs = self.collector.datas['Iptr'].get(funcea)
        if icall_exprs:
            for icall_expr in icall_exprs:
                if not icall_expr.only_contain_global() and icall_expr not in use_exprs:
                    use_exprs.append(icall_expr)

        use_datas = self.collector.datas['uData'].get(funcea)
        if use_datas:
            for use_expr in use_datas:
                if use_expr.contain_special_symbol('_'):
                    continue
                elif use_expr.expr.flag & 0x4000 and use_expr.expr.only_argument():
                    use_exprs.append(use_expr)
                    # print("taint-source-file: %s" % (use_expr))

        if len(use_exprs):
            argument_use_exprs = self._get_argument_use_exprs(function, use_exprs)
        else:
            return []

        new_use_exprs = dedup_exprs_v1(argument_use_exprs)

        return new_use_exprs

    def _get_push_cons_exprs(self, function):
        """
        For the memcpy/strncpy, we trace the length argument in backward.
        """
        cons_exprs = {}
        fiter_syms = ['o', '_']
        funcea = function.addr
        cexprs = self.collector.datas['Cons'].get(funcea)

        if not cexprs:
            return cons_exprs

        for cons_expr in cexprs:
            ast = cons_expr.expr.ast
            if cons_expr.contain_special_symbols(fiter_syms):
                continue
            alias_id = cons_expr.expr.alias_id
            if alias_id not in cons_exprs:
                cons_exprs[alias_id] = []
            cons_exprs[alias_id].append(cons_expr)

        return cons_exprs

    # Kai psu add!
    def _get_push_arg_def_exprs(self, function):
        """
        Process the def exprs in function and get the argument definition exprs which
        should be pushed to callsites or caller.
        """
        def_exprs = []
        funcea = function.addr

        # print("Push-arg-def-in: %s" % (function))
        for data_type in ['Vptr', 'sDef', 'Tdata']:
            collect_exprs = self.collector.datas[data_type].get(funcea)
            if not collect_exprs:
                continue

            for trace_expr in collect_exprs:
                if trace_expr.contain_special_symbol('_'):
                    continue
                if not trace_expr.expr.is_ret and trace_expr not in def_exprs:
                    def_exprs.append(trace_expr)
                    # print("psu-test: push %s_exprs: %s" % (data_type, trace_expr))

        argument_def_exprs = self._get_argument_def_exprs(function, def_exprs)

        # print("psu-test: should push def-exprs: %s" % (argument_def_exprs))
        # if len(argument_def_exprs):
        #     self._remove_killed_definition(function, argument_def_exprs)
        #     self._judge_definition_occur(function, argument_def_exprs)

        return argument_def_exprs

    # Kai psu add!
    def _get_push_ret_def_exprs(self, function):
        """
        Process the def exprs in function and get the ret-pointer definition exprs which
        should be pushed to callsites or caller.
        """
        def_exprs = []
        funcea = function.addr

        for data_type in ['Vptr', 'Fptr', 'sDef', 'Tdata']:
            collect_exprs = self.collector.datas[data_type].get(funcea)
            if not collect_exprs:
                continue

            for trace_expr in collect_exprs:
                if trace_expr.expr.is_ret and trace_expr not in def_exprs:
                    def_exprs.append(trace_expr)
                    # print("psu-test: push %s_ret_exprs: %s" % (data_type, trace_expr))

        new_ret_def_exprs = merge_simlilar_exprs_v2(def_exprs)

        return new_ret_def_exprs

    # Kai psu add!
    def _remove_killed_definition(self, function, def_exprs):
        """
        Remove the definition that is redefined in one path. So the killed definition should't be push to callsite.
        """
        tmp_exprs = []
        redefined_exprs = []
        func_cfg = function.cfg
        graph_parser = function.graph_parser

        for expr in def_exprs:
            for tmp_expr in tmp_exprs:
                if expr.is_ast_equal(tmp_expr):
                    redefined_exprs.append((expr, tmp_expr))
            tmp_exprs.append(expr)

        for expr1, expr2 in redefined_exprs:
            n1 = func_cfg.get_node_by_addr(expr1.expr.source.block_addr)
            n2 = func_cfg.get_node_by_addr(expr2.expr.source.block_addr)
            killed = graph_parser.judge_post_dome(n1, n2)
            if killed:
                # define in node n1 is redefined in node n2
                # print("%s: %s is redefined by %s: %s" % (n1, expr1, n2, expr2))
                try:
                    def_exprs.remove(expr1)
                except ValueError:
                    l.info("expr %s has been remove" % (expr1))

            else:
                killed = graph_parser.judge_post_dome(n2, n1)
                if killed:
                    # define in node n2 is redefined in node n1
                    # print("%s: %s is redefined by %s: %s" % (n2, expr2, n1, expr1))
                    try:
                        def_exprs.remove(expr2)
                    except ValueError:
                        l.info("expr %s has been remove" % (expr2))

    # Kai psu add!
    def _judge_definition_occur(self, function, def_exprs):
        """
        Use the pdom tree to judge the defintion must occur or may occur in a function.
        """
        must_nodes = set()
        may_nodes = set()
        func_cfg = function.cfg
        graph_parser = function.graph_parser
        start_node = function.start_node
        for expr in def_exprs:
            source_loc = expr.expr.source
            # print("DEBUG function %s, source_loc %s" % (function, source_loc))
            source_node = func_cfg.get_node_by_addr(source_loc.block_addr)
            l.debug("definiton node %s" % (source_node))
            if source_node in must_nodes:
                expr.expr.occur = 'must'

            elif source_node in may_nodes:
                expr.expr.occur = 'may'

            else:
                is_pdom = graph_parser.judge_post_dome(start_node, source_node)
                if is_pdom:
                    must_nodes.add(source_node)
                    expr.expr.occur = 'must'

                else:
                    may_nodes.add(source_node)
                    expr.expr.occur = 'may'

        l.debug("node %s def must occur" % (must_nodes))
        l.debug("node %s def may occur" % (may_nodes))

    def _push_function_trace_exprs_to_callsite(self, function):
        """
        Push a function's all trace exprs which containt argument to callsites.
        """
        if push_use_level == 0:
            self._push_function_use_expr_to_callsite(function)

            # self._push_funciton_def_expr_to_callsite(function)

        else:
            self._push_function_expr_to_caller(function)

    def _push_function_use_expr_to_callsite(self, function):

        use_exprs = []

        funcea = function.addr
        use_icalls = collect_icall_exprs[funcea]
        if use_icalls:
            use_exprs.extend(use_icalls)

        use_datas = self.collector.datas['uData'].get(funcea)
        # print("use_datas: %s" % (use_datas))
        if use_datas:
            use_exprs.extend(use_datas)

        if len(use_exprs):
            argument_use_exprs = self._get_argument_use_exprs(function, use_exprs)
        else:
            return

        callsites = self._get_all_callsites_to_function(function)

        for callsite in callsites:
            self._push_use_to_callsite(callsite, argument_use_exprs)

    def _push_function_expr_to_caller(self, function):

        funcea = function.addr
        use_exprs = collect_icall_exprs[funcea]

        if len(use_exprs):
            argument_use_exprs = self._get_argument_use_exprs(function, use_exprs)

        else:
            argument_use_exprs = []

        def_exprs = collect_ptr_exprs[funcea]
        # print("def exprs: %s" % (def_exprs))

        if len(def_exprs) and push_def_level:
            argument_def_exprs = self._get_argument_def_exprs(function, def_exprs)

        else:
            argument_def_exprs = []

        if len(argument_use_exprs) == 0 and len(argument_def_exprs) == 0:
            return

        funcea = function.addr
        pre_functions = self._ida_object.cg.graph.predecessors(function)

        for pre_function in pre_functions:
            self._pre_process_function(pre_function)
            caller_sites = pre_function.cfg.callees.get(funcea)

            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for callsite in caller_sites:

                self._push_use_to_caller(pre_function, callsite, argument_use_exprs)

                self._push_def_to_caller(pre_function, callsite, argument_def_exprs)

    def _push_funciton_def_expr_to_callsite(self, function):
        """
        For all definition in a function, check wether a def would be killed by others,
        or the def is must or may occur, then push the def to all callsites.
        """
        funcea = function.addr
        start_node = function.start_node
        func_cfg = function.cfg

        def_exprs = collect_ptr_exprs.get(funcea)
        if def_exprs is None or len(def_exprs) == 0:
            return

        argument_def_exprs = self._get_argument_def_exprs(function, def_exprs)

        # ret_def_exprs = self._get_ret_pointer_defined(function)

        arg_redefined_exprs = self._get_redefined_exprs(argument_def_exprs)
        # ret_redefined_exprs = self._get_redefined_exprs(ret_def_exprs)

        # time_start = time.time()
        graph_parser = GraphMethod(func_cfg, start_node)
        # print("Parse graph cost time: %lf" % (time.time() - time_start))

        if len(arg_redefined_exprs):
            self._kill_redefined_in_function(function, argument_def_exprs, arg_redefined_exprs, graph_parser)

        # if len(ret_redefined_exprs):
        #     self._kill_redefined_in_function(function, ret_def_exprs, ret_redefined_exprs, graph_parser)

        self._push_argument_define_to_callsite(function, argument_def_exprs, graph_parser)
        # self._push_ret_pointer_define_to_retsite(function, ret_def_exprs, graph_parser, callsite=callsite)

        # self._push_argument_define_to_all_callers(function, argument_def_exprs, graph_parser)
        # self._push_ret_pointer_define_to_all_callers(function, ret_def_exprs, graph_parser)

        # DEBUG
        self._test_context_infect(function, argument_def_exprs, "argument definition")
        # self._test_context_infect(function, ret_def_exprs, "return ptr definition")

    def _get_all_callsites_to_function(self, function):
        """
        Get all callsite which call the given function.
        """
        callsites = []
        funcea = function.addr
        pre_functions = self._ida_object.cg.graph.predecessors(function)

        for pre_function in pre_functions:
            self._pre_process_function(pre_function)
            caller_sites = pre_function.cfg.callees.get(funcea)
            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for cs in caller_sites:
                callsites.append(cs)

        return callsites

    def _push_argument_define_to_all_callers(self, function, argument_defines, graph_parser):
        """
        :param argument_defines: a list, each element is a argument definition.
        """
        func_cfg = function.cfg
        start_node = function.start_node
        must_nodes = set()
        may_nodes = set()
        for expr in argument_defines:
            source_loc = expr.expr.source
            # print("DEBUG function %s, source_loc %s" % (function, source_loc))
            source_node = func_cfg.get_node_by_addr(source_loc.block_addr)
            l.debug("definiton node %s" % (source_node))
            if source_node in must_nodes:
                expr.expr.occur = 'must'

            elif source_node in may_nodes:
                expr.expr.occur = 'may'

            else:
                is_pdom = graph_parser.judge_post_dome(start_node, source_node)
                if is_pdom:
                    must_nodes.add(source_node)
                    expr.expr.occur = 'must'

                else:
                    may_nodes.add(source_node)
                    expr.expr.occur = 'may'

        l.debug("node %s def must occur" % (must_nodes))
        l.debug("node %s def may occur" % (may_nodes))

        callsites = []
        funcea = function.addr
        pre_functions = self._ida_object.cg.graph.predecessors(function)

        # self._merge_exprs(argument_defines)

        for pre_function in pre_functions:
            self._pre_process_function(pre_function)
            caller_sites = pre_function.cfg.callees.get(funcea)
            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for cs in caller_sites:

                # DEBUG
                # if cs.addr not in [0x793f9e]:
                #     continue

                new_argument_definitions = self._make_new_exprs(cs, argument_defines)
                pre_function.callsite_arg_definitions[cs] = new_argument_definitions

                arg_ptr_alias = cs.arg_ptr_alias
                for definition in new_argument_definitions:
                    value = definition.expr.value
                    data_type = definition.expr.data_type

                    if value is not None and data_type == 'Aptr' and value.op in ['BVS', 'BVV']:
                        alias_name = trace_expr.expr.value.args[0]
                        if alias_name not in arg_ptr_alias:
                            arg_ptr_alias[alias_name] = []

                        arg_ptr_alias[alias_name].append(definition)

    def _push_ret_pointer_define_to_all_callers(self, function, ret_pointer_defines, graph_parser):
        """
        :param function:
        :param ret_def_exprs: a list, each element is a ret pointer definition.
        :param graph_parser:
        """
        func_cfg = function.cfg
        start_node = function.start_node
        must_nodes = set()
        may_nodes = set()
        for expr in ret_pointer_defines:
            source_loc = expr.expr.source
            source_node = func_cfg.get_node_by_addr(source_loc.block_addr)
            l.debug("definiton node %s" % (source_node))
            if source_node in must_nodes:
                expr.expr.occur = 'must'
            elif source_node in may_nodes:
                expr.expr.occur = 'may'
            else:
                is_pdom = graph_parser.judge_post_dome(start_node, source_node)
                if is_pdom:
                    must_nodes.add(source_node)
                    expr.expr.occur = 'must'
                else:
                    may_nodes.add(source_node)
                    expr.expr.occur = 'may'
        l.debug("node %s def must occur" % (must_nodes))
        l.debug("node %s def may occur" % (may_nodes))

        callsites = []
        funcea = function.addr
        pre_functions = self._ida_object.cg.graph.predecessors(function)

        for pre_function in pre_functions:
            self._pre_process_function(pre_function)
            caller_sites = pre_function.cfg.callees.get(funcea)
            if caller_sites is None:
                l.info("The function %s didn't call function %s, check it future!" % (pre_function, function))
                continue

            for cs in caller_sites:
                new_ret_pointer_definitions = self._make_new_exprs(cs, ret_pointer_defines)
                pre_function.callsite_ret_definitions[cs] = new_ret_pointer_definitions

    def _push_argument_define_to_callsite(self, function, argument_defines, graph_parser, callsite=None):
        """
        :param argument_defines: a list, each element is a argument definition.
        """
        func_cfg = function.cfg
        start_node = function.start_node
        must_nodes = set()
        may_nodes = set()
        for expr in argument_defines:
            source_loc = expr.expr.source
            # print("DEBUG function %s, source_loc %s" % (function, source_loc))
            source_node = func_cfg.get_node_by_addr(source_loc.block_addr)
            l.debug("definiton node %s" % (source_node))
            if source_node in must_nodes:
                expr.expr.occur = 'must'

            elif source_node in may_nodes:
                expr.expr.occur = 'may'

            else:
                is_pdom = graph_parser.judge_post_dome(start_node, source_node)
                if is_pdom:
                    must_nodes.add(source_node)
                    expr.expr.occur = 'must'

                else:
                    may_nodes.add(source_node)
                    expr.expr.occur = 'may'

        l.debug("node %s def must occur" % (must_nodes))
        l.debug("node %s def may occur" % (may_nodes))

        # self._merge_exprs(argument_defines)

        if callsite is None:
            callsites = self._get_all_callsites_to_function(function)

        else:
            callsites = [callsite]

        for cs in callsites:
            self._make_copy_to_callsite(cs, argument_defines)
            # print("push expr to callsite %s\n expr: %s" % (cs, argument_defines))

    def _push_ret_pointer_define_to_retsite(self, function, ret_pointer_defines, graph_parser, callsite=None):
        """
        :param function:
        :param ret_def_exprs: a list, each element is a ret pointer definition.
        :param graph_parser:
        """
        func_cfg = function.cfg
        start_node = function.start_node
        must_nodes = set()
        may_nodes = set()
        for expr in ret_pointer_defines:
            source_loc = expr.expr.source
            source_node = func_cfg.get_node_by_addr(source_loc.block_addr)
            l.debug("definiton node %s" % (source_node))
            if source_node in must_nodes:
                expr.expr.occur = 'must'
            elif source_node in may_nodes:
                expr.expr.occur = 'may'
            else:
                is_pdom = graph_parser.judge_post_dome(start_node, source_node)
                if is_pdom:
                    must_nodes.add(source_node)
                    expr.expr.occur = 'must'
                else:
                    may_nodes.add(source_node)
                    expr.expr.occur = 'may'
        l.debug("node %s def must occur" % (must_nodes))
        l.debug("node %s def may occur" % (may_nodes))

        if callsite is None:
            callsites = self._get_all_callsites_to_function(function)

        else:
            callsites = [callsite]

        for cs in callsites:
            self._make_ret_define_copy_to_retsite(cs, ret_pointer_defines)

    def _make_new_exprs(self, block, argument_defines):
        new_exprs = []
        addr = block.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_defines:
            new_expr = expr.deep_copy()
            new_expr.expr.source = code_location
            new_expr.index = stmt_idx
            new_exprs.append(new_expr)

        return new_exprs

    def _make_copy_to_callsite(self, callsite, argument_defines):
        """
        :param callsite: a block node which has a call.
        :param
        """
        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_defines:
            new_expr = expr.deep_copy()
            new_expr.expr.source = code_location
            # new_expr.expr.code_location = code_location
            new_expr.index = stmt_idx
            callsite.callsite_exprs.append(new_expr)

    def _make_def_copy_to_callsite(self, callsite, argument_defines, argument_cons):
        """
        :param callsite: a block node which has a call.
        :param argument_defines: callee's defintions to argument pointer.
        """
        copy_exprs = []
        analyzed_cons_ids = set()
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_defines:
            new_expr = expr.deep_copy()
            new_expr.clear_path()
            new_expr.expr.source = code_location
            new_expr.expr.alias_id += code_location.__hash__()
            new_expr.expr.ptr_id += addr
            new_expr.expr.flag &= 0xFEFF
            new_expr.expr.kill_store_action_in_callsite(code_location)

            should_add_cons_values = {}
            traced_cons_ids = []
            for cons_id in new_expr.cons_ids:
                if cons_id in analyzed_cons_ids:
                    traced_cons_ids.append(cons_id)
                elif cons_id in argument_cons:
                    analyzed_cons_ids.add(cons_id)
                    traced_cons_ids.append(cons_id)
                    cons_exprs = argument_cons[cons_id]
                    # print("cons-exprs: %s" % (argument_cons[cons_id]))
                    self._make_cons_copy_to_callsite(callsite, cons_exprs)
                self._check_expr_cons_ids(cons_id, should_add_cons_values)

            if len(traced_cons_ids):
                call_hash = code_location.__hash__()
                for cons_id in traced_cons_ids:
                    new_expr.cons_ids.remove(cons_id)
                    new_id = cons_id + call_hash
                    new_expr.cons_ids.append(new_id)
                    # print("Got new-cons: %s, remove cons: %s" % (new_id, cons_id))

            for cons_id, cons_values in should_add_cons_values.items():
                # print("Get-concret-cons: %s %s" % (cons_id, cons_values))
                # print("Expr-has-cons-ids: %s" % (new_expr.cons_ids))
                if cons_id in new_expr.cons_ids:
                    new_expr.cons_ids.remove(cons_id)
                for cons_v in cons_values:
                    if cons_v not in new_expr.constraints:
                        new_expr.constraints.append(cons_v)

            # print("push-to-callsite: %s %x" % (new_expr, new_expr.expr.alias_id))
            # print("--with-cons: %s" % (new_expr.expr.cons_ids))

            new_expr.inter_funcs.append('%x' % callsite.func_addr)
            if callsite.node_type == 'iCall':
                new_expr.inter_icall_level = 1

            for pre_block in callsite.predecessors:
                new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                pre_block.backward_exprs.append(new_expr)
                # print("push-to-callsite(B) %s : %s %s %x" % (pre_block, new_expr, new_expr.constraints, new_expr.expr.alias_id))

            if expr.expr.data_type == 'Tdata' and expr.only_contain_global():
                f_expr = new_expr.make_forward_copy()
                f_expr.expr.flag |= 0x100
                f_expr.index = 0
                f_expr.expr.active_store_action_in_callsite(code_location)
                f_expr.expr.kill_load_action_by_loc()

                for succ_block in callsite.successors:
                    succ_block.forward_exprs.append(f_expr)
                    # print("push-to-callsite(F) %s : %s %s %x" % (succ_block, f_expr, f_expr.constraints, f_expr.expr.alias_id))

    def _make_use_copy_to_callsite(self, callsite, argument_uses):
        """
        :param callsite: a block node which has a call.
        :param
        """
        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_uses:
            new_expr = expr.deep_copy()
            new_expr.expr.source = code_location
            new_expr.expr.alias_id += code_location.__hash__()
            # clear the trace path
            new_expr.forward_path = set()
            new_expr.backward_path = set()
            copy_exprs.append(new_expr)

        for pre_block in callsite.predecessors:
            for new_expr in copy_exprs:
                new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                pre_block.backward_exprs.append(new_expr)
                # print("push-uData: %s %s %s %s" % (pre_block, new_expr, new_expr.expr.data_type, new_expr.expr.invariant_loc))
        # if len(argument_uses) > 100:
        #     raise Exception("Too many push use datas %s" % (callsite))

    def _make_cons_copy_to_callsite(self, callsite, argument_cons):
        """
        :param callsite: a block node which has a call.
        :param argument_cons: a list save the constraint expr.
        """
        if len(argument_cons) == 0:
            return

        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_cons:
            new_expr = expr.deep_copy()
            new_expr.expr.alias_id += code_location.__hash__()
            new_expr.expr.ptr_id += addr
            new_expr.expr.source = code_location
            # clear the trace path
            new_expr.forward_path = set()
            new_expr.backward_path = set()
            copy_exprs.append(new_expr)

        for pre_block in callsite.predecessors:
            for new_expr in copy_exprs:
                if new_expr not in pre_block.backward_exprs:
                    new_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
                    pre_block.backward_exprs.append(new_expr)
                    # print("Push-cons: %s %s" % (pre_block, new_expr))

    def _make_ret_def_copy_to_callsite(self, callsite, ret_defines):
        """
        :param callsite: a block node which has a call.
        :param argument_defines: callee's defintions to argument pointer.
        """
        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)

        for ret_expr in ret_defines:
            new_expr = ret_expr.deep_copy()
            new_expr.clear_path()
            new_expr.expr.source = code_location
            new_expr.expr.flag |= 0x100
            new_expr.index = stmt_idx

            new_expr.expr.active_store_action_in_callsite(code_location)
            # TODO
            # new_expr.expr.kill_load_action_in_callsite()

            for succ_block in callsite.successors:
                succ_block.forward_exprs.append(new_expr)
                if new_expr.expr.data_type == 'Tdata':
                    new_expr.inter_funcs.append('%x' % (callsite.func_addr))
                    if callsite.node_type == 'iCall':
                        new_expr.inter_icall_level += 1
                    print("Push-ret-%x %s taint-source:%x %s" % (succ_block.addr, new_expr, new_expr.expr.taint_source, new_expr.inter_funcs))

    def _push_use_to_callsite(self, callsite, argument_exprs):
        """
        :param callsite: a block node which has a call.
        :param
        """
        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)
        for expr in argument_exprs:
            new_expr = expr.deep_copy()
            new_expr.expr.source = code_location
            new_expr.expr.code_location = code_location
            new_expr.index = stmt_idx

            # clear the trace path
            new_expr.forward_path = set()
            new_expr.backward_path = set()

            callsite.backward_exprs.append(new_expr)

    def _push_use_to_caller(self, caller, callsite, argument_use_exprs):
        """
        Push callee's argument use exprs to all caller function, not callsite.
        In this case, will only trace the single argument vars.
        """

        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)

        callee_use_exprs = caller.callee_use_exprs
        if addr not in callee_use_exprs:
            callee_use_exprs[addr] = []

        record_use_exprs = callee_use_exprs[addr]
        arg_variables = set()
        load_actions = {}

        for use_expr in argument_use_exprs:

            # print("argument use: %s" % (use_expr))
            use_ast = use_expr.expr.ast

            new_use_expr = use_expr.deep_copy()
            new_use_expr.expr.source = code_location
            new_use_expr.index = 0

            # clear the trace path
            new_use_expr.forward_path = set()
            new_use_expr.backward_path = set()

            sims = use_expr.expr.sims
            # print("sims: %s" % (sims))

            if push_use_level == 1:

                if len(sims) == 1:
                    record_use_exprs.append(new_use_expr)

                    for arg_sym in sims:
                        arg_variables.add(arg_sym)

                    self._collect_load_variables(use_expr, load_actions)

                else:
                    callsite.backward_exprs.append(new_use_expr)

            elif push_use_level == 2:
                record_use_exprs.append(new_use_expr)

                for arg_sym in sims:
                    arg_variables.add(arg_sym)

                self._collect_load_variables(use_expr, load_actions)

        # for load_action in load_actions.values():
        #     symbols = load_action.action_data.variables

        #     for sym in symbols:
        #         if sym in arg_variables:
        #             arg_variables.remove(sym)

        # print("arg variables: %s" % (arg_variables))

        if len(arg_variables):
            argument_exprs = self._initialize_argument_registers(callsite, arg_variables, trace_dir='B', pattern='OB', data_type='Arg')
            # print("callsite: %s, argument_exprs: %s" % (callsite, argument_exprs))

            for arg_expr in argument_exprs:
                # print("arg_expr: %s %s" % (arg_expr, arg_expr.expr.alias_id))
                if arg_expr not in callsite.backward_exprs:
                    callsite.backward_exprs.append(arg_expr)

        # if len(load_actions):
        #     load_exprs = self._initialize_argument_load(callsite, load_actions, trace_dir='B', pattern='OB', data_type='Arg')
        #     print("callsite: %s, load_exprs: %s" % (callsite, load_exprs))

        #     for load_expr in load_exprs:
        #         callsite.backward_exprs.append(load_expr)

    def _push_def_to_caller(self, caller, callsite, argument_def_exprs):
        """
        Push callee's argument def exprs to all caller function, not callsite.
        In this case, will only trace the single argument vars.
        """

        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)

        callee_def_exprs = caller.callee_def_exprs
        if addr not in callee_def_exprs:
            callee_def_exprs[addr] = []

        record_def_exprs = callee_def_exprs[addr]
        arg_variables = set()
        load_actions = {}

        for def_expr in argument_def_exprs:

            # print("argument def: %s" % (def_expr))
            def_ast = def_expr.expr.ast

            new_def_expr = def_expr.deep_copy()
            new_def_expr.expr.source = code_location
            new_def_expr.index = 0

            # clear the trace path
            new_def_expr.forward_path = set()
            new_def_expr.backward_path = set()

            sims = def_expr.expr.sims
            # print("sims: %s" % (sims))

            if push_def_level == 1:

                if len(sims) == 1:
                    record_def_exprs.append(new_def_expr)

                    for arg_sym in sims:
                        arg_variables.add(arg_sym)

                    self._collect_load_variables(def_expr, load_actions)

                else:
                    callsite.backward_exprs.append(new_def_expr)

            elif push_def_level == 2:
                record_def_exprs.append(new_def_expr)

                for arg_sym in sims:
                    arg_variables.add(arg_sym)

                self._collect_load_variables(def_expr, load_actions)

        for load_action in load_actions.values():
            symbols = load_action.action_data.variables

            for sym in symbols:
                if sym in arg_variables:
                    arg_variables.remove(sym)

        # print("arg variables: %s" % (arg_variables))

        if len(arg_variables):
            argument_exprs = self._initialize_argument_registers(callsite, arg_variables, trace_dir='B', pattern='BF', data_type='Arg')
            # print("callsite: %s, argument_exprs: %s" % (callsite, argument_exprs))

            for arg_expr in argument_exprs:
                # print("arg_expr: %s %s" % (arg_expr, arg_expr.expr.alias_id))
                if arg_expr not in callsite.backward_exprs:
                    callsite.backward_exprs.append(arg_expr)

        if len(load_actions):
            load_exprs = self._initialize_argument_load(callsite, load_actions, trace_dir='B', pattern='BF', data_type='Arg')
            # print("callsite: %s, load_exprs: %s" % (callsite, load_exprs))

            for load_expr in load_exprs:
                callsite.backward_exprs.append(load_expr)

    def _get_argument_use_exprs(self, funcea, use_exprs):
        '''
        Get a function's argument use expr in all use exprs.
        The argument use expr will be traced in caller function.
        '''

        # make a list copy
        use_exprs = use_exprs[:]

        # summary and merge all use exprs, this will merge similar expressions.
        # self._merge_exprs(use_exprs)

        # record the merge use exprs
        collect_summary_use_exprs[funcea] = use_exprs

        argument_exprs = []
        for use_expr in use_exprs:
            trace_ast = use_expr.expr.ast
            if is_argument(trace_ast):
                argument_exprs.append(use_expr)
                # print("argument use: %s" % (use_expr))

        return argument_exprs

    def _get_argument_def_exprs(self, function, def_exprs):
        '''
        Get a function's argument or global def expr in all def exprs.
        The argument or global def expr will be traced in caller function.
        '''

        push_exprs = []
        # make a list copy
        def_exprs = def_exprs[:]

        # simplify_base_offset_exprs(def_exprs, data_type='Tdata')

        # summary and merge all def exprs, this will merge similar expressions.
        # self._merge_exprs(def_exprs)
        merged_exprs = merge_simlilar_exprs_v1(def_exprs)

        arguments = function.arguments
        for def_expr in merged_exprs:
            # print("def-expr: %s" % (def_expr))
            if def_expr.only_contain_argument(arguments):
                base_scope = get_expr_base_pointer_type(def_expr)
                base_ptr = def_expr.expr.base_ptr

                if base_scope == 'aptr':
                    def_expr.expr.scope = 'aptr'
                    push_exprs.append(def_expr)
                    # print("\nargument-def: %s" % (def_expr))

                # elif base_scope == 'global':
                if type(base_ptr) is int:
                    def_expr.expr.scope = 'global'
                    push_exprs.append(def_expr)
                    # print("\nglobal-def: %s" % (def_expr))

        return push_exprs

    def _collect_load_variables(self, trace_expr, load_actions):
        """
        Collect all the load variables (e.g. load(rdi+0x20)), then trace it in caller function.
        """

        sim_actions = trace_expr.expr.sim_actions

        for index, sim_action in sim_actions.items():
            # print("sim action: %d %s" % (index, sim_action))

            if sim_action.name and sim_action.live:

                action_type = sim_action.action_data.op

                if action_type == 'Load' or ('BF' in trace_expr.expr.pattern and action_type == 'Store'):

                    data = sim_action.action_data
                    data_hash = data.__hash__()


                    if data_hash not in load_actions:
                        load_actions[data_hash] = sim_action

        # print("load variables: %s" % (load_variables))

    def _make_ret_define_copy_to_retsite(self, callsite, ret_pointer_defines):
        """
        :param callsite: a block node which has a call.
        :param
        """
        copy_exprs = []
        addr = callsite.addr
        stmt_idx = 0
        code_location = CodeLocation(addr, stmt_idx)

        for expr in ret_pointer_defines:
            new_expr = expr.deep_copy()
            new_expr.expr.source = code_location
            # new_expr.expr.code_location = code_location

            # TODO
            # If the ret_pointer is a heap addr, this should update the alias_id
            new_expr.expr.alias_id = hash((expr.expr.alias_id, code_location.__hash__()))

            new_expr.index = 0
            callsite.callsite_exprs.append(new_expr)

    def _pre_process_function(self, function):
        # print("pre_process_function: %s" % (function))
        if function.cfg is not None:
            l.info("The function %s has been pre process!" % (function))
            return

        funcea = function.addr
        # start_ida_block = self._ida_object.ida_cfg._ida_blocks.get(funcea)
        s_ida_blocks = self._ida_object.ida_cfg.find_function_start_ida_block(funcea)

        if self.switch_check:
            start_ida_blocks = s_ida_blocks
        else:
            start_ida_blocks = [n for n in s_ida_blocks if n.addr == funcea]

        if len(start_ida_blocks) == 0:
            l.info("The function %x not been added in work functions, add it future." % (funcea))
            return

        # print("Ida-start-block: %s" % (start_ida_blocks))

        cfg = FunctionCFG(funcea, self._ida_object, self.proj)
        cfg.generate_function_cfg(function, start_ida_blocks)
        function.cfg = cfg

        if funcea not in cfg._nodes:
            l.error("The function %s have error cfg." % (function))
            function.cfg = None
            return
        function.start_node = cfg._nodes[funcea]
        function.start_node.special_flag |= 0x1

        # function.cfg.print_cfg()
        # function.cfg.print_cfg_edges()

        try:
            self._loop_parser.get_loops_from_graph(function)
        except:
            l.error("The function %s have error cfg while parser loop." % (function))

        if len(function.cfg.pre_sequence_nodes) == 0:
            if self.switch_check:
                start_nodes = function.cfg.get_start_nodes()
            else:
                start_nodes = [function.start_node]
            function.get_pre_sequence_in_function(start_nodes)
            self._pre_process_function_vex(function)

            # for n in pre_sequence_nodes:
            #     print("xxx- %s" % (n))
            # for loop in function.loops:
            #     for n in loop.body_nodes:
            #         print("xxxl- %s" % (n))

        # Check the exit blocks, especially some functions has no return and
        # exit with a loop.
        exit_blocks = function.cfg.exit_blocks
        if len(exit_blocks) == 0:
            exit_block = cfg.get_special_exit_block()
            if exit_block is None:
                l.info("We could not find the exit block in function %s" % (function))
                l.info("Then we choose the last block in pre_sequence_nodes as exit block!")
                exit_block = function.cfg.pre_sequence_nodes[-1]
            exit_blocks.add(exit_block)
            # print("psu-debug: get exit-block: %s" % (exit_block))

        # self._pre_process_loops(function)

        # print("Start get graph parser!!!")
        # graph_parser = GraphMethod(cfg, function.start_node, exit_blocks=exit_blocks)
        # print("graph parser done!!!")
        # function.graph_parser = graph_parser

    def _pre_process_loops(self, function):

        for loop in function.loops:
            # print("\nLOOP-T: %s" % (loop))
            ddg_graph = self._fast_dataflow.execute_loop(loop, loop_execute_times=3)
            self._fast_dataflow.label_inc_flag_in_loop(function, ddg_graph)

    def _initialize_ret_register(self, function, ret_type):
        exit_blocks = function.cfg.exit_blocks
        ret_register = 'r%d' % self._binary_parser.ret_offset
        ret_data = claripy.BVS(ret_register, self._binary_parser.arch_bits, explicit_name=True)
        ret_expr = VarExpr(ret_data, value=ret_data, pattern='RSBF', trace_dir='B', data_type='Ret', var_type=ret_type)
        ret_expr.is_ret = True
        ret_expr.get_trace_variable()
        ret_expr.initial_sims(var_type=ret_type)
        # print("initial-ret: %s %s" % (ret_expr, ret_expr.sims))
        for exit_block in exit_blocks:
            stmts_len = len(exit_block.irsb.statements) if exit_block.irsb else 0
            code_location = CodeLocation(exit_block.addr, stmts_len)
            ret_expr.source = code_location
            ret_expr.location = code_location
            ret_expr.alias_id = code_location.__hash__()
            ret_trace = TraceExpr(ret_expr, stmts_len)
            exit_block.backward_exprs.append(ret_trace)

    def get_block_jump_condition(self, node):
        constraint = self._binary_parser.get_constraint(node)
        if constraint is not None:
            node.jump_guard = constraint

        else:
            l.info("Block %s didn't have jump condition." % (node))

    def trace_condition_in_block(self, node):
        if node.jump_guard is None:
            return []

        constraint = node.jump_guard
        bool_con = constraint.args[0]
        constraint_expr = self._make_trace_expr_for_constraint(node, bool_con)
        # print("constraint expr: %s" % (constraint_expr))
        self._get_block_stack_pointer_tmp(node)
        sp_tmp = node.sp_tmp_offset
        bb = node.shallow_copy()
        bb.backward_exprs = [constraint_expr]
        con_exprs = bb.backward_exprs[:]
        self._binary_parser.backward_data_trace(bb, con_exprs, sp_tmp)
        # print("get backward constraint expr: %s" % (bb.backward_exprs))
        return bb.backward_exprs

    def get_succ_block_constraint(self, node, function):
        if node.jump_guard is None:
            return

        func_cfg = function.cfg
        irsb = node.irsb
        constraint = node.jump_guard
        next_stmt = irsb.next
        if type(next_stmt) is pyvex.expr.Const:
            next_block_addr = next_stmt.con.value

        if next_block_addr is None:
            l.info("Block %s has not next block, some error!!!" % (node))
            return

        false_branch, true_branch = None, None
        succ_blocks = func_cfg.graph.successors(node)
        for b in succ_blocks:
            if b.addr == next_block_addr:
                false_branch = b
            else:
                true_branch = b

        if false_branch is None:
            l.info("Get block %s 's default branch error!!!" % (node))
        if true_branch is None:
            l.info("Block %s maybe has indirect ture jump branch." % (node))

        bool_con = constraint.args[0]
        if type(bool_con) is not claripy.ast.bool.Bool:
            l.info("The con %s is not a bool expr, do it future." % (bool_con))
            return

        true_con = bool_con
        false_con = claripy.Not(true_con)
        true_branch.constraints.append(true_con)
        false_branch.constraints.append(false_con)
        # print("Block %s has con %s" % (true_branch, true_con))
        # print("Block %s has con %s" % (false_branch, false_con))

    def _make_trace_expr_for_constraint(self, block, constraint):
        stmts_len = len(block.irsb.statements)
        block_addr = block.addr
        data = VarExpr(constraint, pattern='Cptr', trace_dir='B')
        data.alias_id = hash((block_addr, constraint.__hash__()))
        constraint_expr = TraceExpr(data, index=stmts_len)
        constraint_expr.get_trace_variable()
        return constraint_expr

    def _make_trace_expr_for_constraint_vars(self, block, constraint_vars):
        con_var_exprs = []
        stmts_len = len(block.irsb.statements)
        block_addr = block.addr
        for var in constraint_vars:
            data = VarExpr(var, pattern='Cptr', trace_dir='B')
            data.alias_id = hash((block_addr, var.__hash__()))
            trace_expr = TraceExpr(data, index=stmts_len)
            trace_expr.get_trace_variable()
            con_var_exprs.append(trace_expr)

        return con_var_exprs

    def _get_constraint_in_loop(self, loop):
        if len(loop.constraints):
            return

        for node in loop.end_nodes:
            self.get_block_jump_condition(node)
            if node.jump_guard is not None:
                cons_exprs = self.trace_condition_in_block(node)
                loop.constraints.extend(cons_exprs)
                # self.get_succ_block_constraint(node, function)

            else:
                l.info("Block %s didn't get constraint." % (node))
                continue

        # print("Loop %s has constraints %s" % (loop, loop.constraints))

    def _extract_constant_in_loop_constraints(self, loop):
        concrete_cons = {}
        for constraint_expr in loop.constraints:
            self._extract_constant_in_constraint(constraint_expr, concrete_cons)
        # print("get constraint: %s" % (concrete_cons))
        return concrete_cons

    def _extract_constant_in_constraint(self, constraint_expr, concrete_cons):
        con_ast = constraint_expr.expr.ast
        cc_deps = parse_bool_condition(con_ast)
        if len(cc_deps) == 0:
            return

        cc_data1, cc_data2 = cc_deps[0], cc_deps[1]
        if cc_data1.concrete and cc_data2.symbolic:
            concrete_cons[cc_data2.variables] = cc_data1

        elif cc_data1.symbolic and cc_data2.concrete:
            concrete_cons[cc_data1.variables] = cc_data2

    def _backward_data_flow_analysis(self, function):
        """
        Analyze a function by static data flow analysis.
        :param function: a object instance of FunctionAttribute
        """
        analyzed_blocks = set()
        func_cfg = function.cfg
        pre_sequence_nodes = func_cfg.pre_sequence_nodes
        for i in range(len(pre_sequence_nodes)-1, -1, -1):
            block = pre_sequence_nodes[i]

            if block in analyzed_blocks:
                continue

            # print("\n+++--> Backward analyze block %s" % (block))
            # print("backward expr %s\nforward expr %s" % (block.backward_exprs, block.forward_exprs))

            if block.is_loop:
                loop = function.determine_node_in_loop(block)

                self._backward_process_loop(function, block, loop, analyzed_blocks)

                # loop_in_blocks = loop.in_nodes
                # self._check_loop_definition(loop, loop_in_blocks, func_cfg, 'B')

                # While the node in cycle is executed, clear the backward
                # and forward trace exprs.
                for n in loop.body_nodes:
                    n.forward_exprs = []
                    n.backward_exprs = []

            else:
                self._block_execute(function, block, flow_dir='B')
                analyzed_blocks.add(block)

    def _forward_data_flow_analysis(self, function):
        """
        Analyze a function by static data flow analysis.
        :param function: a object instance of FunctionAttribute
        """
        analyzed_blocks = set()
        # analyzed_cycles = []
        func_cfg = function.cfg
        # work_list = [start_block]
        # work_list = func_cfg.post_order_nodes[:]
        # while work_list:
        for block in func_cfg.pre_sequence_nodes:
            # print("\n+++--> Forward analyze block %s" % (block))
            # print("backward expr %s\nforward expr %s" % (block.backward_exprs, block.forward_exprs))

            if block in analyzed_blocks:
                continue

            if block.is_loop:
                loop = function.determine_node_in_loop(block)
                self._forward_process_loop(function, block, loop, analyzed_blocks)

                for n in loop.body_nodes:
                    n.forward_exprs = []
                    n.backward_exprs = []

            else:
                # print("\n+++--> Forward analyze block %s" % (block))
                # print("+++--# forward expr: %s" % (block.forward_exprs))
                self._block_execute(function, block, flow_dir='F')
                analyzed_blocks.add(block)

    def _get_argument_define_to_callee(self, block):
        """
        Get all the argument define in a callsite.
        """
        forward_callee_exprs = []
        forward_exprs = block.forward_exprs
        for expr in forward_exprs:
            if 'BF' in expr.expr.pattern:
                data_ast = expr.expr.ast
                is_arg_def = is_argument_define(data_ast)
                if is_arg_def:
                    forward_callee_exprs.append(expr)

        return forward_callee_exprs

    def _get_argument_define_in_callsite(self, callsite):
        """
        Get all the argument define in the callsite.
        """
        arg_define_info = {}
        forward_exprs = callsite.forward_exprs

        for expr in forward_exprs:
            data_ast = expr.expr.ast
            data_type = expr.expr.data_type

            if data_type in ['Vptr', 'Fptr', 'Aptr']:

                arg_syms = get_argument_syms(data_ast)

                if len(arg_syms) == 0:
                    continue

                if data_ast.op == 'BVS':
                    arg_sym = arg_syms[0]
                    if data_type == 'Fptr':
                        arg_define_info[arg_sym] = ('BF', 'Fptr')

                    elif data_type == 'Vptr':
                        arg_define_info[arg_sym] = ('LBF', 'Vptr')

                    elif data_type == 'Aptr':
                        arg_define_info[arg_sym] = ('SLBF', 'Aptr')

                # TODO
                # elif data_ast.op == 'Store':
                #     for arg_sym in arg_syms:
                #         if arg_sym in load_info:
                #             arg_define_info[arg_sym] = ('SLBF', 'Aptr')

                #     value = expr.expr.value
                #     if (value is not None and value.op == 'BVS' and
                #             value.args[0] in argument_vars):

                #         pass

        # for arg_sym, pattern in arg_define_info.items():
        #     print("callsite def: %s %s" % (arg_sym, pattern))

        return arg_define_info

    def _get_argument_taint_info(self, callsite, callee_function, call_type=None):
        """
        Check the forward_exprs whether labed taint trace_expr that contain argument.
        And judge if we should forward taint analysis to callee.
        """
        killed_exprs = []
        callsite_taint_exprs = []
        forward_exprs = callsite.forward_exprs
        arguments = callee_function.arguments
        stack_args = get_stack_arguments(arguments)
        # print("%s has args: %s %s" % (callee_function, arguments, stack_args))

        for trace_expr in forward_exprs:
            data_type = trace_expr.expr.data_type
            flag = trace_expr.expr.flag
            source = trace_expr.expr.source
            # print("forward-to-callee: %s %s %s" % (trace_expr, callsite, source))
            if data_type != 'Tdata' or flag & 0x100 != 0x100:
                continue
            elif source.block_addr == callsite.addr:
                continue

            if len(stack_args):
                new_expr = self.update_stack_store_action(callsite, stack_args, trace_expr, 'F')
                if new_expr is not None:
                    trace_expr = new_expr

            # print("Callsite-expr-%x: %s" % (callsite.addr, trace_expr))
            if callee_function.parameter_has_redefined(trace_expr):
                # print("Par-has-redefined: %s %s %s" % (callee_function, trace_expr, trace_expr.expr.is_ret))
                killed_exprs.append(trace_expr)
                if trace_expr.expr.ast.op not in ls_ops:
                    continue

            sims = trace_expr.expr.sims
            data_ast = trace_expr.expr.ast

            if trace_expr.expr.scope is None:
                base_scope = get_expr_base_pointer_type(trace_expr)
                trace_expr.expr.scope = base_scope

            if call_type == 'main' and trace_expr.contain_argument_or_global(arguments):
                base_scope = trace_expr.expr.scope
                base_ptr = trace_expr.expr.base_ptr

                # if base_scope == 'global':
                if type(base_ptr) is int and get_scope(base_ptr) == 'global':
                    if not callsite.contain_exprs(trace_expr) and trace_expr not in callsite_taint_exprs:
                        callsite_taint_exprs.append(trace_expr)
                    # print("Forward callsite global-def taint: %s" % (trace_expr))

                else:
                    if (not callsite.contain_exprs(trace_expr) and
                            trace_expr not in callsite_taint_exprs):
                        callsite_taint_exprs.append(trace_expr)

            elif call_type == 'lib' and trace_expr.contain_argument_ptr(arguments):
                if not callsite.contain_exprs(trace_expr) and trace_expr not in callsite_taint_exprs:
                    callsite_taint_exprs.append(trace_expr)

        if len(killed_exprs):
            self._update_trace_iids(callsite, killed_exprs)
            self._accurate_dataflow.kill_all_alias_exprs(forward_exprs, killed_exprs)

        # print("taint info: %s" % (callsite_taint_exprs))
        return callsite_taint_exprs

    def _get_callsite_argument_pointer_info(self, callsite, callee_function):
        """
        Get all the argument pointer in the callsite.
        """
        callsite_arg_info = {}
        arguments = callee_function.arguments
        forward_exprs = callsite.forward_exprs
        print("callsite %s has %s" % (callee_function, arguments))

        for trace_expr in forward_exprs:
            if trace_expr.expr.source.block_addr == callsite.addr:
                continue

            data_ast = trace_expr.expr.ast
            data_type = trace_expr.expr.data_type
            sim_actions = trace_expr.expr.sim_actions
            trace_sims = trace_expr.expr.sims

            if ((data_ast.op in ['BVS', 'Store'] and data_type in ['Vptr', 'Fptr', 'Aptr']) or
                    (data_ast.op == 'Load' and data_type == 'Tdata' and len(sim_actions) == 1 and sim_actions[0].live)):
                for var, sim in trace_sims.items():
                    if sim.var_type == 'ptr' and type(var) == str and var in arguments:
                        if data_type == 'Fptr':
                            t_pattern = 'BF'
                        elif data_type == 'Vptr':
                            t_pattern = 'LBF'
                        elif data_type == 'Aptr':
                            t_pattern = 'SLBF'
                        elif data_type == 'Tdata':
                            t_pattern = 'SBF'

                        callsite_arg_info[var] = (t_pattern, 'Aptr')

        # for arg, info in callsite_arg_info.items():
        #     print("In-callsite: %s, get %s %s" % (callsite, arg, info))
        return callsite_arg_info

    def _get_argument_info_from_callee_definition(self, trace_exprs):
        """
        Get all the argument define in the callsite.
        """
        arg_define_info = {}
        for expr in trace_exprs:
            data_ast = expr.expr.ast
            data_type = expr.expr.data_type

            arg_syms = get_argument_syms(data_ast)

            if len(arg_syms) == 0:
                continue

            for arg_sym in arg_syms:
                arg_define_info[arg_sym] = ('BF', 'Arg')

        # for arg_sym, pattern in arg_define_info.items():
        #     print("callee argument info: %s %s" % (arg_sym, pattern))

        return arg_define_info

    def _initialize_argument_registers(self, block, arg_variables, trace_dir=None, pattern=None, data_type=None):

        trace_arguments = []
        arch_bits = self._binary_parser.arch_bits
        block_addr = block.addr
        code_location = CodeLocation(block_addr, 0)

        for arg_sym in arg_variables:
            data = claripy.BVS(arg_sym, arch_bits, explicit_name=True)
            expr = VarExpr(data, pattern=pattern, trace_dir=trace_dir, data_type=data_type)
            expr.get_trace_variable()
            expr.initial_sims()

            expr.source = code_location
            expr.location = code_location
            expr.alias_id = hash((code_location, pattern))
            expr.value = data

            trace_expr = TraceExpr(expr, 0)
            trace_arguments.append(trace_expr)

        return trace_arguments

    def _initialize_argument_load(self, block, load_actions, trace_dir=None, pattern=None, data_type=None):

        load_exprs = []
        arch_bits = self._binary_parser.arch_bits
        block_addr = block.addr
        code_location = CodeLocation(block_addr, 0)

        for sim_action in load_actions.values():
            data = sim_action.action_data
            expr = VarExpr(data, pattern=pattern, trace_dir=trace_dir, data_type=data_type)
            expr.get_trace_variable()
            expr.initial_sims()

            expr.source = code_location
            expr.location = code_location
            expr.alias_id = hash((code_location, pattern))
            expr.value = data

            new_sim_action = sim_action.copy()
            new_sim_action.def_locs = {code_location}
            expr.sim_actions[0] = new_sim_action

            trace_expr = TraceExpr(expr, 0)
            load_exprs.append(trace_expr)

        return load_exprs

    def _initialize_trace_argument(self, block, arg_define_info, trace_dir=None):

        trace_arguments = []
        arch_bits = self._binary_parser.arch_bits
        block_addr = block.addr
        code_location = CodeLocation(block_addr, 0)

        for arg_sym, info in arg_define_info.items():
            pattern, data_type = info
            data = claripy.BVS(arg_sym, arch_bits, explicit_name=True)
            expr = VarExpr(data, pattern=pattern, trace_dir=trace_dir, data_type=data_type)
            expr.get_trace_variable()

            expr.source = code_location
            expr.location = code_location
            expr.alias_id = code_location.__hash__()
            expr.value = data

            trace_expr = TraceExpr(expr, 0)
            trace_arguments.append(trace_expr)

        return trace_arguments

    def _initialize_trace_argument_pointers(self, start_block, arg_info):

        initial_exprs = []
        funcea = start_block.addr
        code_location = CodeLocation(funcea, 0)

        for arg_sym, info in arg_info.items():
            pattern, data_type = info
            data = BVS(arg_sym)
            expr = VarExpr(data, value=data, pattern=pattern, trace_dir='F', data_type=data_type, var_type='ptr')
            expr.initial_sims(var_type='ptr')

            expr.source = code_location
            expr.location = code_location
            expr.alias_id = code_location.__hash__()
            expr.base_ptr = arg_sym

            trace_expr = TraceExpr(expr, 0)
            initial_exprs.append(trace_expr)

        for initial_expr in initial_exprs:
            start_block.forward_exprs.append(initial_expr)

    def _initialize_taint_info_in_function(self, start_block, callsite_taint_exprs):

        for taint_expr in callsite_taint_exprs:
            new_expr = taint_expr.deep_copy()
            new_expr.clear_path()
            new_expr.index = 0
            # new_expr.expr.alias_id = taint_expr.expr.ast.__hash__()
            new_expr.set_taint_id()
            new_expr.clear_sim_actions_locs()
            new_expr.expr.is_ret = False
            start_block.forward_exprs.append(new_expr)
            # print("Callee-initial: %s %s\n taint-id: %s" % (start_block, new_expr, new_expr.expr.taint_id))

    def _initialize_taint_expr_in_function(self, callsite, start_block, taint_expr):

        # print("old-ptr-id: %x count: %d" % (taint_expr.expr.ptr_id, count))
        new_expr = taint_expr.deep_copy()
        new_expr.clear_path()
        new_expr.index = 0
        # new_expr.expr.alias_id = taint_expr.expr.ast.__hash__()
        new_expr.set_taint_id()
        new_expr.clear_sim_actions_locs()
        new_expr.expr.is_ret = False
        new_expr.expr.ptr_id = taint_expr.iid
        new_expr.inter_funcs.append('%x' % start_block.func_addr)
        if callsite.node_type == 'iCall':
            new_expr.inter_icall_level += 1
        start_block.forward_exprs.append(new_expr)
        # print("Callee-initial: %s %s\n taint-id: %s ptr-id: %x" % (start_block, new_expr, new_expr.expr.taint_id, new_expr.expr.ptr_id))

    def _check_whether_callinto(self, function):
        """
        Check the function's flag and judge if should call into callee.
        """
        pass

    def _get_ida_object(self, addr):
        """
        Each bianry (main or libary) has a ida object.
        """
        pass

    def _get_lib_function_by_name(self, lib_func_name):
        """
        Get the lib function by lib_func_name.
        """
        if lib_func_name in ['iCall']:
            return None

        lib_func_ob = self.proj.loader.find_symbol(lib_func_name)
        # print("find_symbol: %s %s" % (lib_func_name, lib_func_ob))
        if lib_func_ob is None:
            l.info("The lib function %s not found in libary!!!" % (lib_func_name))
            return None

        libary_name = lib_func_ob.owner.provides
        # print("lib func: %s in %s" % (lib_func_ob, libary_name))
        # print("libary_objects: %s" % (self._libary_objects))
        libary_object = self._libary_objects.get(libary_name)
        # print("libary_object: %s" % (libary_object))
        if libary_object is None:
            l.info("The libary %s has not been analyzed by Ida Pro!!!" % (libary_name))
            return

        lib_function = libary_object.cg.get_function_by_addr(lib_func_ob.rebased_addr)
        return lib_function

    def _get_function_by_addr(self, addr):
        """
        Get function by the given addr, the function may be nomal or lib func.
        """
        pass

    def _call_into_callee_backward(self, callsite, caller_function, callee_function, parameter_ptrs):
        """
        Call into callee function, and get the callee's argument definitions and alias.
        """
        arg_ptr_info = {}
        info = ('SLBF', 'Aptr')
        funcea = callee_function.addr
        self._pre_process_function(callee_function)

        if callee_function.cfg is None:
            return

        for arg in parameter_ptrs:
            if arg in callee_function.arg_contexts or arg not in callee_function.arguments:
                continue
            arg_ptr_info[arg] = info
            callee_function.arg_contexts.append(arg)

        start_block = callee_function.start_node

        # Calculate the argument ptr context, each different context should re-execute
        # the callee function (data flow analysis).
        if len(arg_ptr_info):
            self._initialize_trace_argument_pointers(start_block, arg_ptr_info)

            count = function_analyzed_times[funcea]
            if count >= FUNC_MAX_TIMES:
                l.info("The function 0x%x has been execute %d times, ignore it." % (funcea, count))
            else:
                self._execute_function(callee_function, execute_flag=0x3)

    def _call_into_lib_callee(self, callsite, caller_function, callee_function, libary_object, loop, flow_dir):
        """
        Call into lib function, this mode should have load libary binaries.
        """
        is_taint = False

        self._pre_process_lib_function(callee_function, libary_object)
        start_block = callee_function.start_node

        callsite_taint_exprs = self._get_argument_taint_info(callsite, callee_function, call_type='lib')
        backup_taint_exprs = callsite_taint_exprs[:]

        # Calculate the taint context, each different context should re-execute
        # the callee function (taint analysis).
        self._check_args_in_exprs(callee_function, callsite_taint_exprs)
        for taint_expr in callsite_taint_exprs:
            is_analyzed = callee_function.is_taint_context_analyzed(taint_expr)
            if not is_analyzed:
                self._initialize_taint_expr_in_function(callsite, start_block, taint_expr)
                is_taint = True

        # if len(callsite_taint_exprs):
        #     taint_flag = function.is_taint_context_analyzed(callsite_taint_exprs)
        #     # print("xpx: %s %s" % (callsite_taint_exprs, taint_flag))

        #     if taint_flag:
        #         is_taint = False

        #     else:
        #         self._initialize_taint_info_in_function(start_block, callsite_taint_exprs)

        # else:
        #     is_taint = False

        if is_taint:
            self._accurate_dataflow.set_concret_contexts(callsite, callee_function)

            # print("Call-lib: %s" % (function.procedural_name))
            if callee_function.procedural_name not in ['hsearch_r', 'hdestroy_r', 'hcreate_r']:
                debug

            self._execute_function(callee_function, execute_flag=0x2)

            # function.add_analyzed_taint_contexts(callsite_taint_exprs)

        if len(callee_function.taint_exprs):
            remove_exprs = []
            # for t_expr in function.taint_exprs:
            #     print("%s has %s" % (function, t_expr))

            callee_taint_exprs = callee_function.get_taint_exprs(None, backup_taint_exprs)
            # print("%s has taint exprs (lib):\n %s" % (function, callee_taint_exprs))
            for taint_expr in callee_taint_exprs:
                if not taint_expr.expr.is_ret and taint_expr in backup_taint_exprs:
                    remove_exprs.append(taint_expr)

            for r_expr in remove_exprs:
                callee_taint_exprs.remove(r_expr)

            self._process_callsite_callee_taint_in_forward(callsite, caller_function, callee_function, loop, callee_taint_exprs, flow_dir)

    def _call_into_callee_forward(self, callsite, caller_function, callee_function, loop, flow_dir):
        """
        Call into callee function, and get the callee's argument definitions and alias.
        Or trace the taint expr by forward analysis.
        """
        is_taint, is_arg = False, False
        funcea = callsite.target

        self._pre_process_function(callee_function)

        if callee_function.cfg is None:
            self._check_return_register_redefine(callsite)
            return

        start_block = callee_function.start_node

        # Calculate the argument ptr context, each different context should re-execute
        # the callee function (data flow analysis).
        arg_ptr_info = self._get_callsite_argument_pointer_info(callsite, callee_function)
        arg_flag = len(arg_ptr_info)
        callee_function.check_arg_ptrs(arg_ptr_info)
        if len(arg_ptr_info):
            print("HHH-> %s has %s" % (callsite, arg_ptr_info))
            self._initialize_trace_argument_pointers(start_block, arg_ptr_info)
            is_arg = True

        # if len(arg_ptr_info):
        #     callee_function.check_arg_ptrs(arg_ptr_info)

        #     if len(arg_ptr_info):
        #         self._initialize_trace_argument_pointers(start_block, arg_ptr_info)

        #     else:
        #         is_arg = False

        # else:
        #     is_arg = False

        # Calculate the taint context, each different context should re-execute
        # the callee function (taint analysis).
        if self.taint_check:
            # print("xxx-> %s" % (callsite.forward_exprs))
            callsite_taint_exprs = self._get_argument_taint_info(callsite, callee_function, call_type='main')
            for cs_taint in callsite_taint_exprs:
                print("ooo-> %s 0x%x %s" % (cs_taint, cs_taint.expr.taint_source, cs_taint.inter_funcs))
            if len(caller_function.input_global_taints):
                callee_function.merge_input_global_taints_v1(callsite, caller_function.input_global_taints)
            if len(callsite_taint_exprs):
                callee_function.merge_input_global_taints_v2(callsite, callsite_taint_exprs)

            self._check_args_in_exprs(callee_function, callsite_taint_exprs)
            # print("ooo2-> %s" % (callsite_taint_exprs))

            self._check_taint_source(caller_function, callsite_taint_exprs)

            # Special case - merge RecursiveExpr
            callsite_taint_exprs = merge_recurisive_exprs(callsite_taint_exprs, min_level=1)

            # print("F-Taint: %s" % (callsite))
            for base_addr, g_taint_exprs in callee_function.input_global_taints.items():
                if callee_function.special_flag & 0x2 and base_addr not in callee_function.global_addrs:
                    # print("MMM-skip->%s 0x%x" % (callsite, base_addr))
                    continue
                self._check_taint_source(caller_function, g_taint_exprs)
                for g_taint_expr in g_taint_exprs:
                    # print(" -->global-taint: %x %s" % (base_addr, g_taint_expr))
                    is_analyzed = callee_function.is_taint_context_analyzed(g_taint_expr)
                    if not is_analyzed:
                        is_taint = True

            for p_taint_expr in callsite_taint_exprs:
                is_analyzed = callee_function.is_taint_context_analyzed(p_taint_expr)
                # print(" -->parameter-taint: %s %s" % (p_taint_expr, is_analyzed))
                if not is_analyzed:
                    self._initialize_taint_expr_in_function(callsite, start_block, p_taint_expr)
                    is_taint = True

        if is_taint or is_arg:
            count = function_analyzed_times[funcea]
            if count >= FUNC_MAX_TIMES:
                l.debug("The function 0x%x has been execute %d times, ignore it." % (funcea, count))
                # print("The function 0x%x has been execute %d times, ignore it (call-into)." % (funcea, count))
            else:
                self._accurate_dataflow.set_concret_contexts(callsite, callee_function)
                self._execute_function(callee_function, execute_flag=0x2)

        self._check_return_register_redefine(callsite)

        if len(callee_function.taint_exprs):
            remove_exprs = []
            callee_taint_exprs = callee_function.get_taint_exprs(caller_function, callsite_taint_exprs)
            for t_expr in callee_taint_exprs:
                print("  -->%x has taint exprs (main):\n %s %s" % (callee_function.addr, t_expr, t_expr.inter_funcs))
            for taint_expr in callee_taint_exprs:
                # if not taint_expr.expr.is_ret and taint_expr in callsite_taint_exprs:
                #     remove_exprs.append(taint_expr)
                if taint_expr.iid in callsite.traced_iids:
                    remove_exprs.append(taint_expr)

            for r_expr in remove_exprs:
                callee_taint_exprs.remove(r_expr)

            for taint_expr in callee_taint_exprs:
                callsite.traced_iids.add(taint_expr.iid)

            self._process_callsite_callee_taint_in_forward(callsite, caller_function, callee_function, loop, callee_taint_exprs, flow_dir)

        if arg_flag:
            self._process_callsite_callee_aptr_in_forward(callsite, caller_function, callee_function, loop, flow_dir)

    def _process_callee_function_in_forward(self, callsite, caller_function, callee_function, loop, flow_dir):
        """
        According to the context info to execute the callee function.
        """
        do_ret = True

        function_name = callee_function.procedural_name
        # print("func-name: %s" % (function_name))
        if function_name and function_name in self._sim_procedures and self.taint_check: # or is_hooked(funcea)
            proc = self._sim_procedures[function_name]
            check_ret = proc.execute(callsite, self.proj, 'run', flow_dir=flow_dir, purpose = 0, caller_function=caller_function)

        elif function_name in self.ignore_lib_functions:
            do_ret = True

        elif callee_function.binary_name == 'main':
            self._call_into_callee_forward(callsite, caller_function, callee_function, loop, flow_dir)
            do_ret = True

        elif self.taint_check:
            libary_object = self._libary_objects.get(callee_function.binary_name)
            if libary_object is None:
                l.info("The libary %s has not been analyzed by Ida Pro!!!" % (callee_function.binary_name))
                return do_ret
            self._call_into_lib_callee(callsite, caller_function, callee_function, libary_object, loop, flow_dir)

        return do_ret

    def _process_callee_function_in_backward(self, callsite, caller_function, callee_function, parameter_ptrs, loop, flow_dir):
        """
        In backward trace, should trace into callee to update ret value or argument defs.
        """

        check_ret = True
        function_name = callee_function.procedural_name
        if function_name and function_name in self._sim_procedures and self.taint_check: # or is_hooked(funcea)
            proc = self._sim_procedures[function_name]
            check_ret = proc.execute(callsite, self.proj, 'run', flow_dir='B', caller_function=caller_function)

        elif callee_function.binary_name == 'main':
            # Should analyze callee function to get real ret value and update.
            self._update_ret_variable(callsite, callee_function)

            # Should analyze callee function to get parameter ptrs' definitions.
            if len(parameter_ptrs):
                self._call_into_callee_backward(callsite, caller_function, callee_function, parameter_ptrs)

            self._process_callee_definiton_in_callsite(callsite, caller_function, callee_function, loop, flow_dir)
            check_ret = False

        return check_ret

    def _process_callsite_callee_aptr_in_forward(self, callsite, caller_function, callee_function, loop, flow_dir):
        """
        In forward, process callee parameter_ptrs' definitions and alias.
        """
        target = callee_function.addr

        aptr_exprs = self.collector.datas['Aptr'].get(target)
        if not aptr_exprs:
            return

        # print("In-C %s, has %s" % (callsite, aptr_exprs))
        aptr_aliases = self._get_aptr_aliases(aptr_exprs)
        # print("In-callsite-%x has aptr-alias: %s" % (callsite.addr, aptr_aliases))

        if len(aptr_aliases):
            self._process_arg_ptr_aliases_forward(callsite, caller_function, aptr_aliases, loop, flow_dir)

        aptr_defs = self._get_aptr_definitions(aptr_exprs)

        if len(aptr_defs):
            self._process_forward_arg_ptr_defs(callsite, caller_function, aptr_defs, loop, flow_dir)

    def _process_arg_ptr_aliases_forward(self, callsite, caller_function, aptr_aliases, loop, flow_dir):
        """
        In forward, the callee maybe save parameter_ptr to mem and generate ptr alias.
        """
        new_backward_exprs = []
        new_forward_exprs = []
        reg_alias_info, load_alias_info = {}, {}
        location = CodeLocation(callsite.addr, 0)

        # if self.icall_check:
        aptr_aliases = merge_simlilar_exprs_v3(aptr_aliases)

        for aptr_alias in aptr_aliases:
            # print("Aptr-alias: %s" % (aptr_alias))
            value = aptr_alias.expr.value
            if value.op == 'BVS':
                var = value.args[0]
                if var not in reg_alias_info:
                    reg_alias_info[var] = []
                aptr_alias = aptr_alias.deep_copy()
                for sim_action in aptr_alias.expr.sim_actions.values():
                    if sim_action.action_data.op == 'Store':
                        sim_action.def_locs.add(location)
                reg_alias_info[var].append(aptr_alias)

            elif value.op == 'Load':
                value_id = value.__hash__()
                if value_id not in load_alias_info:
                    load_alias_info[value_id] = []
                aptr_alias = aptr_alias.deep_copy()
                for sim_action in aptr_alias.expr.sim_actions.values():
                    if sim_action.action_data.op == 'Store':
                        sim_action.def_locs.add(location)
                load_alias_info[value_id].append(aptr_alias)

        for trace_expr in callsite.forward_exprs:
            # print("Callsite-%x-has-forward: %s" % (callsite.addr, trace_expr))
            base_ptr = trace_expr.expr.base_ptr
            if base_ptr in reg_alias_info:
                alias_exprs = reg_alias_info[base_ptr]
                new_exprs = self._update_expr_v2(alias_exprs, trace_expr)
                for new_expr in new_exprs:
                    if new_expr.expr.trace_dir == 'F':
                        new_forward_exprs.append(new_expr)
                    else:
                        tmp_expr = self.update_stack_argument(callsite, new_expr)
                        if tmp_expr is None:
                            new_backward_exprs.append(new_expr)
                        else:
                            new_backward_exprs.append(tmp_expr)

        # TODO load alias info update!!!

        pre_block = list(callsite.predecessors)[0]
        for new_expr in new_backward_exprs:
            # print("Push-to-%x from %x: %s" % (pre_block.addr, callsite.target, new_expr))
            new_expr.expr.ptr_id += callsite.addr
            # if pre_block.addr in new_expr.forward_path:
            #     new_expr.forward_path.remove(pre_block.addr)
        self._push_backward_exprs_to_pre_block(caller_function, callsite, loop, new_backward_exprs, flow_dir)

    def _process_callee_definiton_in_callsite(self, callsite, caller_function, callee_function, loop, flow_dir):
        """
        In backward, process callee parameters definitions and argument pointer alias.
        """
        callee_addr = callee_function.addr
        aptr_exprs = self.collector.datas['Aptr'].get(callee_addr)
        if not aptr_exprs:
            return

        aptr_defs = self._get_aptr_definitions(aptr_exprs)
        aptr_aliases = self._get_aptr_aliases(aptr_exprs)
        # print("%s has aptr-defs: \n%s" % (callsite, aptr_defs))
        # print("%s has aptr-alias: \n%s" % (callsite, aptr_aliases))
        # print("B-update-def-%x" % (callsite.addr))

        if len(aptr_defs):
            self._process_arg_ptr_defs(callsite, caller_function, aptr_defs, loop, flow_dir)

        if len(aptr_aliases):
            self._process_arg_ptr_aliases_backward(callsite, aptr_aliases, flow_dir)

    def _process_arg_ptr_defs(self, callsite, caller_function, aptr_defs, loop, flow_dir):
        """
        In this case, the callee function has definition to the 'arg_ptr + offset'
        """
        new_backward_exprs = []
        killed_exprs = []
        new_aptr_defs = {}

        pre_blocks = list(callsite.predecessors)
        if len(pre_blocks) != 1:
            raise Exception("the callsite %s has more than one pre blocks, do it future!" % (callsite))
        context_block = pre_blocks[0]

        location = CodeLocation(callsite.addr, 0)
        for aptr_def in aptr_defs:
            new_defs = self._update_parameter_with_context(context_block, aptr_def)
            for new_def in new_defs:
                # print("aptr-def: %s new_def %s" % (aptr_def, new_def))
                value_id = new_def.expr.value.args[0].__hash__()
                if value_id not in new_aptr_defs:
                    new_aptr_defs[value_id] = []

                if callsite.is_loop:
                    new_def.expr.active_store_action_in_callsite(location)
                else:
                    new_def.expr.kill_store_action_in_callsite(location)
                new_aptr_defs[value_id].append(new_def)

        for trace_expr in callsite.backward_exprs:
            # print("cs-has: %s" % (trace_expr))
            if callsite.contain_exprs(trace_expr):
                continue

            tmp_exprs = [trace_expr]
            new_exprs = []
            sim_actions = trace_expr.expr.sim_actions

            for i, sim_action in sim_actions.items():
                action_data = sim_action.action_data
                data_id = action_data.args[0].__hash__()
                var_type = sim_action.var_type
                if action_data.op == 'Load' and location not in sim_action.def_locs and sim_action.live and data_id in new_aptr_defs:
                    callee_defs = new_aptr_defs[data_id]
                    new_exprs = self._update_expr_v1(tmp_exprs, action_data, var_type, callee_defs)
                    tmp_exprs = new_exprs

            # print("xax-: %s" % (new_exprs))
            if new_exprs:
                killed_exprs.append(trace_expr)
                new_backward_exprs.extend(new_exprs)

        # print("x: %s" % (new_backward_exprs))
        for kill_expr in killed_exprs:
            callsite.backward_exprs.remove(kill_expr)

        self._push_backward_exprs_to_pre_block(caller_function, callsite, loop, new_backward_exprs, flow_dir)

    def _process_forward_arg_ptr_defs(self, callsite, caller_function, aptr_defs, loop, flow_dir):
        """
        In this case, the callee function has definition to the 'arg_ptr + offset'
        """
        new_backward_exprs = []
        killed_exprs = []
        new_aptr_defs = {}

        pre_blocks = list(callsite.predecessors)
        if len(pre_blocks) != 1:
            raise Exception("the callsite %s has more than one pre blocks, do it future!" % (callsite))
        context_block = pre_blocks[0]

        location = CodeLocation(callsite.addr, 0)
        for aptr_def in aptr_defs:
            # print("aptr-def: %s" % (aptr_def))
            value = aptr_def.expr.value
            if sim_action_len(value) > 2:
                continue

            value_id = value.args[0].__hash__()
            if value_id not in new_aptr_defs:
                new_aptr_defs[value_id] = []

            new_def = aptr_def.deep_copy()
            if callsite.is_loop:
                new_def.expr.active_store_action_in_callsite(location)
            else:
                new_def.expr.kill_store_action_in_callsite(location)
            new_aptr_defs[value_id].append(new_def)

        for trace_expr in callsite.forward_exprs:

            if callsite.contain_exprs(trace_expr):
                continue

            tmp_exprs = [trace_expr]
            new_exprs = []
            sim_actions = trace_expr.expr.sim_actions

            for i, sim_action in sim_actions.items():
                action_data = sim_action.action_data
                data_id = action_data.args[0].__hash__()
                var_type = sim_action.var_type
                if action_data.op == 'Load' and location not in sim_action.def_locs and sim_action.live and data_id in new_aptr_defs:
                    callee_defs = new_aptr_defs[data_id]
                    new_exprs = self._update_expr_v1(tmp_exprs, action_data, var_type, callee_defs)
                    tmp_exprs = new_exprs

            if new_exprs:
                killed_exprs.append(trace_expr)
                new_backward_exprs.extend(new_exprs)

        for kill_expr in killed_exprs:
            callsite.forward_exprs.remove(kill_expr)

        self._push_backward_exprs_to_pre_block(caller_function, callsite, loop, new_backward_exprs, flow_dir)

    def _process_arg_ptr_aliases_backward(self, callsite, aptr_aliases, flow_dir):
        pass

    def _update_expr_v1(self, trace_exprs, sub_ast, sub_type, rep_exprs):
        new_exprs = []
        for trace_expr in trace_exprs:
            for rep_expr in rep_exprs:
                rep_ast = rep_expr.expr.ast
                rep_sim_actions = rep_expr.expr.sim_actions
                if rep_ast.op in ['Load', 'Store']:
                    rep_sim_actions[0].var_type = sub_type
                new_expr = trace_expr.replace(sub_ast, rep_ast, re_sim_actions=rep_sim_actions, rep_type=sub_type)
                new_expr.expr.trace_dir = 'B'
                new_expr.index = 0
                new_exprs.append(new_expr)
                # print("Hello-new: %s" % (new_expr))

        return new_exprs

    def _update_expr_v2(self, alias_exprs, trace_expr):
        """
        Update alias pointer.
        """
        new_exprs = []
        for alias_expr in alias_exprs:
            alias_ast = alias_expr.expr.ast
            value = alias_expr.expr.value
            rep_sim_actions = alias_expr.expr.sim_actions
            sim_types = {}
            for var, sim in alias_expr.expr.sims.items():
                sim_types[var] = sim.var_type
            if alias_ast.op in ['Load', 'Store']:
                rep_sim_actions[0].var_type = 'ptr'
            new_expr = trace_expr.replace(value, alias_ast, rep_info=sim_types, re_sim_actions=rep_sim_actions, rep_type='ptr')
            if alias_expr.expr.is_ret:
                new_expr.expr.trace_dir = 'F'
            else:
                new_expr.expr.trace_dir = 'B'
            new_expr.expr.value = trace_expr.expr.value
            new_expr.expr.base_ptr = alias_expr.expr.base_ptr
            new_expr.index = 0
            new_exprs.append(new_expr)

        return new_exprs

    def _update_parameter_with_context(self, callsite, aptr_expr):
        new_exprs = []
        value = aptr_expr.expr.value
        new_value = value
        live_defs = callsite.live_defs

        context_info = {}
        for arg in value.variables:
            if arg in default_arg_names:
                context_asts = self._find_reg_context(arg, live_defs)
                context_info[arg] = context_asts

        tmp_values = [value]
        new_values = []
        for arg, context_asts in context_info.items():
            arg_ast = BVS(arg)
            new_values = []
            for context_ast in context_asts:
                if arg_ast.size() != context_ast.size():
                    continue
                for tmp_value in tmp_values:
                    new_value = tmp_value.replace(arg_ast, context_ast)
                    new_values.append(new_value)
            tmp_values = new_values[:]

        for new_value in new_values:
            new_expr = aptr_expr.deep_copy()
            new_expr.expr.value = new_value
            new_exprs.append(new_expr)
        return new_exprs

        # for arg in value.variables:
        #     if arg in default_arg_names:
        #         context_asts = self._find_reg_context(arg, live_defs)
        #         if len(context_asts) == 0:
        #             continue
        #         arg_ast = BVS(arg)
        #         for context_ast in context_asts:
        #             new_value = new_value.replace(arg_ast, context_ast)
        #             new_values.append(new_value)

        # new_expr = aptr_expr.deep_copy()
        # new_expr.expr.value = new_value
        # return new_expr

    def _find_reg_context(self, reg, live_defs):
        context_asts = []
        if reg not in live_defs:
            return context_asts

        context_ast = None
        reg_at = live_defs[reg]
        reg_src = reg_at.src_alias if reg_at.src_alias else reg_at.src
        reg_size = reg_at.var_size
        if type(reg_src) is str and 'r' in reg_src:
            context_ast = BVS(reg_src, reg_size)
            context_asts.append(context_ast)

        elif type(reg_src) is str and 't' in reg_src and reg_src in live_defs:
            tmp_at = live_defs[reg_src]
            if tmp_at.action_type == 'wl' and tmp_at.addr_type == 'S' and type(tmp_at.addr_value) is int:
                stack_addr = BVV(tmp_at.addr_value)
                context_ast = claripy.Load(stack_addr, stack_addr.size())
                context_asts.append(context_ast)

        if reg_at.value and reg_at.var_type == 'ptr':
            context_ast = BVV(reg_at.value, reg_size)
            context_asts.append(context_ast)

        return context_asts

    def _get_aptr_definitions(self, aptr_exprs):
        aptr_defs = []
        for aptr_expr in aptr_exprs:
            value = aptr_expr.expr.value
            if value.op == 'Store':
                aptr_defs.append(aptr_expr)
        return aptr_defs

    def _get_aptr_aliases(self, aptr_exprs):
        aptr_aliases = []
        for aptr_expr in aptr_exprs:
            aptr_ast = aptr_expr.expr.ast
            value = aptr_expr.expr.value
            if aptr_ast.op == 'Store' and value.op in ['BVS', 'Load']:
                aptr_aliases.append(aptr_expr)
        return aptr_aliases

    def _process_callsite_context(self, callsite, succ_forward_exprs):
        new_forward_exprs = []
        # print("callsite target: %s" % (callsite.target))
        cs_target = callsite.target
        callsite_contexts = self.collector.datas['Aptr'].get(cs_target) if type(cs_target) is int else None
        # print("callsite contexts: %s" % (callsite_contexts))

        if callsite_contexts is None:
            return []

        # TODO should update callsite's expr from callee?

        current_location = CodeLocation(callsite.addr, 0)
        simple_aliases = {}
        complex_aliases = {}
        for trace_expr in callsite_contexts:
            data, value = trace_expr.expr.ast, trace_expr.expr.value
            if len(trace_expr.expr.sims) == 0: continue
            if value is None or not is_argument(value): continue
            if value.op in ['BVS', 'BVV'] and data.op == 'Store':
                alias_name = value.args[0]
                if alias_name not in simple_aliases:
                    simple_aliases[alias_name] = []
                alias_pair = (value, trace_expr)
                simple_aliases[alias_name].append(alias_pair)

            elif value.op == 'Load' and data.op == 'Store':
                pass

            elif value.op == 'Store' and data.op in ['Load', 'BVV', 'BVS']:
                pass

        if len(simple_aliases):
            # print("simple alias: %s" % (simple_aliases))
            for forward_expr in succ_forward_exprs:
                # print("f-expr: %s" % (forward_expr))
                new_exprs = self._update_expr_with_simple_alias(simple_aliases, forward_expr)
                for new_expr in new_exprs:
                    new_expr.expr.trace_dir = 'F'
                    new_expr.expr.location = current_location
                    new_expr.index = 0
                    new_forward_exprs.append(new_expr)
                # for new_expr in new_exprs:
                #     print("alias get new expr:\n %s\n %s %s" % (new_expr, new_expr.expr.sims, new_expr.expr.sim_actions))
                    # for sim_action in new_expr.expr.sim_actions.values():
                    #     print("%s %s" % (sim_action, sim_action.def_locs))

        return new_forward_exprs

    def _process_callsite_callee_taint_in_forward(self, callsite, caller_function, callee_function, loop, taint_exprs, flow_dir):
        """
        In callsite, we should update callee's taint exprs to callsite.
        """
        new_forward_exprs = []
        new_backward_exprs = []
        code_location = CodeLocation(callsite.addr, 0)
        # print("\n---- %s start update callee taint exprs ----\n" % (callsite))

        for taint_expr in taint_exprs:
            is_update = False
            new_expr = self.update_stack_argument(callsite, taint_expr)
            if new_expr is not None:
                taint_expr = new_expr
                is_update = True

            # print("taint expr: %s %s, is-ret: %s" % (callsite, taint_expr, taint_expr.expr.is_ret))
            # print(" -->%s" % (list(callsite.successors)))

            if not is_update:
                taint_expr = taint_expr.deep_copy()
                taint_expr.expr.source = code_location
                taint_expr.index = 0

            taint_expr.clear_path()

            if taint_expr.expr.is_ret:
                taint_expr.expr.trace_dir = 'F'
                taint_expr.expr.is_ret = False
                taint_expr.expr.active_store_action_in_callsite(code_location)
                new_forward_exprs.append(taint_expr)

            else:
                if callsite.is_loop:
                    taint_expr.expr.active_store_action_in_callsite(code_location)
                else:
                    taint_expr.expr.kill_store_action_in_callsite(code_location)

                new_backward_exprs.append(taint_expr)

                if type(taint_expr.expr.base_ptr) is int:
                    f_expr = taint_expr.make_forward_copy()
                    f_expr.expr.active_store_action_in_callsite(code_location)
                    new_forward_exprs.append(f_expr)

        if len(new_forward_exprs):
            # for new_expr in new_forward_exprs:
            #     new_expr.expr.ptr_id += callsite.addr
            self._update_attribute_in_callsite(callsite, caller_function, callee_function, new_forward_exprs, loop, flow_dir)
            self._push_forward_exprs_to_succ_block(caller_function, callsite, loop, new_forward_exprs, flow_dir)

        if len(new_backward_exprs):
            # for new_expr in new_backward_exprs:
            #     new_expr.expr.ptr_id += callsite.addr
            self._update_attribute_in_callsite(callsite, caller_function, callee_function, new_backward_exprs, loop, flow_dir)
            self._push_backward_exprs_to_pre_block(caller_function, callsite, loop, new_backward_exprs, flow_dir)

    def _update_attribute_in_callsite(self, callsite, caller_function, callee_function, callee_exprs, loop, flow_dir):
        """
        In callsite, update expr's attribute (ptr_id, cons_ids, etc.)
        """
        addr = callsite.addr
        arg_constraints = callee_function.arg_constraints
        # print("up-attribute in %s %s %s" % (callsite, callee_function, arg_constraints))
        if len(arg_constraints):
            location = CodeLocation(addr, 0)
            update_cons_exprs = []
            for arg_cons_expr in arg_constraints:
                find_flag = False
                for trace_expr in callee_exprs:
                    arg_cons_id = arg_cons_expr.expr.alias_id
                    # print("--Test: %s %s %s" % (trace_expr, arg_cons_id, trace_expr.cons_ids))
                    if arg_cons_id in trace_expr.cons_ids:
                        trace_expr.cons_ids.remove(arg_cons_id)
                        new_cons_id = arg_cons_id + location.__hash__()
                        trace_expr.cons_ids.append(new_cons_id)
                        find_flag = True

                if find_flag:
                    update_cons_exprs.append(arg_cons_expr)

            if len(update_cons_exprs):
                new_cons_exprs = []
                for cons_expr in update_cons_exprs:
                    new_cons_expr = cons_expr.deep_copy()
                    new_cons_expr.expr.alias_id += location.__hash__()
                    new_cons_exprs.append(new_cons_expr)
                    # print("push-cons(2): %s %s" % (callsite, new_cons_exprs))
                self._push_backward_exprs_to_pre_block(caller_function, callsite, loop, new_cons_exprs, flow_dir)

        for trace_expr in callee_exprs:
            trace_expr.expr.ptr_id += addr

    def _update_expr_with_simple_alias(self, alias_info, trace_expr):
        """
        Update all trace exprs with alias info.
        """
        new_exprs = []
        sims = trace_expr.expr.sims
        r_syms = [name for name, sim in sims.items() if sim.live]

        update_exprs = [trace_expr]
        while r_syms:
            name = r_syms.pop()
            tmp_exprs = []
            if name in alias_info:
                for old_data, alias_expr in alias_info[name]:
                    for update_expr in update_exprs:
                        new_expr = update_expr.replace(old_data, alias_expr.expr.ast, re_sim_actions=alias_expr.expr.sim_actions)
                        tmp_exprs.append(new_expr)
                        new_exprs.append(new_expr)

            if len(tmp_exprs):
                update_exprs = tmp_exprs

        return new_exprs

    def _update_expr_with_complex_alias(self, alias_info, trace_expr):
        """
        Update expr with complex alias, e.g. Load(rdi + 0x20): Store(rax + 0x10)
        """
        new_exprs = []
        struct_ids = [_id for _id in alias_info.keys()]

        update_exprs = [trace_expr]
        while struct_ids:
            sid = struct_ids.pop()
            tmp_exprs = []
            for old_data, alias_expr in alias_info[sid]:
                for update_expr in update_exprs:
                    new_expr = update_expr.replace(old_data, alias_expr.expr.ast, re_sim_actions=alias_expr.expr.sim_actions)
                    tmp_exprs.append(new_expr)
                    new_exprs.append(new_expr)

            if len(tmp_exprs):
                update_exprs = tmp_exprs

        return new_exprs

    def _process_callee_definiton_in_callsite_bak(self, callsite, succ_forward_exprs, pre_backward_exprs):
        # print("process callee definition.")
        # print("callsite exprs: %s" % (callsite.callsite_exprs))

        new_exprs = []
        arg_ptr_alias = defaultdict(list)
        arg_ptr_definitions = []
        ret_ptr_definitions = []
        should_backward_exprs = []

        for trace_expr in callsite.callsite_exprs:
            # print("%s" % (trace_expr))

            if trace_expr.expr.trace_dir == 'B':
                value = trace_expr.expr.value
                if value is not None and value.op in ['BVS', 'BVV']:
                    alias_name = trace_expr.expr.value.args[0]
                    arg_ptr_alias[alias_name].append(trace_expr)

                if trace_expr.expr.data_type in ['Vptr', 'Fptr', 'Iptr']:
                    should_backward_exprs.append(trace_expr)

                elif trace_expr.expr.data_type == 'Aptr':
                    arg_ptr_definitions.append(trace_expr)

            elif trace_expr.expr.trace_dir == 'F':
                ret_ptr_definitions.append(trace_expr)

        if len(arg_ptr_alias):

            # print("callsite: %s has alias:\n alias- %s" % (callsite, arg_ptr_alias))
            current_location = CodeLocation(callsite.addr, 0)
            forward_new_exprs = self._update_exprs_with_alias(arg_ptr_alias, succ_forward_exprs)
            new_exprs.extend(forward_new_exprs)

            # backward_new_exprs = self._update_exprs_with_alias(arg_ptr_alias, pre_backward_exprs)
            # new_exprs.extend(backward_new_exprs)

            for new_expr in new_exprs:
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.location = current_location
                new_expr.expr.pattern = 'OBF'
                new_expr.expr.update_sims()

                # print("new_expr: %s %s" % (new_expr, new_expr.expr.sims))

        # print("callsite new exprs: %s" % (new_exprs))
        # for e in should_backward_exprs:
        #     print("should backward: %s" % (e))

        # argument_info = self._get_argument_info_from_callee_definition(should_backward_exprs)
        # trace_arguments = self._initialize_trace_argument(callsite, argument_info, trace_dir='B')
        # pre_backward_exprs.extend(trace_arguments)

        pre_backward_exprs.extend(should_backward_exprs)
        pre_backward_exprs.extend(new_exprs)

        # succ_forward_exprs.extend(ret_ptr_definitions)

        # clear the callsite exprs
        callsite.callsite_exprs = []

        # for expr in should_backward_exprs:
        #     callsite.callsite_exprs.remove(expr)

        # for expr in ret_ptr_definitions:
        #     callsite.callsite_exprs.remove(expr)

    def _update_exprs_with_alias(self, arg_ptr_alias, trace_exprs):

        new_exprs = []

        for trace_expr in trace_exprs:

            new_datas = []

            trace_vars = trace_expr.expr.trace_vars
            trace_data = trace_expr.expr.ast
            choose_alias_name = [a for a in arg_ptr_alias if a in trace_vars]

            if len(choose_alias_name) == 0:
                continue

            all_alias_pairs = self._get_all_alias_pairs(choose_alias_name, arg_ptr_alias)

            # print("updata expr %s" % (trace_expr))
            # print("All alias pairs: %s" % (all_alias_pairs))

            for alias_info in all_alias_pairs:
                new_trace_data = trace_data

                # print("alias info: %s" % (alias_info))
                replace_count = 0
                for alias_name, alias_expr in alias_info:
                    arg_ptr = alias_expr.expr.value
                    alias_data = alias_expr.expr.ast
                    new_trace_data = new_trace_data.replace(arg_ptr, alias_data)
                    replace_count += 1

                if replace_count == len(alias_info):
                    new_datas.append(new_trace_data)

                else:
                    l.info("Update expr %s with alias %s error!" % (trace_expr, alias_info))

            # print("Get new datas: %s" % (new_datas))

            for new_data in new_datas:
                new_expr = self._get_new_expr_with_ast(trace_expr, new_data)
                new_expr.get_trace_variable(trace_expr.expr.killed_vars)
                new_exprs.append(new_expr)

        return new_exprs

    def _get_new_expr_with_ast(self, old_expr, new_ast):

        new_expr = old_expr.deep_copy()
        new_expr.expr.ast = new_ast

        return new_expr

    def _get_all_alias_pairs(self, alias_names, arg_ptr_alias):

        all_alias_pairs = []

        if len(alias_names) == 1:
            alias_name = alias_names[0]

            for alias_expr in arg_ptr_alias[alias_name]:
                all_alias_pairs.append([(alias_name, alias_expr)])

            return all_alias_pairs

        all_combinations = self._get_all_combinations(alias_names, arg_ptr_alias)

        for alias_ids, combination_info in all_combinations.items():
            choose_names = [alias_names[i] for i in alias_ids]
            choose_len = len(choose_names)

            for comb_info in combination_info:
                choose_alias_pair = []

                for i in range(choose_len):
                    expr_id = comb_info[i]
                    choose_name = choose_names[i]
                    pair = (choose_name, arg_ptr_alias[choose_name][expr_id])

                    choose_alias_pair.append(pair)

                all_alias_pairs.append(choose_alias_pair)

        return all_alias_pairs

    def _get_all_combinations(self, alias_names, arg_ptr_alias):

        def _combinations(l):
            r = []
            for i in range(1, len(l)+1):
                iter = itertools.combinations(l,i)
                r.append(list(iter))

            return r

        all_combination = {}
        info = {}

        for index, alias_name in enumerate(alias_names):
            info[index] = []
            has_alias_count = len(arg_ptr_alias[alias_name])

            for n in range(has_alias_count):
                info[index].append(n)

        alias_list = info.keys()
        diff_alias = _combinations(alias_list)

        for comb_list in diff_alias:
            for t in comb_list:
                p = [info[i] for i in t]
                r = list(itertools.product(*p))

                all_combination[t] = r

        return all_combination

    def _label_custom_libc_return_value(self, block):

        if block.addr not in custom_block_trace_record:
            custom_block_trace_record.add(block.addr)

    def _active_store_action(self, callsite):
        location = CodeLocation(callsite.addr, 0)
        for trace_expr in callsite.forward_exprs:
            trace_expr.expr.active_store_action_by_loc(location)

    def _kill_load_action(self, callsite):
        location = CodeLocation(callsite.addr, 0)
        for trace_expr in callsite.forward_exprs:
            # print("kill-load-action: %s %s" % (trace_expr, location))
            trace_expr.expr.kill_load_action_by_loc(location)

    def _check_trace_flag(self, function, callsite, loop, flow_dir):
        """
        In libc function callsite, check libc whether generate new expr.
        Then set the function_trace_record or loop.execute_flag
        """
        cycle_nodes = loop.body_nodes if loop is not None else []
        if flow_dir == 'F':
            for pre_block in callsite.predecessors:
                if len(pre_block.backward_exprs):
                    if pre_block not in cycle_nodes:
                        if function.trace_dir == 'F':
                            function_trace_record[callsite.func_addr] |= 0x1
                            # if callsite.func_addr == 0x1200955D4:
                            #     print("Changed in %s, should analyze backward again" % (callsite))
                    else:
                        loop.execute_flag = 0x1

        elif flow_dir == 'B':
            for succ_block in callsite.successors:
                if len(succ_block.forward_exprs):
                    if succ_block not in cycle_nodes:
                        if function.trace_dir == 'B':
                            function_trace_record[callsite.func_addr] |= 0x2
                            # if callsite.func_addr == 0x1200955D4:
                            #     print("Changed in %s, should analyze forward again" % (callsite))

                    else:
                        loop.execute_flag = 0x2

    def _pre_execute_callsite(self, function, callsite, loop=None, flow_dir=None, loop_dir=None):
        """
        In forward analysis, callsite may be generate new exprs from callee.
        Pre_execute the callsite and push callee expr to forward block.
        """
        # print("In %s, process-callsite: %s" % (function, callsite))
        for pre_block in callsite.predecessors:
            # print("pre-block: %s" % (pre_block))
            if len(pre_block.backward_exprs):
                for b_expr in pre_block.backward_exprs:
                    b_expr.backward_path.clear()
                    # print("back-expr: %s %s" % (b_expr, b_expr.backward_path))
                self._block_execute(function, pre_block, loop, 'B', loop_dir=flow_dir)

    def _block_execute(self, function, block, loop=None, flow_dir=None, loop_dir=None):
        """
        :param block: a CFG block
        :param loop: a instance of class Loop
        """
        trace_flag = 0

        # if function.addr == 0x1200955D4:
        print("\nDEBUG-%s%s-%x %s\n" % (flow_dir, flow_dir, block.addr, block))
        # if block.irsb: block.irsb.pp()

        ret_exprs = self.collector.datas['Ret'].get(0x4032a8)

        # if len(block.backward_exprs) == 0 and len(block.forward_exprs) == 0:
        #     return

        block.analyzed_flag = 0x1
        self._remove_current_node_from_path(block, flow_dir)

        if block.irsb is not None:
            trace_flag = self._block_trace2(function, block)

        if block.node_type in ['Call', 'Extern', 'iCall']:
            if self.taint_check and block.icall_flag == 1:
                return
            # print("Callsite %s has type %s" % (block, block.node_type))
            check_forward_ret, check_backward_ret = True, True
            if type(block.target) is str:
                lib_func_name = block.target
                callee_function = self._get_lib_function_by_name(lib_func_name)

                if callee_function is None and lib_func_name in self._sim_procedures:
                    # block.print_trace_expr()
                    proc = self._sim_procedures[lib_func_name]
                    if self.taint_check:
                        check_forward_ret = proc.execute(block, self.proj, 'run', flow_dir='F', purpose=0, caller_function=function)
                    elif self.icall_check:
                        check_forward_ret = proc.execute(block, self.proj, 'run', flow_dir='F', purpose=1, caller_function=function)

                    if flow_dir == 'F':
                        self._pre_execute_callsite(function, block, loop, flow_dir)

                    if self.taint_check and len(block.backward_exprs):
                        check_backward_ret = proc.execute(block, self.proj, 'run', flow_dir='B', caller_function=function)
                    elif self.icall_check and len(block.backward_exprs):
                        check_backward_ret = proc.execute(block, self.proj, 'run', flow_dir='B', purpose=1, caller_function=function)

            else:
                funcea = block.target
                callee_function = self._call_graph._nodes.get(funcea)
                if callee_function is None:
                    l.info("The callee function %x not in call graph!" % (funcea))

            # if callee_function:
            if callee_function and callee_function.flag == 0:
                func_name = callee_function.procedural_name
                # print("callee-name: %s" % (func_name))
                if (len(block.forward_exprs) or
                        (func_name and func_name in self._sim_procedures and self.taint_check) or
                        (len(function.input_global_taints) and function.trace_dir == 'F')):
                    print("Forward-call-0x%x -> %s with function-flag %d" % (block.addr, callee_function, callee_function.flag))
                    check_forward_ret = self._process_callee_function_in_forward(block, function, callee_function, loop, flow_dir)
                    if flow_dir == 'F':
                        self._pre_execute_callsite(function, block, loop, flow_dir)

                if len(block.backward_exprs):
                    print("Backward-call-0x%x -> %s with function-flag %d" % (block.addr, callee_function, callee_function.flag))
                    parameter_ptrs = predict_parameter_pointer_in_backward(block)
                    print("Predict-paras-%x: %s" % (block.addr, parameter_ptrs))
                    check_backward_ret = self._process_callee_function_in_backward(block, function, callee_function, parameter_ptrs, loop, flow_dir)

                if self.taint_check:
                    self._ida_object.cg.push_global_info(callee_function)

            # print("Is-check-ret(F): %s" % (check_forward_ret))
            if check_forward_ret:
                # Check the return default register in block.forward_exprs
                self._check_return_register_redefine(block, callee_function=callee_function)

            if check_backward_ret:
                self._check_return_register_update(block)

            self._active_store_action(block)
            self._kill_load_action(block)

            self._check_trace_flag(function, block, loop, flow_dir)

        pre_backward_exprs = self._get_predecessor_block_backward_exprs(function, block)
        succ_forward_exprs = self._get_successor_block_forward_exprs(function, block)

        # DEBUG
        # print("pushB-%x: %s" % (block.addr, pre_backward_exprs))
        # print("pushF-%x: %s" % (block.addr, succ_forward_exprs))

        if self.taint_check and block.node_type in ['Call', 'Extern', 'iCall']:
            self._check_taint_flag(block, succ_forward_exprs, 'F')
            self._check_taint_flag(block, pre_backward_exprs, 'B')

        # clear block's all trace exprs after execute the block.
        # print("DEBUG-clear-exprs: %s" % (block))
        block.backward_exprs = []
        block.forward_exprs = []

        flow_dir = loop_dir if loop_dir else flow_dir
        self._push_backward_exprs_to_pre_block(function, block, loop, pre_backward_exprs, flow_dir)

        self._push_forward_exprs_to_succ_block(function, block, loop, succ_forward_exprs, flow_dir)

        # # clear block's all trace exprs after execute the block.
        # # print("DEBUG-clear-exprs: %s" % (block))
        # block.backward_exprs = []
        # block.forward_exprs = []

        if (len(function.input_global_taints) and len(block.global_defs)):
            # print("Kill-global-def: %s" % (block))
            function.kill_input_global_taints(block)

        # print("\nDEBUG: expr_path (after):")
        # for expr in pre_backward_exprs:
        #     print("\nB: %s" % (expr))
        #     print("b_path %s" % (expr.backward_path))
        #     print("f_path %s" % (expr.forward_path))
        #     print("")

        # for expr in succ_forward_exprs:
        #     print("\nF: %s" % (expr))
        #     print("b_path %s" % (expr.backward_path))
        #     print("f_path %s" % (expr.forward_path))
        #     print("")

    def _check_taint_flag(self, callsite, trace_exprs, flow_dir):

        for trace_expr in trace_exprs:
            # print("Check-taint-flag:\n %s" % (trace_expr))
            # print("source: %s, callsite: %s" % (trace_expr.expr.source, callsite))
            if (trace_expr.expr.data_type == 'Tdata' and
                    (trace_expr.expr.source.block_addr == callsite.addr or
                     (trace_expr.expr.taint_live and trace_expr.expr.taint_live == callsite.addr))):
                if flow_dir == 'F':
                    trace_expr.expr.flag |= 0x100

                else:
                    trace_expr.expr.flag &= 0xfeff

    def _block_trace2(self, function, block):

        flag = 0
        forward_exprs = block.forward_exprs[:]
        backward_exprs = block.backward_exprs[:]

        if len(block.global_addrs) and len(function.input_global_taints):
            function.get_global_taints(block, forward_exprs)

        for trace_expr in backward_exprs:
            if ('F' in trace_expr.expr.pattern and trace_expr.could_forward()):
                self._accurate_dataflow.update_put_alias_in_backward(block, trace_expr)

        count = 1
        while True:
            if len(forward_exprs):
                # print("call forward_data_trace -->%x(%d)" % (block.addr, count))
                alive_exprs = self._accurate_dataflow.forward_data_trace2(block, forward_exprs)
                backward_exprs.extend(alive_exprs)
                if len(alive_exprs):
                    flag = 0x1

            forward_exprs = []
            if len(backward_exprs):
                # print("call backward_data_trace -->%x(%d)" % (block.addr, count))
                forward_exprs = self._accurate_dataflow.backward_data_trace2(block, backward_exprs)
                if len(forward_exprs):
                    flag = 0x2

            backward_exprs = []
            if len(forward_exprs) == 0:
                break
            count += 1

        return flag

    def _push_forward_exprs_to_succ_block(self, function, block, loop, succ_forward_exprs, flow_dir):

        if len(succ_forward_exprs) == 0:
            return

        cycle_nodes = loop.body_nodes if loop is not None else []
        # if loop is not None:
        #     loop_start_nodes = loop.start_nodes
        #     cycle_nodes = loop.body_nodes
        #     # print("xxLoop: %s %s" % (loop, loop_start_nodes))
        # else:
        #     loop_start_nodes = None
        #     cycle_nodes = []

        # if loop_start_nodes:
        #     for succ_block in block.successors:
        #         if succ_block in loop_start_nodes:
        #             into_loop

        trace_ptrs = set()

        for trace_expr in succ_forward_exprs:
            trace_expr.index = 0
            trace_expr.clear_sim_index()

            # for var, sim in trace_expr.expr.sims.items():
            #     if sim.var_type == 'ptr' and type(var) is str:
            #         trace_ptrs.add(var)

            self._check_taint_constraint_in_block_v1(block, trace_expr)
            if self.taint_check:
                self.collector.collect_weaks(block, trace_expr)

        for succ_block in block.successors:

            branch_falg = self._solver_branch_guard(block, succ_block, function)
            # print("Branch-flag: %s %s" % (succ_block, branch_falg))
            if not branch_falg:
                continue

            # print("push-succ-%x %s" % (succ_block.addr, succ_block.forward_exprs))
            self._merge_block_exprs(block, succ_block, succ_forward_exprs, cycle_nodes, flow_dir='F')
            # print("push-succ-(after)%x %s" % (succ_block.addr, succ_block.forward_exprs))

            # if flow_dir == 'B' and len(succ_block.forward_exprs):
            if len(succ_block.forward_exprs):
                if succ_block not in cycle_nodes:
                    if function.trace_dir == 'B':
                        # if block.func_addr == 0x1200955D4:
                        #     print("Changed in %s, should analyze forward again" % (block))
                        #     for ee in succ_block.forward_exprs:
                        #         print("  -->fexpr %s %s %s" % (succ_block, ee, ee.expr.source))
                        function_trace_record[block.func_addr] |= 2

                elif flow_dir == 'B':
                    loop.execute_flag = 0x2
                    # print("In loop, %s has new exprs (B)" % (succ_block))

    def _push_backward_exprs_to_pre_block(self, function, block, loop, pre_backward_exprs, flow_dir):

        if len(pre_backward_exprs) == 0:
            return

        cycle_nodes = loop.body_nodes if loop is not None else []

        for expr in pre_backward_exprs:
            expr.clear_sim_index()

        for pre_block in block.predecessors:
            # print("ui%s %s" % (pre_block, pre_backward_exprs))
            if pre_block.irsb is not None:
                stmts_len = len(pre_block.irsb.statements)

            else:
                stmts_len = 0

            for expr in pre_backward_exprs:
                expr.index = stmts_len

            # pre_block.print_backward_exprs(debug_type=0)
            self._merge_block_exprs(pre_block, block, pre_backward_exprs, cycle_nodes, flow_dir='B')
            # pre_block.print_backward_exprs(debug_type=1)

            if len(pre_block.backward_exprs):
                if pre_block not in cycle_nodes:
                    if function.trace_dir == 'F':
                        # if block.func_addr == 0x1200955D4:
                        #     print("Changed in %s, should analyze backward again" % (block))
                        #     for ee in pre_block.backward_exprs:
                        #         print("  -->bexpr %s %s %s" % (pre_block, ee, ee.expr.source))
                        function_trace_record[block.func_addr] |= 1

                elif flow_dir == 'F':
                    loop.execute_flag = 0x1
                    # print("In loop, %s has new exprs (F)" % (pre_block))

    # def _push_expr_to_succ_block(self, block, trace_expr):

    # def _push_expr_to_succ_block(self, block, trace_expr):

    def _check_special_libc(self, block):
        for pre_block in block.predecessors:
            if pre_block.node_type == 'Extern' and type(pre_block.target) is str:
                libc_name = pre_block.target
                if libc_name in ['inet_pton', 'gethostbyname2', 'gethostbyname']:
                    return 1
                elif libc_name in ['strcmp']:
                    return 2
        return 0

    def _solver_special_constriant(self, src, dst, cons_type, trace_expr):
        """
        Solver the special libc function with return constraint (e.g. strcmp).
        """
        def get_guard_var(src, dst):
            src_addr = src.addr
            if src_addr in dst.guard:
                jmp_guard = dst.guard[src_addr]
                # print("solver-special-cons: %s -> %s, with %s" % (src, dst, jmp_guard))
                if (len(jmp_guard.args) == 2 and
                        jmp_guard.args[0].op == 'BVS' and
                        jmp_guard.args[1].op == 'BVV'):
                    guard_var = jmp_guard.args[0]
                    return jmp_guard.op, jmp_guard.args[1].args[0]
            return None, None

        guard_flag = None
        guard_op, guard_con = get_guard_var(src, dst)
        if cons_type == 1:
            if guard_op == '__eq__' and guard_con == 0:
                guard_flag = 1
            elif guard_op == '__ne__' and guard_con == 0:
                guard_flag = 2
        elif cons_type == 2:
            if guard_op == '__eq__' and guard_con == 0:
                guard_flag = 3
            elif guard_op == '__ne__' and guard_con == 0:
                guard_flag = 4

        cons_flag = None
        constraints = trace_expr.constraints
        # print("Call-special: %s %s %s %s, -guard_flag: %s %s" % (src, cons_type, guard_op, guard_con, guard_flag, constraints))
        for cons in constraints:
            if cons == 'C1':
                # print("Check-special-cons: %s %s" % (trace_expr, cons))
                if guard_flag == 1:
                    cons_flag = 1
                    # print("Remove-cons: %s %s" % (trace_expr, cons))
                elif guard_flag == 2:
                    cons_flag = 2
                    # print("Add-cons: %s %s" % (trace_expr, cons))

            elif cons == 'C2':
                # print("Check-special-cons: %s %s" % (trace_expr, cons))
                if guard_flag == 3:
                    cons_flag = 3
                    # print("Add-cons: %s %s" % (trace_expr, cons))
                elif guard_flag == 4:
                    cons_flag = 4
                    # print("Remove-cons: %s %s" % (trace_expr, cons))
        if cons_flag == 1:
            trace_expr.remove_constraint('C1')
            # new_expr = trace_expr.deep_copy()
            # new_expr.expr.constraints.remove('C1')
        elif cons_flag == 2:
            trace_expr.add_constraint('S1')
            trace_expr.constraints.remove('C1')
            # new_expr = trace_expr.deep_copy()
            # new_expr.expr.constraints.remove('C1')
            # new_expr.expr.constraints.append('S1')
        # else:
        #     new_expr = trace_expr

        # return new_expr

    def _solver_branch_guard(self, src, dst, function):
        """
        Solver the branch guard and judge the succ-block's satisfiable.
        """
        src_addr = src.addr
        if src_addr in dst.guard:
            jmp_guard = dst.guard[src_addr]
            if jmp_guard.args[0] in [True, False]:
                return jmp_guard.args[0]
            # print(jmp_guard, jmp_guard.args[0])
            var, con = jmp_guard.args
            if var.op == 'BVS' and con.op == 'BVV':
                # print("ppp-> %s %s" % (var, con))
                if function:
                    value = function.get_var_concret_value(src, var.args[0])
                    if value is not None:
                        # print("Get-value: %s" % (value))
                        new_guard = jmp_guard.replace(var, BVV(value))
                        return new_guard.is_true()
        return True

    def _add_taint_constraint(self, block_addr, cons_info, trace_expr):
        cons_type, cons_op, cons_var = cons_info
        # if cons_type == 3 and len(str(cons_var)) > 10 and type(cons_var) is int:
        #     trace_expr.cons_ids = trace_expr.cons_ids.copy()
        #     if cons_var not in trace_expr.cons_ids:
        #         trace_expr.cons_ids.append(cons_var)
        #         # print("add-cons-5: %s %s" % (trace_expr, cons_var))
        if cons_type == 5 and cons_op in ['eq', 'le', 'lt']:
            if cons_var != 0xffffffff:
                trace_expr.add_constraint(cons_var)
                # print("add-cons-5: %x -> %s (%s) %s" % (block_addr, trace_expr, id(trace_expr), cons_var))
        elif cons_type == 4 and cons_op in ['eq', 'le', 'lt']:
            if cons_var != 0xffffffff:
                trace_expr.add_constraint(cons_var)
                # print("add-cons-4: %x -> %s %s" % (block_addr, trace_expr, cons_var))
        elif cons_type == 2 and cons_op == 'eq' and cons_var == 0:
            # trace_expr.add_constraint('S')
            return 1
        elif cons_type == 1 and cons_op != 'eq' and cons_var == 0:
            # trace_expr.add_constraint('S')
            return 1
        elif cons_type == 6 and cons_op == 'eq' and cons_var == 0 and trace_expr.expr.var_type != 'ptr':
            return 1
        elif cons_type == 0 and cons_op == 'eq' and cons_var == 0 and trace_expr.expr.ast.op == 'BVS':
            return 1
        return 0

    def _check_taint_constraint_in_block_v1(self, block, trace_expr):
        ptr_id = trace_expr.expr.ptr_id
        # print("ptr-id: %x taint-cons: %s" % (ptr_id, block.taint_constraints))
        if self.taint_check and ptr_id in block.taint_constraints:
            guard_info = block.taint_constraints[ptr_id]
            for succ_target, cons_info in guard_info.items():
                if succ_target != 0:
                    continue
                self._add_taint_constraint(succ_target, cons_info, trace_expr)

    def _check_taint_constraint_in_block_v2(self, src, dst, trace_expr):
        kill_tainted = False
        ptr_id = trace_expr.expr.ptr_id
        # print("\nxpx: %s -> %s %s" % (src, dst, trace_expr))
        # print("block-cons: %s" % (src.taint_constraints))
        if self.taint_check and ptr_id in src.taint_constraints:
            guard_info = src.taint_constraints[ptr_id]
            # print("ptr-id %x has guard %s" % (ptr_id, str(guard_info)))
            for succ_target, cons_info in guard_info.items():
                if succ_target == dst.addr:
                    cons_flag = self._add_taint_constraint(succ_target, cons_info, trace_expr)
                    # print("Fcons: %s %s" % (dst, str(cons_info)))
                    if cons_flag == 1:
                        kill_tainted = True
        return kill_tainted

    def _check_constraint_in_block_v1(self, src, dst, cons_expr):
        """
        In backward, check the constraint expr with cmp.
        """
        sims = cons_expr.expr.sims
        cons_ast = cons_expr.expr.ast
        # print("Check-cons(B) %s -> %s %s" %(dst, src, cons_expr))
        if src.addr in dst.guard:
            cons_guard = dst.guard[src.addr]
            # print("cons-guard %s" % (cons_guard))
            for var in cons_guard.variables:
                if var in sims:
                    guard_info = self._accurate_dataflow.get_var_guard_info(var, cons_guard)
                    if guard_info is None:
                        continue
                    # print("Get-guard-info: %s" % str(guard_info))
                    guard_op, opnd0, opnd1 = guard_info
                    if guard_op in ['le', 'eq']:
                        opnd1_value = get_value(src, opnd1) if type(opnd1) is str else opnd1
                        opnd1_ast = BVV(opnd1_value) if type(opnd1_value) is int else BVS(opnd1)
                    elif guard_op == 'lg':
                        opnd1_value = get_value(src, opnd1) if type(opnd1) is str else opnd1
                        opnd1_ast = BVV(opnd1_value) if type(opnd1_value) is int else BVS(opnd1)
                        opnd1_ast = opnd1_ast - 1
                    else:
                        continue
                    new_expr = cons_expr.replace(cons_ast, opnd1_ast, rep_type=cons_expr.expr.var_type)
                    new_expr.expr.trace_dir = cons_expr.expr.trace_dir
                    new_expr.index = cons_expr.index
                    # print("New-cons-expr - %s %s" % (opnd1_ast, new_expr))
                    return new_expr

    def _merge_constraints(self, trace_expr, other_expr, src=None, dst=None):
        """
        Merge different path for traced exprs.
        """
        other_constraints = other_expr.constraints
        if src and dst:
            self._check_taint_constraint_in_block_v2(src, dst, trace_expr)

        if ((len(other_constraints) == 0 or
                (len(other_constraints) == 1 and other_constraints[0] == 0)) and
                'Y' not in trace_expr.constraints):
            # self.constraints.append('Y')
            pass
            # print("add-cons-1: %s %s" % (self, 'Y'))
        else:
            for c in other_constraints:
                if c not in trace_expr.constraints:
                    trace_expr.constraints.append(c)
                    # print("merge-cons: %s -> %s %s %s" % (src, dst, self, c))

        for cons_id in other_expr.cons_ids:
            if cons_id not in trace_expr.cons_ids:
                trace_expr.cons_ids.append(cons_id)

    def _whether_call_into_callee(self, callsite, s_block, forward_exprs):
        forward_to_callee = []
        start_code_location = CodeLocation(s_block.addr, 0)
        for expr in forward_exprs:
            if expr.expr.pattern == 'BF':
                is_arg_def = is_argument_define(expr.expr.ast)
                if is_arg_def:
                    new_expr = expr.deep_copy()
                    new_expr.index = 0
                    new_expr.expr.source = start_code_location
                    forward_to_callee.append(new_expr)

        if len(forward_to_callee) == 0:
            return

        s_block.forward_exprs = forward_to_callee

        # print("Call into function %s" % (s_block))
        function = self._cfg.functions_manager[s_block.addr]
        self.execute_function(function, callsite=callsite, collect_ret=False)

    def _remove_current_node_from_path(self, block, flow_dir):
        if flow_dir == 'F':
            for expr in block.forward_exprs:
                if expr.expr.source.block_addr == block.addr:
                    expr.backward_path = set()

                if block.addr in expr.backward_path:
                    expr.backward_path.remove(block.addr)

            for expr in block.backward_exprs:
                if block.addr in expr.backward_path:
                    expr.backward_path.remove(block.addr)

        if flow_dir == 'B':
            for expr in block.forward_exprs:
                if block.addr in expr.forward_path:
                    # print("remove addr %x from forward_path" % (block.addr))
                    expr.forward_path.remove(block.addr)

            for expr in block.backward_exprs:
                if expr.expr.source.block_addr == block.addr:
                    expr.forward_path = set()

                if block.addr in expr.forward_path:
                    # print("remove addr %x from forward_path" % (block.addr))
                    expr.forward_path.remove(block.addr)

    def _check_return_register_redefine(self, block, callee_function=None):
        """
        Check the block.forward_exprs in callsite, if the return reg is killed.
        We assume all the callsite has a returned value, not consider the non-returned function.
        """
        killed_exprs = []
        new_exprs = []
        ret_reg = 'r%d' % (self._binary_parser.ret_offset)

        for trace_expr in block.forward_exprs:
            if ret_reg in trace_expr.expr.sims:
                # print("kill-expr: %s" % (trace_expr))
                last_code_location = CodeLocation(block.addr, 0)
                new_expr = self._accurate_dataflow.kill_expr_by_reg_redefine(ret_reg, last_code_location, trace_expr)
                if new_expr is not None:
                    new_exprs.append(new_expr)

                killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            block.forward_exprs.remove(kill_expr)

        for new_expr in new_exprs:
            block.forward_exprs.append(new_expr)

    def _get_successor_block_forward_exprs(self, function, block):
        """
        Each block irsb analysis done, will generate new forward exprs for successor block.
        :param
        """
        succ_forward_exprs = []
        killed_exprs = []
        live_backward_stores = self._accurate_dataflow.backward_store_records
        ret_reg = 'r%d' % (self._binary_parser.ret_offset)

        if len(block.forward_exprs) > 30:
            # print("Should merge and filter exprs. %s %s" % (function, block))
            if self.icall_check:
                block.forward_exprs = merge_simlilar_exprs_v3(block.forward_exprs)
            elif self.taint_check:
                block.forward_exprs = merge_simlilar_exprs_v1(block.forward_exprs)

        for expr in block.forward_exprs:
            if expr.contain_symbol('t'):
                continue

            data_type = expr.expr.data_type
            trace_ast = expr.expr.ast

            if len(expr.expr.sims) == 0 and get_symbols(expr.expr.ast):
                if block in function.cfg.exit_blocks:
                    block.collect_completed_exprs(expr)

            elif data_type in ['Vptr', 'Ret'] and sim_action_len(trace_ast) > 3:
                continue

            elif data_type == 'Tdata' and is_filter_v4(trace_ast):
                # print("Should-filter-Tdata %s" % (expr))
                continue

            else:
                if block in function.cfg.exit_blocks:
                    block.collect_completed_exprs(expr)
                succ_forward_exprs.append(expr)

        return succ_forward_exprs

    def _get_predecessor_block_backward_exprs(self, function, block):
        """
        Each block irsb analysis done, will generate new backward exprs for predecessor block.
        :param
        """
        funcea = block.func_addr
        pre_backward_exprs = []
        fiter_syms = ['o', '_']

        if len(block.backward_exprs) > 30:
            # print("Should merge and filter exprs. %s %s" % (function, block))
            if self.icall_check:
                block.backward_exprs = merge_simlilar_exprs_v3(block.backward_exprs)
            elif self.taint_check:
                block.backward_exprs = merge_simlilar_exprs_v1(block.backward_exprs)

        for expr in block.backward_exprs:
            # print("  --> %s has done expr %s" % (block, expr))
            if expr.contain_symbol('t') and expr.expr.flag & 2 != 0x2:
                continue

            data_type, pattern = expr.expr.data_type, expr.expr.pattern
            trace_ast, value = expr.expr.ast, expr.expr.value

            if data_type == 'sDef':
                continue

            elif data_type == 'Cons' and expr.expr.ast.op == 'BVV':
                # print("Get-concrete-cons: %s" % (expr))
                alias_id = expr.expr.alias_id
                if expr not in self.collector.constraints[alias_id]:
                    self.collector.constraints[alias_id].append(expr)
                continue

            elif (data_type == 'Cons' and
                    (expr.contain_special_symbols(fiter_syms) or not is_simple_cons(trace_ast))):
                # print("Filter-cons: %s" % (expr))
                # data_collector = self.collector.datas[data_type][block.func_addr]
                # if expr not in data_collector:
                #     data_collector.append(expr)
                continue

            elif (data_type == 'Aptr' and sim_action_len(trace_ast)+sim_action_len(value) > 10):
                continue

            elif (data_type in ['Ret', 'Rptr'] and
                  (type(expr.expr.base_ptr) is str and sim_action_len(trace_ast) > 4)):
                continue

            elif data_type == 'Tdata' and is_filter_v4(trace_ast):
                # print("Should-filter-Tdata %s" % (expr))
                continue

            symbols = get_symbols(expr.expr.ast)

            if len(symbols) == 1 and 'ptr' in symbols[0] and data_type != 'Aptr':
                data_collector = self.collector.datas[data_type][block.func_addr]
                if expr not in data_collector:
                    data_collector.append(expr)
                    # print("7 %s" % (expr))
                # print("xpx-> %s %s" % (expr.expr.taint_loc, expr.expr.memory_size))
                if self.taint_check and expr.expr.taint_loc and expr.expr.memory_size:
                    self.collector.collect_heap_weaks(expr)
                    # print("oooo-> %s %s" % (block, expr))

            # elif len(symbols) == 1 and '_' in symbols[0]:
            elif expr.contain_special_symbol('_'):
                if data_type not in ['Aptr', 'Ret', 'Rptr', 'Tdata']:
                    data_collector = self.collector.datas[data_type][block.func_addr]
                    if expr not in data_collector:
                        data_collector.append(expr)
                        # print("8 %s" % (expr))

            else:
                if block.addr == function.start_node.addr:
                    block.collect_completed_exprs(expr)
                if data_type == 'Ret' and expr.expr.ast.concrete:
                    data_collector = self.collector.datas[data_type][block.func_addr]
                    if expr not in data_collector:
                        data_collector.append(expr)
                        # print("9 %s" % (expr))

                else:
                    pre_backward_exprs.append(expr)

        return pre_backward_exprs

    def _merge_block_exprs(self, src, dst, new_exprs, cycle_nodes, flow_dir=None):
        move_exprs = []
        merge_exprs = []
        if flow_dir == 'F':
            old_exprs = dst.forward_exprs
        elif flow_dir == 'B':
            old_exprs = src.backward_exprs
        else:
            old_exprs = []

        in_loop = False
        if src in cycle_nodes and dst in cycle_nodes:
            in_loop = True

        for new_expr in new_exprs:
            # print("\nmerge-new_expr: %s" % (new_expr))
            # print("%s -> %s merge expr %s (%s)" % (src, dst, new_expr, new_expr.expr.sims))
            # print("forward path %s" % (new_expr.forward_path))

            if flow_dir == 'F' and dst.is_loop:
                iid = new_expr.iid
                if iid in dst.traced_iids:
                    # print("--iid (skip): %s %s %s" % (dst, new_expr, new_expr.iid))
                    continue

            if not in_loop and flow_dir == 'F' and len(new_expr.backward_path):
                if dst.addr not in new_expr.backward_path:
                    # print("Skip-one: %s %s" % (in_loop, new_expr.backward_path))
                    continue

            elif not in_loop and flow_dir == 'B' and len(new_expr.forward_path):
                # print("src: %s, %s has %s" % (src.addr, new_expr, new_expr.forward_path))
                if src.addr not in new_expr.forward_path:
                    # print("Skip-two: %s %s" % (in_loop, new_expr.forward_path))
                    continue

            skip = False
            for old_expr in old_exprs:
                # print("old-%s, new-%s" % (old_expr.ast_iid, new_expr.ast_iid))
                # if (new_expr == old_expr and
                #         len(new_expr.expr.sims) == len(old_expr.expr.sims) and
                #         new_expr.expr.pattern == old_expr.expr.pattern and
                #         new_expr.expr.ptr_id == old_expr.expr.ptr_id):
                if ((self.taint_check and new_expr.ast_iid == old_expr.ast_iid) or (self.icall_check and new_expr == old_expr)):
                    skip = True
                    # print("OMG: has old-expr: %s" % (new_expr))
                    old_expr.merge_state(new_expr)
                    # old_expr.expr.flag |= new_expr.expr.flag
                    old_expr.expr.taint_loc = new_expr.expr.taint_loc
                    self._merge_constraints(old_expr, new_expr, src, dst)
                    if not in_loop:
                        self._merge_path(src, dst, new_expr, old_expr, flow_dir)
                    break

            if not skip and new_expr not in merge_exprs:
                merge_exprs.append(new_expr)

        # for expr in merge_exprs:
        #     print("%s -> %s merge expr %s" % (src, dst, expr))

        if flow_dir == 'F':
            for expr in merge_exprs:
                branch_falg = self._judge_branch_guard(src, dst, expr)
                # print("f-branch-flag: %s" % (branch_falg))
                if not branch_falg:
                    continue
                expr_copy = expr.copy()

                # if libc_flag:
                #     self._solver_special_constriant(src, dst, libc_flag, expr_copy)
                    # expr_copy = self._solver_special_constriant(src, dst, libc_flag, expr_copy)

                kill_flag = self._check_taint_constraint_in_block_v2(src, dst, expr_copy)
                # print("kill-tainted %s -> %s %s" % (src, dst, kill_flag))
                if kill_flag:
                    continue

                if not in_loop:
                    expr_copy.forward_path.add(src.addr)
                old_exprs.append(expr_copy)

                if dst.is_loop and (self.icall_check or self.taint_check and expr_copy.expr.flag & 0x100):
                    dst.traced_iids.add(expr_copy.iid)
                    # print("add-iids: %s -> %s %s %s" % (src, dst, expr_copy, expr_copy.iid))
                # print("")
                # print("HHH(F)- %s -> %s %s %s" % (src, dst, expr_copy, expr_copy.cons_ids))
                # print(" expr-guard: %s, block-guard: %s" % (expr_copy.guard, dst.guard))
                # print(" constraints: %s" % (expr_copy.constraints))
                expr_copy.guard = None

        elif flow_dir == 'B':
            for expr in merge_exprs:
                expr_copy = expr.copy()
                if not in_loop:
                    expr_copy.backward_path.add(dst.addr)
                expr_copy.guard = None

                if expr_copy.expr.data_type == 'Cons':
                    new_cons_expr = self._check_constraint_in_block_v1(src, dst, expr_copy)
                    if new_cons_expr is not None:
                        old_exprs.append(new_cons_expr)

                # print("HHH(B)- %s -> %s %s %x" % (src, dst, expr_copy, expr_copy.expr.flag))
                old_exprs.append(expr_copy)

            if src.is_loop and self.icall_check:
                self._accurate_dataflow.set_trace_expr_constraint_in_backward(src, dst, merge_exprs)

    def _judge_branch_guard(self, src, dst, trace_expr):
        """
        In branch, some trace expr has constraint and we only push expr to ture block.
        """
        if trace_expr.guard is None:
            return True

        expr_guard = trace_expr.guard
        if src.addr in dst.guard:
            jmp_guard = dst.guard[src.addr]
            print("  %s has %s jmp-guard %s" % (trace_expr, expr_guard, jmp_guard))
            if expr_guard.op != jmp_guard.op and expr_guard.args[0].__hash__() == jmp_guard.args[0].__hash__():
                return False
        return True

    def _merge_path(self, src, dst, new_expr, old_expr, flow_dir):
        if flow_dir == 'F':
            old_expr.forward_path.add(src.addr)
            for addr in new_expr.forward_path:
                old_expr.forward_path.add(addr)
            # print("merge-path: \n old_expr: %s\n new_expr: %s\n old_fpath: %s\n new_fpath: %s\n" % (old_expr, new_expr, old_expr.forward_path, new_expr.forward_path))

        elif flow_dir == 'B':
            old_expr.backward_path.add(dst.addr)
            for addr in new_expr.backward_path:
                old_expr.backward_path.add(addr)

    def _is_expr_live(self, expr):
        """
        Check the expr whether live in forward.
        """
        trace_sims = expr.expr.sims
        sim_actions = expr.expr.sim_actions
        sim_lives = [sim.live for sim in trace_sims.values() if sim.live]
        action_lives = [action.live for action in sim_actions.values() if action.live]
        # print(sim_lives, action_lives)

        if len(sim_lives) and len(action_lives):
            return True
        return False

    def _get_block_stack_pointer_tmp(self, block):
        irsb = block.irsb
        if block.sp_tmp_offset is not None:
            return

        # TODO: How to use the stack size?
        if block.addr == block.func_addr:
            sp_tmp, stack_size = self._binary_parser.get_stack_size_and_tmp(irsb)
        else:
            sp_tmp = self._binary_parser.get_esp_tmp(irsb)

        block.sp_tmp_offset = sp_tmp

    def _check_return_register_update(self, callsite):
        """
        Only update with symbol ret value.
        """
        new_exprs = []
        killed_exprs = []

        callee_addr = callsite.target
        ret_ast = self._symbol_ret_value(callsite, callee_addr)

        for trace_expr in callsite.backward_exprs:
            if not trace_expr.contain_symbol(self.ret_name):
                continue

            ret_sim = trace_expr.expr.sims[self.ret_name]
            ret_type = ret_sim.var_type
            new_expr = trace_expr.replace(self.ret_name, ret_ast, rep_type=ret_type)
            new_expr.expr.trace_dir = 'B'
            new_expr.index = 0
            new_exprs.append(new_expr)
            killed_exprs.append(trace_expr)

        for kill_expr in killed_exprs:
            callsite.backward_exprs.remove(kill_expr)

        callsite.backward_exprs.extend(new_exprs)

    def _update_return(self, trace_expr, ret_exprs):
        """
        update trace_expr with return exprs.
        """
        new_exprs = []
        ret_sim = trace_expr.expr.sims[self.ret_name]
        ret_type = ret_sim.var_type
        # print("update-ret: %s, with ret-type: %s" % (trace_expr, ret_type))

        # if len(ret_exprs) > 18:
        #     debug

        for ret_expr in ret_exprs:
            # print("ret-expr: %s" % (ret_expr))

            if type(ret_expr) is RecursiveExpr:
                reset_sim_action_type(ret_expr, ret_type)
                new_expr = trace_expr.replace_with_recurisve_expr(self.ret_name, ret_expr, var_type=ret_type)
                new_expr.constraints = ret_expr.constraints.copy()

            elif type(ret_expr) is TraceExpr:
                reset_sim_action_type(ret_expr, ret_type)
                ret_ast = ret_expr.expr.ast
                if ret_type and ret_type == 'ptr' and ret_ast.op == 'BVV' and ret_ast.args[0] <= 1024:
                    continue

                new_expr = trace_expr.replace(self.ret_name, ret_ast, re_sim_actions=ret_expr.expr.sim_actions)
                new_expr.constraints = ret_expr.constraints.copy()

            else:
                new_expr = trace_expr.replace(self.ret_name, ret_expr)

            if new_expr not in new_exprs:
                new_expr.expr.trace_dir = 'B'
                new_expr.index = 0
                new_exprs.append(new_expr)

        return new_exprs

    def _update_ret_variable(self, callsite, callee_function):
        """
        If a expr has ret register (e.g. rax), update the expr with true ret value.
        :param callsite: a block which has a call will return value to ret register.
        :param callee_function: the callee function which return value.
        """
        print("Update-ret in %s -> %s" % (callsite, callee_function))
        killed_exprs = []
        new_backward_exprs = []
        get_ret_flag = False

        ret_exprs = []
        for trace_expr in callsite.backward_exprs:
            # print("xxx-has: %s %s" % (trace_expr, trace_expr.iid))
            if not trace_expr.contain_symbol(self.ret_name):
                continue

            tmp_exprs = []
            should_updates = []
            ret_type = trace_expr.expr.sims[self.ret_name].var_type
            # print("ret-type: %s" % (ret_type))

            if not get_ret_flag:
                if ret_type and ret_type != 'ptr':
                    ret_ast = BVS("o%d" % (next(symbolic_count)))
                    # print("unsym-data(3): %s %s" % (callsite, ret_ast))
                    ret_exprs.append(ret_ast)

                else:
                    ret_exprs = self.get_function_ret_expr(callsite, callee_function, ret_type)
                    # print("Get-ret: %s %s" % (callsite, ret_exprs))
                get_ret_flag = True

                if self.icall_check:
                    ret_syms = self._use_symbol_replace_real_ret_value(callsite, callee_function.addr, 1)
                    ret_exprs = ret_exprs + ret_syms

                elif len(ret_exprs) == 0:
                    ret_exprs = self._use_symbol_replace_real_ret_value(callsite, callee_function.addr)

            new_exprs = self._update_return(trace_expr, ret_exprs)
            new_backward_exprs.extend(new_exprs)

            # tmp_exprs = self._update_ret_def(pre_block, callee_addr, expr)

            # for tmp_expr in tmp_exprs:
            #     if not tmp_expr.contain_symbol(ret_name):
            #         if tmp_expr not in new_exprs: new_exprs.append(tmp_expr)
            #     else:
            #         should_updates.append(tmp_expr)

            # if len(tmp_exprs) == 0:
            #     should_updates.append(expr)

            killed_exprs.append(trace_expr)
            # print("kill-expr: %s %s" % (trace_expr, trace_expr.iid))

        for kill_expr in killed_exprs:
            if kill_expr in callsite.backward_exprs:
                callsite.backward_exprs.remove(kill_expr)

        for new_expr in new_backward_exprs:
            callsite.backward_exprs.append(new_expr)
            # print("Get new ret exprs:\n  %s" % (new_expr))

    def _update_ret_def(self, callsite, callee_addr, trace_expr):
        """
        update expr use the ret def, e.g. store(ret + 0x10)
        """
        # print("update_ret_def: %s %x %s" % (callsite, callee_addr, trace_expr))
        ret_def_exprs = self.collector.datas['Ret'].get(callee_addr)
        # print("ret-def: %s" % (ret_def_exprs))

        complex_aliases = {}
        trace_actions = {}
        for sim_action in trace_expr.expr.sim_actions.values():
            action_data = sim_action.action_data
            if action_data is not None and action_data.op == 'Load':
                struct_id = calculate_ast_struct_id(action_data)
                trace_actions[struct_id] = action_data

        for ret_def in ret_def_exprs:
            value = ret_def.expr.value
            if value.op == 'Store':
                struct_id = calculate_ast_struct_id(value)
                if struct_id in trace_actions:
                    if struct_id not in complex_aliases:
                        complex_aliases[struct_id] = []
                    alias_pair = (trace_actions[struct_id], ret_def)
                    complex_aliases[struct_id].append(alias_pair)

        # print("complex_aliases: %s" % (complex_aliases))
        if len(complex_aliases) == 0:
            return []

        new_exprs = self._update_expr_with_complex_alias(complex_aliases, trace_expr)
        # print('ret new-exprs: %s' % (new_exprs))
        return new_exprs

    def _get_heap_ret(self, callsite_addr):
        ret_sym = '%x_ptr' % (callsite_addr)

        ret_ast = claripy.BVS(ret_sym, self._binary_parser.arch_bits, explicit_name=True)

        return [ret_ast]


    def _get_VLTVerifyVtablePointerDebug_ret(self):
        # l.info("VLTVerifyVtablePointerDebug ret: %s" % (ret_name))
        ret_name = self._binary_parser.argument_vars[1]

        ret_ast = claripy.BVS(ret_name, self._binary_parser.arch_bits, explicit_name=True)

        return [ret_ast]

    def _replace_with_recurisve_expr(self, expr, replace_expr):
        count = 0
        _position = None
        if type(subvariable) is str:
            subvariable = claripy.BVS(subvariable, self._binary_parser.arch_bits, explicit_name=True)

        base = replace_expr.base
        new_expr = expr.expr.replace(subvariable, replace_expr.expr.ast)
        new_sim_data = RecursiveExpr(new_expr)
        for child_ast in new_expr.ast.recursive_children_asts:
            count += 1
            if child_ast.__hash__() == base.__hash__():
                _position = count
                break

        if _position:
            new_sim_data.position = _position
        else:
            l.info("Not find base position in new expr %s" % (new_sim_data))
        new_sim_data.offset = replace_expr.offset
        new_sim_data.base = base
        return new_sim_data

    def _symbol_ret_value(self, callsite, callee_addr):
        callsite_addr = callsite.addr
        if type(callee_addr) is str:
            symbol_name = '%x_%s' % (callsite_addr, callee_addr)

        else:
            symbol_name = '%x_%x' % (callsite_addr, callee_addr)

        ret_ast = BVS(symbol_name)
        return ret_ast

    def _use_symbol_replace_real_ret_value(self, callsite, callee_addr, flag=0):
        """
        While the callee is not in call graph, use symbol to replace the returned value.
        """
        callsite_addr = callsite.addr
        s1 = '%x_' % (callsite_addr) if flag == 0 else 'ret_'
        if type(callee_addr) is str:
            symbol_name = s1 + '%s' % (callee_addr)
        else:
            symbol_name = s1 + '%x' % (callee_addr)

        ret_ast = claripy.BVS(symbol_name, self._binary_parser.arch_bits, explicit_name=True)

        return [ret_ast]

    def _forward_process_loop(self, function, start_block, loop, analyzed_blocks):
        """
        Processing each node in the cycle.
        :param loop: a instance of calss Loop.
        """

        if loop.analyzed_times > MAX_LOOPS:
            # print("W-Loop-f %s execed %d" % (loop, MAX_LOOPS))
            return

        loop_sequence = loop.body_nodes

        for count in range(F_MAX_LOOPS):
            # print("DEBUG-loop-time(F): %s %d (%d), loop-flag: %d" % (loop, loop.analyzed_times, count, loop.execute_flag))
            for block in loop_sequence:

                analyzed_blocks.add(block)

                # print("\n+++--> Forward loop analyze block %s" % (block))
                # print("backward expr %s\nforward expr %s" % (block.backward_exprs, block.forward_exprs))

                self._block_execute(function, block, loop=loop, flow_dir='F')

            for block in loop_sequence:
                block.analyzed_flag = 0x0

            loop.analyzed_times += 1

        for block in loop_sequence:
            # print("DEBUG-clear-expr(loop-F) %s" % (block))
            block.forward_exprs.clear()

        # print("Floop-done! %d" % (loop.execute_flag))
        if loop.execute_flag == 0x1:
            self._backward_process_loop(function, start_block, loop, analyzed_blocks)
            loop.execute_flag = 0

    def _backward_process_loop(self, function, start_block, loop, analyzed_blocks):
        """
        Processing each node in the cycle.
        :param loop: a intance of calss Loop
        """
        if loop.analyzed_times > MAX_LOOPS:
            print("W-Loop-b %s execed %d" % (loop, MAX_LOOPS))
            return

        # print("DEBUG: process loop:\n%s" % (loop))
        # for loop_node in loop.body_nodes:
        #     print("loop node: %s" % (loop_node))

        loop_sequence = loop.body_nodes
        loop_len = len(loop_sequence)

        for count in range(B_MAX_LOOPS):
            # print("DEBUG-loop-time(B): %s %d (%d)" % (loop, loop.analyzed_times, count))
            for i in range(loop_len-1, -1, -1):

                block = loop_sequence[i]

                # print("\n+++--> Backward loop analyze block %s" % (block))
                # print("backward expr %s\nforward expr %s" % (block.backward_exprs, block.forward_exprs))

                analyzed_blocks.add(block)

                self._block_execute(function, block, loop=loop, flow_dir='B')

            loop.analyzed_times += 1

        for block in loop_sequence:
            # print("DEBUG-clear-expr(loop-B) %s" % (block))
            block.backward_exprs.clear()

        if loop.execute_flag == 0x2:
            self._forward_process_loop(function, start_block, loop, analyzed_blocks)
            loop.execute_flag = 0

    def _pre_process_loop_to_summary(self, function, loop):
        loop_sequence = loop.body_nodes
        for block in loop_sequence:

            if block.irsb and len(block.actions) == 0:
                actions = block.actions
                code_locations = block.code_locations
                self._binary_parser.execute_block_irsb(block, actions, code_locations)

        self._binary_parser._backward_find_inc_variable_in_loop(function, loop)

    def _pre_check_loop_variables(self, loop, trace_exprs):
        done_exprs = []
        todo_exprs = []
        remove_exprs = []
        for expr in trace_exprs:
            if expr.expr.loop:
                done_exprs.append(expr)
            else:
                todo_exprs.append(expr)

        new_exprs_info = self._summary_variable_in_loop(loop.inc_variables, todo_exprs, remove_exprs)
        if new_exprs_info:
            # print("in loop, get new exprs %s" % (new_exprs_info))
            for r_expr in remove_exprs:
                trace_exprs.remove(r_expr)

            self._solve_varialbe_in_loop(loop, new_exprs_info, trace_exprs)

    def _check_loop_definition(self, loop, blocks, function_cfg, flow_dir):
        """
        Process the store and load instructions in loop, and give a summary of
        the varialbes in the loop.
        :param blocks: a list of block, which would be the out block or in block of the loop.
        :param flow_dir: lable doing forward or backward data flow analysis.
        """
        # print("\nDEBUG loop (%s)" % (flow_dir))
        # for bb in blocks:
        #     print("loop out block %s" % (bb))
        #     for expr in bb.forward_exprs:
        #         print("forward: %s %s" % (expr, expr.expr.location))
        #     for expr in bb.backward_exprs:
        #         print("backward: %s %s" % (expr, expr.expr.location))

        for block in blocks:
            if flow_dir == 'F':
                exprs = block.forward_exprs
            elif flow_dir == 'B':
                exprs = block.backward_exprs
            else:
                exprs = []
                l.debug("flow_dir cannot be None.")

            # for expr in exprs:
            #     print("LOOP test %s" % (expr))

            if len(loop.inc_variables):
                self._pre_check_loop_variables(loop, exprs)

            l.debug("A loop's out or in block %s(%s)" % (block, block.is_loop))
            # print("A loop's out or in block %s(%s)" % (block, block.is_loop))
            loop_exprs = defaultdict(list)
            for expr in exprs:
                _id = (expr.expr.alias_id, expr.expr.location)

                # print("function %x, expr location %s" % (function_cfg.addr, expr.expr.location))
                expr_loc_addr = expr.expr.location.block_addr
                loc_node = function_cfg._nodes.get(expr_loc_addr)
                if loc_node is None:
                    continue

                if loc_node.is_loop:
                    loop_exprs[_id].append(expr)

            # DEBUG
            # for _id, alias_exprs in loop_exprs.items():
            #     for e in alias_exprs:
            #         print("expr id: ", _id)
            #         print("##GET loop alias %s %s %s %d" % (block, e, e.expr.location, e.index))

            inc_variables = {}
            for _id, alias_exprs in loop_exprs.items():
                if len(alias_exprs) >= 2:
                    inc_vars = self._calculate_increment_in_exprs(block, alias_exprs)
                    for _hash, info in inc_vars.items():
                        if _hash not in inc_variables:
                            inc_variables[_hash] = info

            if len(inc_variables):
                for _hash, info in inc_variables.items():
                    if _hash not in loop.inc_variables:
                        loop.inc_variables[_hash] = info

            # print("loop inc variables: %s" % (inc_variables))

            remove_exprs = []
            new_exprs_info = self._summary_variable_in_loop(inc_variables, exprs, remove_exprs)
            if new_exprs_info:
                # print("in loop, get new exprs %s" % (new_exprs_info))
                self._solve_varialbe_in_loop(loop, new_exprs_info, exprs)
                for r_expr in remove_exprs:
                    exprs.remove(r_expr)

            for _id, alias_exprs in loop_exprs.items():
                if len(alias_exprs) >= 2:
                    recur_info = self._extract_recurisive_in_expr(block, alias_exprs)
                    if recur_info is not None:
                        self._solve_recurisive_in_loop(recur_info, exprs)

            # for _id, alias_exprs in loop_exprs.items():
            #     if len(alias_exprs) >= 2:
            #         for e in alias_exprs:
            #             print("expr id: ", _id)
            #             print("##GET loop alias %s %s %s %d" % (block, e, e.expr.location, e.index))

            #         inc_variables = self._calculate_increment_in_exprs(block, alias_exprs)
            #         if len(inc_variables):
            #             loop.inc_variables.extend(inc_variables)

            #         remove_exprs = []
            #         new_exprs_info = self._summary_variable_in_loop(inc_variables, exprs, remove_exprs)
            #         if new_exprs_info:
            #             print("in loop, get new exprs %s" % (new_exprs_info))
            #             self._solve_varialbe_in_loop(loop, new_exprs_info, exprs)
            #             for r_expr in remove_exprs:
            #                 exprs.remove(r_expr)

            #         else:
            #             recur_info = self._extract_recurisive_in_expr(block, alias_exprs)
            #             if recur_info is not None:
            #                 self._solve_recurisive_in_loop(recur_info, exprs)

    def _solve_recurisive_in_loop(self, recurisive_info, exprs):
        recur_data, base, offset = recurisive_info
        # print("recurisive info %s %s %s" % (recur_data, base, offset))
        symbols = get_symbols(base)
        if len(symbols) != 1:
            l.info("The recurisive data %s has more than one symbols." % (base))
            return

        alias_exprs_dict = defaultdict(dict)
        recur_var = symbols[0]
        for expr in exprs:
            expr_len = len(str(expr))
            alias_exprs_dict[expr.expr.alias_id][expr_len] = expr

        for alias_exprs in alias_exprs_dict.values():
            sort_exprs = sorted(alias_exprs.items(), key=lambda item: item[0])
            # print("sorted exprs: %s" % (sort_exprs))
            remove_exprs = []
            for expr_len, s_expr in sort_exprs:
                if recur_var in s_expr.expr.trace_vars:
                    remove_exprs.append(s_expr)

            if len(remove_exprs):
                c_expr = remove_exprs[0]
                position = 0
                count = 0
                for child_ast in c_expr.expr.ast.recursive_children_asts:
                    count += 1
                    if child_ast.__hash__() == base.__hash__():
                        position = count
                        break

                if position == 0:
                    l.info("Not find base %s in expr %s" % (base, c_expr))
                    return

                recursive_expr = RecursiveExpr(c_expr.expr.copy(),
                                               index=c_expr.index,
                                               base=base,
                                               offset=offset,
                                               position=position)
                # print("New recursive expr %s (%s)" % (recursive_expr, type(recursive_expr)))
                # print("remove exprs %s" % (remove_exprs))
                for r_expr in remove_exprs:
                    exprs.remove(r_expr)
                exprs.append(recursive_expr)

    def _extract_recurisive_in_expr(self, block, alias_exprs):
        elements = {}
        expr_info = {}
        for expr in alias_exprs:
            # print("\nExpression %s" % (expr))
            data = expr.expr.ast
            deref_asts = [d for d in data.recursive_children_asts if d.op == 'Load']
            # print(deref_asts)
            elements[expr] = deref_asts
            element_len = len(deref_asts)
            if element_len not in expr_info:
                expr_info[element_len] = []
            expr_info[element_len].append(expr)

        if len(expr_info) <= 1:
            l.info("No recurisive exprs in loop!")
            return

        sort_exprs = sorted(expr_info.items(), key=lambda item: item[0])
        # print("Sorted exprs: %s" % (sort_exprs))

        for element_len, exprs in sort_exprs:
            if len(exprs) >= 2:
                l.info("There are two or more exprs not recurisive, do it in future!")
                return

        for i in range(1, len(sort_exprs)):
            gap = sort_exprs[i][0] - sort_exprs[i-1][0]
            if gap != 1:
                l.info("The gap %d false in exprs in loop, do it future!" % (gap))
                return

        recurisive_data = {}
        last_expr = sort_exprs[-1][1][0]
        # print("Last expr %s" % (last_expr))
        for deref_ast in elements[last_expr]:
            _, base_offset = extract_base_and_offset(deref_ast)
            base, offset = base_offset
            if base is None or offset is None:
                continue
            # print(deref_ast, base, offset)
            offset_hash = offset.__hash__()
            if offset.__hash__() not in recurisive_data:
                recurisive_data[offset_hash] = []
            recurisive_data[offset_hash].append((deref_ast, base, offset))

        base_offset_list = [b for b in recurisive_data.values() if len(b) >= 2]
        if len(base_offset_list) != 1:
            l.info("The recurisive exprs %s are complex, do it in future!" % (alias_exprs))
            return

        base_ofssets = base_offset_list[0]
        for ast_data, base, offset in base_ofssets:
            # print("Get recurisive data %s, base %s, offset %s" % (ast_data, base, offset))
            if base.op in ['BVS']:
                return (ast_data, base, offset)

    def _solve_varialbe_in_loop(self, loop, summary_expr_info, trace_exprs):
        self._get_constraint_in_loop(loop)
        concrete_cons = self._extract_constant_in_loop_constraints(loop)
        # concrete_cons = {}

        loop_new_exprs = []
        for new_expr, (inc_variable, inc_offset) in summary_expr_info.items():
            i_value = None
            if inc_variable.variables in concrete_cons:
                threshold_value = concrete_cons[inc_variable.variables]
                # print(threshold_value, inc_offset)
                if inc_offset.concrete:
                    i_value = threshold_value / inc_offset
            if i_value is not None:
                sym_i = claripy.BVS('i', self._binary_parser.arch_bits, explicit_name=True)
                zero = claripy.BVV(0, self._binary_parser.arch_bits)
                i_con = self._binary_parser.state.solver.eval_one(i_value)
                old_ast = new_expr.expr.ast
                for i in range(i_con):
                    loop_value = claripy.BVV(i, self._binary_parser.arch_bits)
                    new_ast = old_ast.replace(sym_i, loop_value)
                    new_ast = new_ast.replace(inc_variable, zero)
                    copy_expr = new_expr.deep_copy()
                    copy_expr.expr.trace_vars = set()
                    copy_expr.expr.ast = new_ast
                    copy_expr.get_trace_variable(new_expr.expr.killed_vars)
                    self._binary_parser.simplify_expr(copy_expr)
                    loop_new_exprs.append(copy_expr)

        if len(loop_new_exprs):
            trace_exprs.extend(loop_new_exprs)
        else:
            for new_expr in summary_expr_info.keys():
                trace_exprs.append(new_expr)

    def _summary_variable_in_loop(self, inc_variables, trace_exprs, remove_exprs):
        # print("summarize the expr: %s" % (trace_exprs))
        new_exprs_info = {}
        inc_expr_info = {}
        if len(inc_variables) == 0:
            return new_exprs_info

        for expr in trace_exprs:
            expr_with_incvar = set()
            for _hash, inc_info in inc_variables.items():
                inc_variable, inc_offset = inc_info
                symbols = get_symbols(inc_variable)
                if len(symbols) != 1:
                    l.info("The inc variable %s has zero or more than one symbol" % (inc_variable))
                    continue
                    # return new_exprs_info

                inc_symbol = symbols[0]
                if inc_symbol in expr.expr.ast.variables:
                    expr_with_incvar.add(_hash)

            if len(expr_with_incvar):
                _key = tuple(expr_with_incvar)
                if _key not in inc_expr_info:
                    inc_expr_info[_key] = []
                inc_expr_info[_key].append(expr)

        if len(inc_expr_info) == 0:
            return {}

        for inc_var_hashs, inc_exprs in inc_expr_info.items():
            remove_exprs_info = defaultdict(list)
            summ_variables = []

            remove_exprs.extend(inc_exprs)

            if len(inc_var_hashs) >= 2:
                l.info("the expr %s has two or more inc variables, do it future." % (inc_exprs))
                continue

            for _hash in inc_var_hashs:
                inc_variable, inc_offset = inc_variables[_hash]
                inc_symbol = inc_variable.args[0]
                i = claripy.BVS('i', inc_offset.size(), explicit_name=True)
                summ_variable = inc_variable + inc_offset * i
                summ_variables.append(summ_variable)

            expr_len_info = []
            for expr in inc_exprs:
                leaf_asts = [e for e in expr.expr.ast.recursive_leaf_asts]
                expr_len = len(leaf_asts)
                expr_len_info.append((expr_len, expr))

            sort_exprs = sorted(expr_len_info, key=lambda item: item[0])

            for _len, expr in sort_exprs:
                ast = expr.expr.ast
                index = 0
                ast_vars = ast.variables
                for child_ast in ast.recursive_children_asts:
                    # print child_ast
                    if child_ast.op in self._binary_parser.add_ops:
                        if len(child_ast.variables) == 1 and inc_symbol in child_ast.variables:
                            arg_0 = child_ast.args[0]
                            arg_1 = child_ast.args[1]
                            if arg_0.__hash__() == inc_offset.__hash__():
                                if arg_1.op in self._binary_parser.add_ops:
                                    _id = (index, ast_vars)
                                    remove_exprs_info[_id].append((child_ast, expr))
                                    break

                                elif arg_1.op == inc_variable.op and arg_1.__hash__() == inc_variable.__hash__():
                                    _id = (index, ast_vars)
                                    remove_exprs_info[_id].append((child_ast, expr))
                                    break

                            if arg_1.__hash__() == inc_offset.__hash__():
                                if arg_0.op in self._binary_parser.add_ops:
                                    _id = (index, ast_vars)
                                    remove_exprs_info[_id].append((child_ast, expr))
                                    break

                                elif arg_0.op == inc_variable.op and arg_0.__hash__() == inc_variable.__hash__():
                                    _id = (index, ast_vars)
                                    remove_exprs_info[_id].append((child_ast, expr))
                                    break

                    elif child_ast.op == inc_variable.op and child_ast.__hash__() == inc_variable.__hash__():
                        _id = (index, ast_vars)
                        remove_exprs_info[_id].append((child_ast, expr))
                        break

                    index += 1

            # print(remove_exprs_info)
            for _id, expr_info in remove_exprs_info.items():
                child_ast, c_epxr = expr_info[0]
                # print("remove expr %s containt %s" % (c_epxr, child_ast))
                # print(c_epxr.expr.location)
                new_expr = c_epxr.deep_copy()
                new_ast = c_epxr.expr.ast.replace(child_ast, summ_variable)
                new_expr.expr.ast = new_ast
                new_expr.expr.loop = True
                # print("new expr %s, trace vars %s" % (new_expr, new_expr.expr.trace_vars))
                # print(new_expr.expr.location)
                self._binary_parser.simplify_expr(new_expr)
                new_exprs_info[new_expr] = (inc_variable, inc_offset)

        return new_exprs_info


        # for inc_info in inc_variables.values():
        #     inc_variable, inc_offset = inc_info
        #     symbols = get_symbols(inc_variable)
        #     if len(symbols) != 1:
        #         l.info("The inc variable %s has zero or more than one symbol" % (inc_variable))
        #         return new_exprs_info

        #     inc_symbol = symbols[0]
        #     for expr in trace_exprs:
        #         if inc_symbol in expr.expr.ast.variables:
        #             remove_exprs.append(expr)

        # if len(remove_exprs) == 0:
        #     return {}

        # remove_exprs_info = defaultdict(list)
        # i = claripy.BVS('i', inc_offset.size(), explicit_name=True)
        # summ_variable = inc_variable + inc_offset * i

        # expr_len_info = []
        # for expr in remove_exprs:
        #     leaf_asts = [e for e in expr.expr.ast.recursive_leaf_asts]
        #     expr_len = len(leaf_asts)
        #     expr_len_info.append((expr_len, expr))

        # sort_exprs = sorted(expr_len_info, key=lambda item: item[0])

        # for _len, expr in sort_exprs:
        #     ast = expr.expr.ast
        #     index = 0
        #     ast_vars = ast.variables
        #     # child_asts = [a for a in ast.recursive_children_asts]
        #     for child_ast in ast.recursive_children_asts:
        #         print child_ast
        #         if child_ast.op in self._binary_parser.add_ops:
        #             if len(child_ast.variables) == 1 and inc_symbol in child_ast.variables:
        #                 _id = (index, ast_vars)
        #                 remove_exprs_info[_id].append((child_ast, expr))
        #                 break

        #         elif child_ast.op in ['BVS']:
        #             if inc_symbol in child_ast.variables:
        #                 _id = (index, ast_vars)
        #                 remove_exprs_info[_id].append((child_ast, expr))
        #                 break

        #         index += 1

        # # print(remove_exprs_info)
        # for _id, expr_info in remove_exprs_info.items():
        #     child_ast, c_epxr = expr_info[0]
        #     print("remove expr %s containt %s" % (c_epxr, child_ast))
        #     new_expr = c_epxr.deep_copy()
        #     new_ast = c_epxr.expr.ast.replace(child_ast, summ_variable)
        #     new_expr.expr.ast = new_ast
        #     new_expr.expr.loop = True
        #     print("new expr %s, trace vars %s" % (new_expr, new_expr.expr.trace_vars))
        #     self._binary_parser.simplify_expr(new_expr)
        #     new_exprs_info[new_expr] = (inc_variable, inc_offset)

        # # for r_expr in remove_exprs:
        # #     trace_exprs.remove(r_expr)

        # return new_exprs_info

    def _calculate_increment_in_exprs(self, block, exprs):
        """
        calulate the increment between two exprs in a loop.
        """
        # print("Doing summary for %s" % (exprs))
        inc_variables = {}
        expr_elements = {}
        sort_exprs = {}
        expr_len_info = {}

        for expr in exprs:
            # l.info("expr: %s" % (expr))
            child_with_add = []
            for child_ast in expr.expr.ast.recursive_children_asts:
                if child_ast.op in self._binary_parser.add_ops:
                    child_with_add.append(child_ast)

            child_len = len(child_with_add)
            expr_elements[expr] = child_with_add
            if child_len not in expr_len_info:
                expr_len_info[child_len] = []
            expr_len_info[child_len].append(expr)

        sort_exprs = sorted(expr_len_info.items(), key=lambda item: item[0])
        # print("sort exprs: %s" % (sort_exprs))

        if len(sort_exprs) < 2:
            return {}

        for _len, s_exprs in sort_exprs:
            if len(s_exprs) >= 2:
                l.info("The maybe some special definition in loop %s! Do it in future!" % (block))
                l.info("exprs: %s" % (s_exprs))
                return {}

        for index, expr_info in enumerate(sort_exprs):
            if index >= 1:
                curr_len = expr_info[0]
                base_len = sort_exprs[index-1][0]
                if curr_len - base_len != 1:
                    l.info("The maybe two more increment in loop! Do it in future!")
                    l.info("exprs: %s" % (sort_exprs))
                    return {}

        # <BV64 (r40 + 0x1) + 0x1>
        c_expr = sort_exprs[-1][1][0]
        b_expr = sort_exprs[-2][1][0]
        # l.info("Last expr %s" % (c_expr))
        cexpr_with_add = expr_elements[c_expr]
        bexpr_with_add = expr_elements[b_expr]
        for child_ast in cexpr_with_add:
            find_inc = False
            if len(child_ast.args) == 2:
                arg_0 = child_ast.args[0]
                arg_1 = child_ast.args[1]

                if arg_0.op in self._binary_parser.add_ops and arg_1.op in ['BVV', 'BVS']:
                    arg0 = arg_0
                    arg1 = arg_1

                elif arg_1.op in self._binary_parser.add_ops and arg_0.op in ['BVV', 'BVS']:
                    arg0 = arg_1
                    arg1 = arg_0

                else:
                    continue

                if len(arg0.args) != 2:
                    continue

                for data in bexpr_with_add:
                    if data.__hash__() == arg0.__hash__():
                        find_inc = True
                        break

                if not find_inc:
                    continue

                if arg0.args[0].__hash__() == arg1.__hash__():
                    inc_variable = arg0.args[1]
                    inc_element = arg1
                    inc_variables[inc_variable.__hash__()] = (inc_variable, inc_element)

                elif arg0.args[1].__hash__() == arg1.__hash__():
                    inc_variable = arg0.args[0]
                    inc_element = arg1
                    inc_variables[inc_variable.__hash__()] = (inc_variable, inc_element)


        # l.info("inc variables: %s" % (inc_variables))
        # print("Find inc variables: %s" % (inc_variables))
        return inc_variables

    def _parse_increment_varialbe(self, expr, inc_elements):
        if len(inc_elements) == 0:
            l.info("There are NULL inc in variable in the loop!")
            return {}
        elif len(inc_elements) >= 2:
            l.info("There are more than one inc in varialbe in the loop!")
            return {}

        inc_variables = {}
        inc_element = inc_elements[0]
        for child_ast in expr.expr.ast.recursive_children_asts:
            if (child_ast.op in self._binary_parser.add_ops and
                    len(child_ast.args) == 2):
                arg_1 = child_ast.args[0]
                arg_2 = child_ast.args[1]

                if arg_1.op == inc_element.op and arg_2.op not in self._binary_parser.add_ops:
                    if arg_1.__hash__() == inc_element.__hash__():
                        inc_variable = arg_2
                        if inc_variable.op == 'BVS':
                            inc_var_hash = inc_variable.__hash__()
                            inc_variables[inc_var_hash] = (inc_variable, inc_element)

                        elif inc_variable.op == 'BVV':
                            l.info("In loop, the inc variable %s is constant, do it future!" % (inc_variable))

                        else:
                            l.info("In loop, the inc variable %s not BVV or BVS, do it future!" % (inc_variable))

                        break

                elif arg_2.op == inc_element.op and arg_1.op not in self._binary_parser.add_ops:
                    if arg_2.__hash__() == inc_element.__hash__():
                        inc_variable = arg_1
                        if inc_variable.op == 'BVS':
                            inc_var_hash = inc_variable.__hash__()
                            inc_variables[inc_var_hash] = (inc_variable, inc_element)

                        elif inc_variable.op == 'BVV':
                            l.info("In loop, the inc variable %s is constant, do it future!" % (inc_variable))

                        else:
                            l.info("In loop, the inc variable %s not BVV or BVS, do it future!" % (inc_variable))

                        break

        return inc_variables

    def _loop_execute_times(self, loop_block_analyzed_times):
        pass

    def _search_test(self, blocks):
        # print("@@@--> vptr addrs: %s" % (self._cfg._vptrs_xref))
        # print("@@@--> icall addrs: %s" % (self._cfg._icalls_xref))

        for block, addrs in self._cfg._vptrs_xref.items():
            irsb = block.irsb
            for addr in addrs:
                index = self._binary_parser.get_save_vptr_index(irsb, addr)
                vptr_expr = self._binary_parser.get_save_vptr_expr(irsb, index)
                # print("@@@--> vtable: %s" % (vptr_expr))

        for block, addr in self._cfg._icalls_xref.items():
            pass

    def test_return_expr(self):
        state = self._init_state
        start_block = self.get_block_node(0x34b3b0)
        call_block = self.get_block_node(0x34b710)
        ret_exprs = self.get_return_expr(state, start_block, call_block)
        # print("ret exprs:%s" % (ret_exprs))

    def inital_state(self, state, function_addr):
        inital_block = self._all_nodes[function_addr]
        irsbs = self.block_sclicing(state, block)
        irsb = irsbs[0]
        for stmt in irsb.statements:
            pass

    def generate_call_graph(self):
        pass

    def get_block_node(self, addr):
        if addr in self._all_nodes:
            return self._all_nodes[addr]
        else:
            raise KeyError

    def parse_cfg_graph(self):
        # bb = self.get_block_node(0x2ebaa0)
        # print(bb)
        # bb_pres = self._cfg.predecessors(bb)
        # print(bb_pres)
        for node in self._cfg.nodes():
            print("Node: %s" % (node))

        for node in self._call_graph.nodes():
            print('Call Graph node: %s' % (node))

    def update_call_context(self, state, track_expr, track_var, load_offset):
        print("Track expr: %s\nTrack var: %s\nLoad_offset: %d\n" % (track_expr, track_var, load_offset))

    def get_exit_block(self, start_block):
        # First method. Use ida plugin to get all exit block of functions.
        # TODO

        # Second method. Travel the cfg of function to get exit block.
        trace_blocks = defaultdict(int)
        exit_blocks = set()
        work_list = [start_block]

        while work_list:
            block = work_list.pop()
            trace_blocks[block.addr] += 1

            if trace_blocks[block.addr] > 1:
                continue

            all_out_edges = self._cfg.graph.out_edges(block, data=True)
            for _, dst, data in all_out_edges:
                if data['jumpkind'] == 'Call':
                    if len(all_out_edges) == 1:
                        exit_blocks.add(block)
                    continue

                work_list.append(dst)

            if len(all_out_edges) == 0:
                exit_blocks.add(block)

        return list(exit_blocks)

    def get_call_successor(self, block):
        all_out_edges = self._cfg.graph.out_edges(block, data=True)
        for _, dst, data in all_out_edges:
            if data['jumpkind'] == 'Call':
                return dst

    def get_return_argument_in_expr(self, irsb, expr):
        """
        Judge if the expr has a return register. For example r16(eax).
        """
        ret_register = 'r%d' % self._proj.arch.ret_offset
        if ret_register in expr.ast.variables and irsb.jumpkind == 'Ijk_Call':
            expr.is_ret = True
            return ret_register
        else:
            return None

    def get_function_ret_expr(self, callsite, function, ret_type):
        """
        Get ret value in function.
        """
        ret_exprs = []
        callsite_addr = callsite.addr
        funcea = function.addr
        if funcea not in self.collector.datas['Ret']:

            self._pre_process_function(function)

            if function.cfg is None:
                l.info("For ret, the child function %x is not in work functions. Should be added in." % (funcea))
                return ret_exprs

            self.backward_trace_ret(function, ret_type=ret_type)

        ret_exprs = self.collector.datas['Ret'].get(funcea)

        if ret_exprs is None:
            l.info("We could't get the return value in function %x." % (funcea))
            return []

        merged_exprs = merge_recurisive_exprs(ret_exprs)
        self.collector.datas['Ret'][funcea] = merged_exprs

        for ret_expr in merged_exprs:
            # print("xxx-ret-expr: %s" % (ret_expr))
            ret_ast = ret_expr.expr.ast
            if ret_ast.op == 'BVS' and 'ptr' in ret_ast.args[0]:
                new_ret_ast = BVS('%x_ptr' % callsite_addr)
                ret_expr.expr.ast = new_ret_ast

        return merged_exprs

    def backward_trace_ret(self, function, ret_type=None):

        self._initialize_ret_register(function, ret_type)
        # print("Execute function %s" % (function))
        self._execute_function(function, collect_ret=True, execute_flag=0x4)

    def _add_backward_tmp_exprs(self, function):
        """
        Add tmp backward expr to source block, and analyze them again.
        """
        cfg = function.cfg
        for tmp_expr in backward_tmp_exprs[function.addr]:
            source = tmp_expr.expr.source
            block_addr = source.block_addr
            source_block = cfg.get_node_by_addr(block_addr)
            source_block.backward_exprs.append(tmp_expr)
            tmp_expr.expr.flag = 2
            # print("debug-add %s to block %s" % (tmp_expr, source_block))

        # clear the backward_tmp_exprs
        backward_tmp_exprs[function.addr].clear()

    def _add_backward_remaining_exprs(self, function):
        """
        Add remaining backward expr to source block, and analyze them again.
        """
        cfg = function.cfg
        for tmp_expr in record_remaining_exprs[function.addr]:
            label_id = (tmp_expr.expr.alias_id, tmp_expr.expr.bw_loc)
            if label_id in record_redef_labels:
                # print("ppp-expr should re-backward: %s" % (tmp_expr))
                source = tmp_expr.expr.source
                block_addr = source.block_addr
                source_block = cfg.get_node_by_addr(block_addr)
                source_block.backward_exprs.append(tmp_expr)
                tmp_expr.expr.flag = 2
            else:
                # print("qqq-expr should recover backward: %s" % (tmp_expr))
                bw_loc = tmp_expr.expr.bw_loc
                original_block = cfg.get_node_by_addr(bw_loc.block_addr)
                original_block.backward_exprs.append(tmp_expr)
            # print("debug-add %s to block %s" % (tmp_expr, source_block))

        # clear the record_remaining_exprs
        record_remaining_exprs[function.addr].clear()

    def _recover_record_backward_exprs(self, block, trace_expr, function_cfg):
        """
        Recover the record backward exprs which breaked off and continue trace them in backward.
        """
        # print("kkkk- %s %s" % (trace_expr, trace_expr.expr.bw_loc))
        # for loc, exprs in record_backward_exprs.items():
        #     print("%s %s" % (loc, exprs))
        bw_loc = trace_expr.expr.bw_loc
        bw_exprs = record_backward_exprs.get(bw_loc)
        if not bw_exprs:
            return

        expr_id = trace_expr.expr.alias_id
        should_rebackward_exprs = [bw_expr for bw_expr in bw_exprs if bw_expr.expr.alias_id == expr_id]
        if len(should_rebackward_exprs) == 0:
            return

        # print("should_rebackward_exprs: %s" % (should_rebackward_exprs))
        record_block = function_cfg.get_node_by_addr(bw_loc.block_addr)
        # print("record_block: %s" % (record_block))
        record_block.backward_exprs.extend(should_rebackward_exprs)
        function_trace_record[block.func_addr] = 1

    def _is_call_source(self, function):
        succ_functions = self._ida_object.cg.graph.successors(function)
        # print("function %s has succ %s" % (function, list(succ_functions)))
        for succ_func in succ_functions:
            if succ_func.addr in self._source_initial.source_functions:
                return True
        return False

    def _get_taint_sources(self, function):
        """
        Get the taint Source from function.
        """
        succ_functions = self._ida_object.cg.graph.successors(function)
        print(succ_functions)
        for succ_func in succ_functions:
            lib_name = succ_func.procedural_name
            # print("Find-source: %s" % (lib_name))
            if lib_name and lib_name in self.taint_source:
                return True
        return False

    def _initialize_taint_source(self, function, sources, data_parser):
        # print("psu-debug: function %s callsite %s" % (function, function.cfg.callees))
        for source in sources:
            caller_sites = function.cfg.callees.get(source.name)
            if caller_sites is None:
                l.info("The function %s didn't call source %s, check it future!" % (function, source))
                continue
            # print("Call-site %s call %s" % (caller_sites, source))

            for callsite in caller_sites:
                data_parser.inital_source_arguments(callsite, source)

    def _pre_process_lib_function(self, function, libary_object):
        # print("pre_process_lib_function: %s" % (function))
        if function.cfg is not None:
            l.info("The function %s has been pre process!" % (function))
            return

        funcea = function.addr
        start_ida_block = libary_object.ida_cfg._ida_blocks.get(funcea-libary_object.base_addr)
        if start_ida_block is None:
            l.info("The function %x not been added in work functions, add it future." % (funcea))
            return

        cfg = FunctionCFG(funcea, libary_object, self.proj)
        start_ida_blocks = [start_ida_block]
        cfg.generate_function_cfg(function, start_ida_blocks)
        function.cfg = cfg
        function.start_node = cfg._nodes[funcea]
        # print("psu-debug: exit-blocks %s" % (function.cfg.exit_blocks))

        # function.cfg.print_cfg()
        # function.cfg.print_cfg_edges()

        self._loop_parser.get_loops_from_graph(function)

        if len(function.cfg.pre_sequence_nodes) == 0:
            pre_sequence_nodes = self._get_pre_sequence_in_function(function)
            function.cfg.pre_sequence_nodes = pre_sequence_nodes
            self._pre_process_function_vex(function)

        # print("psu-debug: pre-sequence %s" % (pre_sequence_nodes))

        # Check the exit blocks, especially some functions has no return and
        # exit with a loop.
        exit_blocks = function.cfg.exit_blocks
        if len(exit_blocks) == 0:
            exit_block = cfg.get_special_exit_block()
            if exit_block is None:
                l.info("We could not find the exit block in function %s" % (function))
                l.info("Then we choose the last block in pre_sequence_nodes as exit block!")
                exit_block = pre_sequence_nodes[-1]
            exit_blocks.add(exit_block)
            # print("psu-debug: get exit-block: %s" % (exit_block))

        self._pre_process_loops(function)

        # graph_parser = GraphMethod(cfg, function.start_node, exit_blocks=exit_blocks)
        # function.graph_parser = graph_parser

    def _set_function_ret_action(function, callsite):
        cfg_graph = function.cfg.graph
        for succ_block in cfg_graph.successors(callsite):
            pass

    def _execute_callsite_node(self, function, callsite):
        """
        Process libc function and infer the arguments and ret type.
        """
        if type(callsite.target) is str:
            lib_func_name = callsite.target
            if lib_func_name in self._sim_procedures:
                proc = self._sim_procedures[lib_func_name]
                proc.execute(callsite, self.proj, "infer_type", caller_function=function)

            else:
                at = Action('p', CodeLocation(callsite.addr, 0), self.ret_name, 'RET', self.arch_bits)
                callsite.live_defs[self.ret_name] = at

        else:
            funcea = callsite.target
            callee_function = self._call_graph._nodes.get(funcea)
            function_name = callee_function.procedural_name if callee_function else None
            if function_name in self._sim_procedures:
                proc = self._sim_procedures[function_name]
                proc.execute(callsite, self.proj, "infer_type", caller_function=function)

            else:
                at = Action('p', CodeLocation(callsite.addr, 0), self.ret_name, 'RET', self.arch_bits)
                callsite.live_defs[self.ret_name] = at

    def _execute_libc_callee_to_infer_type(self, function, callsite):
        """
        Process libc function and infer the arguments and ret type.
        """
        if type(callsite.target) is str:
            lib_func_name = callsite.target
            if lib_func_name in self._sim_procedures:
                proc = self._sim_procedures[lib_func_name]
                proc.execute(callsite, self.proj, "infer_type", caller_function=function)

        else:
            funcea = callsite.target
            callee_function = self._call_graph._nodes.get(funcea)
            function_name = callee_function.procedural_name
            if function_name in self._sim_procedures:
                proc = self._sim_procedures[function_name]
                proc.execute(callsite, self.proj, "infer_type", caller_function=function)

    def update_stack_argument(self, callsite, trace_expr):
        """
        In callsite, update stack argument in trace_expr with parameter.
        """
        is_update = False
        location = CodeLocation(callsite.addr, 0)
        new_expr = trace_expr

        while True:
            tmp_expr = self.update_stack_with_parameter(callsite, location, new_expr)
            if tmp_expr is None:
                break
            else:
                new_expr = tmp_expr
                is_update = True

        return new_expr if is_update else None

    def update_stack_with_parameter(self, callsite, code_location, trace_expr):
        """
        In the callsite, update the stack argument in trace_expr which push from callee.
        """
        sims = trace_expr.expr.sims

        for v, sim in sims.items():
            if type(v) is str and is_stack_symbol(v):
                stack_arg_num = int(v[1:], 10)
                sp_at = callsite.live_defs[self.sp_name]
                sp = BVV(sp_at.value + stack_arg_num * self.arch_bytes)
                stack_arg = claripy.Load(sp, self.arch_bits)
                sim_action = self._accurate_dataflow.create_sim_action(stack_arg, code_location)
                sim_action.var_type = sim.var_type
                re_sim_actions = {0: sim_action}
                # rep_info = {sp.args[0]: 'ptr'}

                new_expr = trace_expr.replace(v, stack_arg, re_sim_actions)
                new_expr.expr.trace_dir = 'B'
                new_expr.expr.source = code_location
                new_expr.index = 0

                return new_expr

    def update_stack_store_action(self, callsite, stack_args, trace_expr, trace_dir):
        """
        """
        sim_actions = trace_expr.expr.sim_actions
        current_sp = callsite.live_defs[self.sp_name].value

        for i, sim_action in sim_actions.items():
            action_data = sim_action.action_data
            if action_data.op == 'Store' and action_data.args[0].op == 'BVV':
                var = action_data.args[0].args[0]
                if type(var) is int and get_mem_permission(var) == 'stack':
                    sarg = self._get_stack_arg_sym(current_sp, var, stack_args)
                    if sarg:
                        # print("sim_action: %s" % (trace_expr.expr.sim_actions))
                        # print("Find sarg: %s" % (sarg))
                        new_expr = trace_expr.replace(action_data, sarg, rep_type='ptr')
                        new_expr.expr.trace_dir = trace_dir
                        # print("sim_action: %s" % (new_expr.expr.sim_actions))
                        return new_expr

    def _get_stack_arg_sym(self, sp, addr, stack_args):
        """
        Judge the stack pointer addr is saved arguments.
        """
        # print('stack args: %s' % (stack_args))
        offset = addr - sp - self.base_stack_offset
        # print("stack-offset: %d" % (offset))
        if (offset % self.arch_bytes) == 0:
            sarg = 's%d' % (offset // self.arch_bytes)
            if sarg in stack_args:
                return sarg

    def _check_args_in_exprs(self, function, trace_exprs):
        """
        If the function has arguments, check the trace_exprs and remove that symobl var not function's arguments.
        """
        remove_exprs = []
        arguments = function.arguments
        for trace_expr in trace_exprs:
            is_removed = False
            for var in trace_expr.expr.ast.variables:
                if ('r' in var or 's' in var) and var not in arguments:
                    is_removed = True

            if is_removed:
                remove_exprs.append(trace_expr)

        for r_expr in remove_exprs:
            trace_exprs.remove(r_expr)

    def _check_expr_cons_ids(self, cons_id, cons_info):
        """
        Check the cons_id whether have a concrete constraint value.
        """
        if cons_id in self.collector.constraints:
            cons_exprs = self.collector.constraints[cons_id]
            for cons_expr in cons_exprs:
                cons_ast = cons_expr.expr.ast
                if cons_ast.op == 'BVV':
                    cons_value = cons_ast.args[0]
                    if cons_value:
                        if cons_id not in cons_info:
                            cons_info[cons_id] = []
                        cons_info[cons_id].append(cons_value)

    def _update_trace_iids(self, callsite, killed_exprs):
        """
        :param callsite:
        :param killed_exprs:
        """
        # print("callsite has traced_iids: %s" % (callsite.traced_iids))
        for kill_expr in killed_exprs:
            kill_ptr_id = kill_expr.expr.ptr_id
            for f_expr in callsite.forward_exprs:
                # print("f_expr: %s %s %s" % (f_expr, f_expr.iid, f_expr.expr.ptr_id))
                if f_expr.expr.ptr_id == kill_ptr_id:
                    kill_iid = f_expr.iid
                    if kill_iid in callsite.traced_iids:
                        callsite.traced_iids.remove(kill_iid)
