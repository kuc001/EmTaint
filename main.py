import os
import sys
import json
import time
import argparse
import logging
import configparser
import angr

from dataflow.parse_binary import BinaryParser
from dataflow.data_trace import FastSearch
from dataflow.ida_process import IDAProcess
from dataflow.fast_data_flow import FastDataFlow
from dataflow.accurate_data_flow import AccurateDataFlow
from dataflow.data_collector import Collector
from dataflow.call_graph import CallGraph
from dataflow.security_check import SecurityCheck

from dataflow.global_config import initialize_global_config, section_regions
from dataflow.ida_plugin.ida_utils import parse_cfg_info

from dataflow.errors import NoIdaCFGFileError

l = logging.getLogger(name="cle.backends.externs")
l.setLevel("ERROR")

# read configuration
CONFIG_FILE = './dataflow.conf'
config = configparser.ConfigParser()
config.read(CONFIG_FILE)
current_path = os.getcwd()
data_path = os.path.join(current_path, config.get('result_config', 'DATA_PATH'))
ida_data_path = os.path.join(current_path, config.get('result_config', 'IDA_DATA_PATH'))
result_save_path = os.path.join(current_path, config.get('result_config', 'RESULT_PATH'))

firmware_info_path = ''


def load_binary(binary):
    proj = angr.Project(binary,
                        default_analysis_mode='symbolic',
                        )
    return proj


def re_construct_cfg(collector, binary_cfg_info_path, binary_block_info_path):
    """
    Re-construct CFG.
    """
    cfg_record = json.load(open(binary_cfg_info_path, 'r'))
    blocks_record = json.load(open(binary_block_info_path, 'r'))

    for funcea, icall_info in collector.icall_targets.items():
        # print("Function: %x" % (funcea))
        funcea_s = '%x' % (funcea)
        func_cfg_record = cfg_record[funcea_s]
        func_block_record = blocks_record[funcea_s]

        # print(func_cfg_record)
        # print(func_block_record)

        call_info = func_cfg_record['call']

        for loc, targets in icall_info.items():
            block_addr_s = '%s' % (loc.block_addr)

            # if block_addr_s in func_block_record:
            #     print("Found, %s %s" % (loc, func_block_record[block_addr_s]))


def save_icall_info(binary_name, collector):
    icall_info_path = os.path.join(firmware_info_path, '%s_icall.json' % (binary_name))
    # print("Icall-save: %s" % (icall_info_path))
    icall_targets = collector.icall_targets
    # print(icall_targets)
    json.dump(icall_targets, open(icall_info_path, 'w'), indent=4)

def save_icall_statistics(ida_object, collector, statistics_path, result_statistics):
    all_icalls = ida_object.all_icalls
    recovered_icall_num = 0
    min_target, max_target = 0xffffffff, 0x0
    icall_targets = set()
    recovered_icalls = set()
    for funcea, icall_info in collector.icall_targets.items():
        for addr, targets in icall_info.items():
            recovered_icalls.add(addr)
            for target in targets:
                icall_targets.add(target)
            targets_len = len(targets)
            if targets_len < min_target:
                min_target = targets_len
            if targets_len > max_target:
                max_target = targets_len
            # print("Resolved icall in %x" % (addr))
        recovered_icall_num += len(icall_info)

    # for icall in all_icalls:
    #     if icall not in recovered_icalls:
    #         print("Non-recovery-icall in %x" % (icall))

    # print("Binary has icalls: %d" % (len(all_icalls)))
    # print("Recovered icalls: %d" % (recovered_icall_num))
    result_statistics['icall']['all_icall'] = len(all_icalls)
    result_statistics['icall']['recovered_icall'] = recovered_icall_num
    result_statistics['icall']['min_tartet_num'] = min_target
    result_statistics['icall']['max_tartet_num'] = max_target
    result_statistics['icall']['add_icall_target'] = len(icall_targets)
    json.dump(result_statistics, open(statistics_path, 'w'), indent=4)


def save_taint_statistics(ida_object, security_engine, statistics_path, result_statistics, resolve_icall):
    # from dataflow.data_trace import function_analyzed_times
    taint_name = 'taint_%d' % (resolve_icall)
    all_func_num = 0
    analyzed_func_num = 0
    analyzed_node_num = 0
    tainted_node_num = 0
    tainted_sinks_num = 0
    call_graph = ida_object.cg

    sinks_info = {}

    for function in call_graph.graph.nodes():
        if function.addr == 0:
            continue
        funcea = function.addr
        all_func_num += 1
        cfg = function.cfg
        if cfg is None:
            continue
        analyzed_func_num += 1
        for node in cfg.graph.nodes():
            if node.node_type in ['Call', 'iCall']:
                continue
            elif node.node_type == 'Extern':
                analyzed_node_num += 1
                if node.is_tainted == 2:
                    tainted_sinks_num += 1
                    # print("tainted-sink: %s" % (node))
                    tainted_node_num += 1
                    sinks_info[node.addr] = (funcea, node.target)
            else:
                analyzed_node_num += 1
                if node.is_tainted == 1:
                    tainted_node_num += 1

    for loc, info in security_engine.weaks_info.items():
        print(" -->0x%x" % (loc), info)
    for loc, (funcea, name) in sinks_info.items():
        print(" -->sink: 0x%x %s in func- %x" % (loc, name, funcea))

    print("All-funcs: %d\nAll-analyzed-funcs: %d\nAll-analyzed-blocks: %d\nAll-tainted-blocks: %d\nAll-tainted-sinks: %d"
          % (all_func_num, analyzed_func_num, analyzed_node_num, tainted_node_num, tainted_sinks_num))
    result_statistics[taint_name]['all_functions'] = all_func_num
    result_statistics[taint_name]['analyzed_functions'] = analyzed_func_num
    result_statistics[taint_name]['all_blocks'] = analyzed_node_num
    result_statistics[taint_name]['tainted_blocks'] = tainted_node_num
    result_statistics[taint_name]['tainted_sinks'] = tainted_sinks_num

    buffer_overflow_num = len(security_engine.weaks)
    buffer_overflow_num += len(security_engine.weaks_length)
    command_exec_num = len(security_engine.weaks_exec)
    print("Weak-copys: %d\nCommand-exec: %d" % (buffer_overflow_num, command_exec_num))
    result_statistics[taint_name]['buffer_overflow_num'] = buffer_overflow_num
    result_statistics[taint_name]['command_exec_num'] = command_exec_num

    vuls_statics = {}
    for s_name in security_engine.sinks:
        vuls_statics[s_name] = 0

    buffer_overflows = {}
    result_statistics[taint_name]['buffer_overflow'] = buffer_overflows
    for addr, stack_offsets in security_engine.weaks.items():
        if addr in sinks_info:
            funcea, name = sinks_info[addr]
        else:
            funcea, name = 0, ''
        info = security_engine.weaks_info.get(addr)
        addr_str = '%x' % (addr)
        buffer_overflows[addr_str] = {'name': name, 'offset': list(stack_offsets), 'info': list(info), 'func': funcea}

        if name in vuls_statics:
            vuls_statics[name] += 1

    command_execs = {}
    for addr in security_engine.weaks_exec:
        if addr in sinks_info:
            funcea, name = sinks_info[addr]
        else:
            funcea, name = 0, ''
        addr_str = '%x' % (addr)
        info = security_engine.weaks_info.get(addr)
        command_execs[addr_str] = {'name': name, 'info': list(info), 'func': funcea}

        if name in vuls_statics:
            vuls_statics[name] += 1

    result_statistics[taint_name]['command_exec'] = command_execs
    tainted_copy_lengths = {}
    for addr in security_engine.weaks_length:
        if addr in sinks_info:
            funcea, name = sinks_info[addr]
        else:
            funcea, name = 0, ''
        addr_str = '%x' % (addr)
        info = security_engine.weaks_info.get(addr)
        tainted_copy_lengths[addr_str] = {'name': name, 'info': list(info), 'func': funcea}

        if name in vuls_statics:
            vuls_statics[name] += 1

    result_statistics[taint_name]['tained_length'] = tainted_copy_lengths

    result_statistics[taint_name]['sink_info'] = vuls_statics

    json.dump(result_statistics, open(statistics_path, 'w'), indent=4)

def save_switch_info(binary_name, collector):
    switch_info_path = os.path.join(firmware_info_path, '%s_ijmp.json' % (binary_name))
    # print("Switch-save: %s" % (switch_info_path))
    switch_targets = collector.switch_targets
    # print(switch_targets)
    json.dump(switch_targets, open(switch_info_path, 'w'), indent=4)


def get_binary_name(binary_location):
    bs = binary_location.split('/')
    return bs[-1]


def init_file_path(firmware_name, firmware_version):
    print("data-path: %s" % (data_path))
    if not os.path.exists(data_path):
        os.makedirs(data_path)
    print("ida-data-path: %s" % (ida_data_path))
    if not os.path.exists(ida_data_path):
        os.makedirs(ida_data_path)
    print("result-save-path: %s" % (result_save_path))
    if not os.path.exists(result_save_path):
        os.makedirs(result_save_path)

    global firmware_info_path
    filename = '%s_%s/' % (firmware_name, firmware_version)
    firmware_info_path = os.path.join(ida_data_path, filename)
    print("firmware info path: %s" % (firmware_info_path))
    if not os.path.exists(firmware_info_path):
        os.makedirs(firmware_info_path)

def ida_parse_binary(binary_path, binary_name):
    print("firmware info path: %s" % (firmware_info_path))
    binary_cfg_info_path = os.path.join(firmware_info_path, '%s_cfg.json' % (binary_name))
    binary_block_info_path = os.path.join(firmware_info_path, '%s_block_info.json' % (binary_name))
    switch_info_path = os.path.join(firmware_info_path, '%s_switch.json' % (binary_name))
    print("cfg-info-file: %s" % (binary_cfg_info_path))
    print("block-info-file: %s" % (binary_block_info_path))
    print("switch-info-file: %s" % (switch_info_path))

    if (not os.path.exists(binary_cfg_info_path) or
            not os.path.exists(binary_block_info_path) or
            not os.path.exists(switch_info_path)):
        print("Use ida to parse %s and get binary info." % (binary_name))
        # TODO
        # parse_cfg_info(binary_path, ida_data_path, CONFIG_FILE)

    if not os.path.exists(switch_info_path):
        print("Not found switch info path!!!")
        switch_info_path = None

    if (os.path.exists(binary_cfg_info_path) and
            os.path.exists(binary_block_info_path)):
        return binary_cfg_info_path, binary_block_info_path, switch_info_path

    else:
        raise NoIdaCFGFileError

def get_idirect_call_info(binary_path, binary_name):
    """
    Get icall and ijmp info.
    """
    icall_info_path = os.path.join(firmware_info_path, '%s_icall.json' % (binary_name))
    if not os.path.exists(icall_info_path):
        icall_info_path = None

    ijmp_info_path = os.path.join(firmware_info_path, '%s_ijmp.json' % (binary_name))
    if not os.path.exists(ijmp_info_path):
        ijmp_info_path = None

    return icall_info_path, ijmp_info_path

def get_result_statistics(statistics_path):
    if os.path.exists(statistics_path):
        result_statistics = json.load(open(statistics_path, 'r'))
    else:
        result_statistics = {}
    return result_statistics

def load_binary_bytes(binary_name):
    """
    Load binary bytes from Ida Pro, the binary couldn't directly analyzed by Angr.
    """
    binary_bytes_path = os.path.join(ida_data_path, '%s.bytes' % (binary_name))
    if not os.path.exists(binary_bytes_path):
        return None

    else:
        with open(binary_bytes_path, 'rb') as f:
            binary_bytes = f.read()
            return binary_bytes


def print_irsb(proj):

    addr = 0x9db

    s = proj.factory.blank_state()
    s.block(addr).vex.pp()

def custom_user_search():
    from angr.analyses.code_location import CodeLocation

    user_search = {}

    s_locations = []
    user_search[0xa36] = s_locations

    # rsi = CodeLocation(0xaf2, 11)
    # s_locations.append(rsi)

    # rsi = CodeLocation(0xad9, 25)
    rdi = CodeLocation(0xa61, 1)
    # s_locations.append(rsi)
    s_locations.append(rdi)

    return user_search

def custom_sink():
    user_sink = {}

    user_sink[0x2bf64] = {0x2c260: 2}

    return user_sink

def print_results(collector):
    iptr_info = collector.datas['Iptr']
    fptr_info = collector.datas['Fptr']
    for funcea, datas in iptr_info.items():
        if len(datas):
            print("\nFunc (Iptr): %x" % (funcea))
        for data in datas:
            print(" %s %s" % (data, data.expr.source))

    for funcea, datas in fptr_info.items():
        if len(datas):
            print("\nFunc (Fptr): %x" % (funcea))
        for data in datas:
            print(" %s %s" % (data, data.expr.source))


def add_text_section(ida_object):
    base_addr = ida_object.base_addr
    code_start, code_end = 0xffffffffffffffff, -1
    for function in ida_object.cfg_record:
        funcea = int(function, 16) + base_addr
        if funcea > code_end:
            code_end = funcea
        if funcea < code_start:
            code_start = funcea
    section_regions['.text'] = (code_start, code_end)

# def initialize_global_config(proj):
#     """
#     Initialize all global variables which from the binary.
#     """
#     main_object = proj.loader.main_object

#     for section in main_object.sections:
#         region_name = section.name
#         if region_name in choose_region_names:
#             start = section.vaddr
#             end = start + section.memsize
#             section_regions[region_name] = (start, end)


def test_global_config(binary):

    proj = load_binary(binary)

    initialize_global_config(proj)

    from dataflow.global_config import section_regions, arch_info
    print("secton regions: %s" % (section_regions))
    print("arch bits: %s" % (arch_info))

    import claripy
    t = claripy.BVS("t", 32, explicit_name=True)

    from dataflow.variable_expression import VarExpr
    expr = VarExpr(t)
    print("expr: %s" % (expr))


def perform_analysis(binary,
                     taint_check=False,
                     icall_check=False,
                     switch_check=False,
                     firmware_name=None,
                     firmware_version=None,
                     resolve_icall=True,
                     debug=False,
                     load_ida_bytes=False):

    analyzed_time_start = time.time()
    functions = []

    # import_libaries = {
    #     # 'libc.so.0': '/home/kuc822/work/Binaries/rv130/libc.so.0',
    #     'libuClibc-0.9.28.so': '/home/kuc822/work/Binaries/rv130/libuClibc-0.9.28.so'
    # }
    import_libaries = {}
    libary_links = {'libuClibc-0.9.28.so': ['libc.so.0']}

    init_file_path(firmware_name, firmware_version)

    binary_name = get_binary_name(binary)

    binary_cfg_info_path, binary_block_info_path, switch_info_path = ida_parse_binary(binary, binary_name)

    icall_info_path, ijmp_info_path = get_idirect_call_info(binary, binary_name)
    print("Icall-info-file: %s" % (icall_info_path))
    print("Ijmp-info-file: %s" % (ijmp_info_path))
    print("Results-path: %s" % (result_save_path))
    # return

    proj = load_binary(binary)
    initialize_global_config(proj)

    binary_bytes = load_binary_bytes(binary_name)

    binary_parser = BinaryParser(proj, binary_bytes=binary_bytes)

    # binary_cfg_info_path = None
    # binary_block_info_path = None

    libary_objects = {}
    call_graph = CallGraph()

    start_funcea = 0x0
    # start_funcea = 0x4384C4
    if start_funcea:
        debug_call_graph = CallGraph()
        debug_ida_object = IDAProcess(call_graph=debug_call_graph,
                                binary_cfg_info_path=binary_cfg_info_path,
                                binary_block_info_path=binary_block_info_path,
                                switch_info_path=switch_info_path,
                                icall_info_path=icall_info_path,
                                ijmp_info_path=ijmp_info_path,
                                binary_bytes=binary_bytes,
                                resolve_switch=switch_check,
                                binary_name='main')

        debug_ida_object.load_icall_info()
        debug_ida_object.add_icall_edge()

        start_func = debug_call_graph.get_function_by_addr(start_funcea)
        tree_nodes = debug_call_graph.get_all_nodes_by_root(start_func)
        for func in tree_nodes:
            # if func.addr in [0x12000bda4]:
            #     continue
            funcea_hex = '%x' % (func.addr)
            functions.append(funcea_hex)
            print(funcea_hex)
        # print(len(functions))
        # return


    if len(functions):
        ida_object = IDAProcess(call_graph=call_graph,
                                functions=functions,
                                binary_cfg_info_path=binary_cfg_info_path,
                                binary_block_info_path=binary_block_info_path,
                                switch_info_path=switch_info_path,
                                icall_info_path=icall_info_path,
                                ijmp_info_path=ijmp_info_path,
                                binary_bytes=binary_bytes,
                                resolve_switch=switch_check,
                                resolve_icall=resolve_icall,
                                binary_name='main')

    else:
        ida_object = IDAProcess(call_graph=call_graph,
                                binary_cfg_info_path=binary_cfg_info_path,
                                binary_block_info_path=binary_block_info_path,
                                switch_info_path=switch_info_path,
                                icall_info_path=icall_info_path,
                                ijmp_info_path=ijmp_info_path,
                                binary_bytes=binary_bytes,
                                resolve_switch=switch_check,
                                resolve_icall=resolve_icall,
                                binary_name='main')


    libary_objects['main'] = ida_object

    if '.text' not in section_regions:
        add_text_section(ida_object)

    print("section regions:")
    for name, (start, end) in section_regions.items():
        print("%s 0x%x 0x%x" % (name, start, end))
    # return

    # for node in ida_object.ida_cfg.graph.nodes():
    #     print("xxx-> %s" % (node))

    for libary_name, libary_file in import_libaries.items():
        libary_cfg_info_path, libary_block_info_path, _ = ida_parse_binary(libary_file, libary_name)
        # print("libary: %s\n has cfg info: %s\n has block info: %s" % (libary_name, libary_cfg_info_path, libary_block_info_path))

        lib_ob = proj.loader.find_object(libary_name)
        if lib_ob:
            libary_ida_object = IDAProcess(call_graph=call_graph,
                                           binary_cfg_info_path=libary_cfg_info_path,
                                           binary_block_info_path=libary_block_info_path,
                                           base_addr=lib_ob.image_base_delta,
                                           binary_name=libary_name)
            libary_objects[libary_name] = libary_ida_object
            if libary_name in libary_links:
                for link_name in libary_links[libary_name]:
                    libary_objects[link_name] = libary_ida_object

        else:
            print("Not found libary %s" % (libary_name))

        # print(libary_object.ida_cfg)

    # DEBUG
    # ida_object.print_ida_cfg_graph()
    # ida_object.print_cg_graph()
    print("Analyzed all functions number: %d" % (len(ida_object.cg._nodes)))

    blocks_data_info = ida_object.collect_blocks_info()
    start_functions = []

    user_search_locatons = {}
    # user_search_locatons = custom_user_search()

    user_sinks = {}
    # user_sinks = custom_sink()

    fast_dataflow = FastDataFlow(proj)
    accurate_dataflow = AccurateDataFlow(proj, icall_check=icall_check, taint_check=taint_check)
    collector = Collector(proj)

    FastSearch(proj, binary_parser, ida_object, accurate_dataflow, fast_dataflow, collector,
               call_graph,
               start_functions=start_functions,
               blocks_data_info=blocks_data_info,
               search_locations=user_search_locatons,
               user_sinks=user_sinks,
               libary_objects=libary_objects,
               taint_check=taint_check,
               icall_check=icall_check,
               switch_check=switch_check,
               debug=debug)

    # collector.alias_check()
    # re_construct_cfg(collector, binary_cfg_info_path, binary_block_info_path)

    filename = '%s_%s.json' % (firmware_name, firmware_version)
    statistics_path = os.path.join(result_save_path, filename)
    print("Result-statistics-path: %s" % (statistics_path))
    result_statistics = get_result_statistics(statistics_path)

    if icall_check:
        save_icall_info(binary_name, collector)
        result_statistics['icall'] = {}
        total_time = '%lf' % (time.time() - analyzed_time_start)
        result_statistics['icall']['time'] = total_time
        save_icall_statistics(ida_object, collector, statistics_path, result_statistics)

    if switch_check:
        save_switch_info(binary_name, collector)

    if taint_check:
        security_engine = SecurityCheck(collector)
        security_engine.check_taint_security()

        security_engine.print_weaks()

        # for alias_id, cons_exprs in collector.constraints.items():
        #     for cons_expr in cons_exprs:
        #         print("collector-cons: %s %s %s %s" % (alias_id, cons_expr, cons_expr.expr.source, cons_expr.expr.invariant_loc))

        taint_name = 'taint_%d' % (resolve_icall)
        result_statistics[taint_name] = {}
        total_time = '%lf' % (time.time() - analyzed_time_start)
        result_statistics[taint_name]['time'] = total_time
        save_taint_statistics(ida_object, security_engine, statistics_path, result_statistics, resolve_icall)

def main():
    parser = argparse.ArgumentParser(description="Firmware Binary Static Analysis Tool.")
    parser.add_argument("-f", "--binary_file", help="single binary file in firmware")
    parser.add_argument("-i", "--icall_check", default=False, help="check and resolve the switch jmp", action="store_true")
    parser.add_argument("-t", "--taint_check", default=False, help="check and resolve the switch jmp", action="store_true")
    parser.add_argument("--switch_check", default=False, help="check and resolve the switch jmp", action="store_true")
    parser.add_argument("-n", "--firmware_name", help="the firmware name, used for binary info generated by Ida Pro")
    parser.add_argument("-v", "--firmware_version", help="the firmware version, used for different binary path")
    parser.add_argument("--resolve_icall", default=1, type=int, help="If reolve indirect call while doing taint analysis")
    parser.add_argument("--debug", default=False, help="check and resolve the switch jmp", action="store_true")
    parser.add_argument("--load_ida_bytes", default=False, help="whether load binary bytes from IDA Pro", action="store_true")
    args = parser.parse_args()

    if not args.binary_file or args.firmware_name is None or args.firmware_version is None:
        parser.print_help()
        sys.exit()

    perform_analysis(args.binary_file,
                     taint_check=args.taint_check,
                     icall_check=args.icall_check,
                     switch_check=args.switch_check,
                     firmware_name=args.firmware_name,
                     firmware_version=args.firmware_version,
                     resolve_icall=args.resolve_icall,
                     debug=args.debug,
                     load_ida_bytes=args.load_ida_bytes,
                     )

if __name__ == "__main__":
    main()
