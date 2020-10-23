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


# Global Nmae
_save_path = '/home/kai/Work/angr-work/exp_data/'

def load_binary(binary):
    proj = angr.Project(binary,
                        default_analysis_mode='symbolic',
                        )
    return proj


# def load_binary(binary):
#     proj = angr.Project(binary,
#                         use_sim_procedures=True,
#                         default_analysis_mode='symbolic',
#                         load_options={'auto_load_libs': False},
#                         )
#     return proj


def re_construct_cfg(collector, binary_cfg_info_path, binary_block_info_path):
    """
    Re-construct CFG.
    """
    cfg_record = json.load(open(binary_cfg_info_path, 'r'))
    blocks_record = json.load(open(binary_block_info_path, 'r'))

    for funcea, icall_info in collector.icall_targets.items():
        print("Function: %x" % (funcea))
        funcea_s = '%x' % (funcea)
        func_cfg_record = cfg_record[funcea_s]
        func_block_record = blocks_record[funcea_s]

        print(func_cfg_record)
        print(func_block_record)

        call_info = func_cfg_record['call']

        for loc, targets in icall_info.items():
            block_addr_s = '%s' % (loc.block_addr)

            if block_addr_s in func_block_record:
                print("Found, %s %s" % (loc, func_block_record[block_addr_s]))


def save_icall_info(binary_name, collector):
    icall_info_path = os.path.join(firmware_info_path, '%s_icall.json' % (binary_name))
    print("Icall-save: %s" % (icall_info_path))
    icall_targets = collector.icall_targets
    print(icall_targets)
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
            print("Resolved icall in %x" % (addr))
        recovered_icall_num += len(icall_info)

    for icall in all_icalls:
        if icall not in recovered_icalls:
            print("Non-recovery-icall in %x" % (icall))

    print("Binary has icalls: %d" % (len(all_icalls)))
    print("Recovered icalls: %d" % (recovered_icall_num))
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
    tainted_copy_func_num = 0
    call_graph = ida_object.cg

    for function in call_graph.graph.nodes():
        if function.addr == 0:
            continue
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
                    tainted_copy_func_num += 1
                    tainted_node_num += 1
            else:
                analyzed_node_num += 1
                if node.is_tainted == 1:
                    tainted_node_num += 1
    print("All-funcs: %d\nAll-analyzed-funcs: %d\nAll-analyzed-blocks: %d\nAll-tainted-blocks: %d"
          % (all_func_num, analyzed_func_num, analyzed_node_num, tainted_node_num))
    result_statistics[taint_name]['all_functions'] = all_func_num
    result_statistics[taint_name]['analyzed_functions'] = analyzed_func_num
    result_statistics[taint_name]['all_blocks'] = analyzed_node_num
    result_statistics[taint_name]['tainted_blocks'] = tainted_node_num
    result_statistics[taint_name]['tainted_copy_funcs'] = tainted_copy_func_num

    buffer_overflow_num = len(security_engine.weaks)
    buffer_overflow_num += len(security_engine.weaks_length)
    command_exec_num = len(security_engine.weaks_exec)
    print("Weak-copys: %d\nCommand-exec: %d" % (buffer_overflow_num, command_exec_num))
    result_statistics[taint_name]['buffer_overflow_num'] = buffer_overflow_num
    result_statistics[taint_name]['command_exec_num'] = command_exec_num

    buffer_overflows = {}
    result_statistics[taint_name]['buffer_overflow'] = buffer_overflows
    for addr, stack_offsets in security_engine.weaks.items():
        addr_str = '%x' % (addr)
        buffer_overflows[addr_str] = list(stack_offsets)
    command_execs = []
    for addr in security_engine.weaks_exec:
        addr_str = '%x' % (addr)
        command_execs.append(addr_str)
    result_statistics[taint_name]['command_exec'] = command_execs
    tainted_copy_lengths = []
    for addr in security_engine.weaks_length:
        addr_str = '%x' % (addr)
        tainted_copy_lengths.append(addr_str)
    result_statistics[taint_name]['tained_length'] = tainted_copy_lengths

    json.dump(result_statistics, open(statistics_path, 'w'), indent=4)

def save_switch_info(binary_name, collector):
    switch_info_path = os.path.join(firmware_info_path, '%s_ijmp.json' % (binary_name))
    print("Switch-save: %s" % (switch_info_path))
    switch_targets = collector.switch_targets
    print(switch_targets)
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

# def save_results(binary_name):
#     import pickle
#     from dataflow.data_trace import collect_icall_exprs, collect_ptr_exprs

#     print("#"*30 + "Result!" + "#"*30)
#     icall_results = {}
#     ptr_results = {}
#     for funcea, exprs in collect_icall_exprs.items():
#         icall_results[funcea] = exprs
#         print("  Icall: %x" % (funcea))
#         for expr in exprs:
#             print("%s %s" % (expr.expr.source, expr))
#             print("  actions:")
#             for sim_action in expr.expr.sim_actions.values():
#                 print("%s" % (sim_action))
#             print("")

#     for funcea, exprs in collect_ptr_exprs.items():
#         ptr_results[funcea] = exprs
#         print("  Ptr: %x" % (funcea))
#         for expr in exprs:
#             print("%s %s" % (expr.expr.source, expr))
#             print("  actions:")
#             for sim_action in expr.expr.sim_actions.values():
#                 print("%s" % (sim_action))
#             print("")

#     global _save_path
#     icall_file = _save_path + '%s.icall.txt' % (binary_name)
#     with open(icall_file, 'wb') as f1:
#         pickle.dump(icall_results, f1)

#     ptr_file = _save_path + '%s.ptr.txt' % (binary_name)
#     with open(ptr_file, 'wb') as f2:
#         pickle.dump(ptr_results, f2)

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

    # DEBUG
    # '34b710', '30a680', '34b3b0'
    # '280510', '2839d0', '334e50'
    analyzed_time_start = time.time()
    functions = []
    # functions = ['278e00', '3e0370']
    # functions = ['3e0700', '293f10']
    # functions = ['265980', '409ab0']
    # functions = ['27ec60', '27e230']
    # functions = ['2f2810']
    # functions = ['364140']
    # functions = ['382ab0', '384730']
    # functions = ['38d870']
    # functions = ['2bc3d0']
    # functions = ['293f10']
    # functions = ['40aca0']
    # functions = ['2e3060']
    # functions = ['364140']
    # functions = ['3e09d0']
    # functions = ['380da0']
    # functions = ['2cef90', '40b7e0']
    # functions = ['4406a0']
    # functions = ['2d05b0']
    # functions = ['320fb0']
    # functions = ['45f230']
    # functions = ['37ad50']
    # functions = ['370d70']
    # functions = ['25a9c0']
    # functions = ['3d33f0']

    # Trace to ret
    # functions = ['38a530', '3780d0', '3780c0']
    # functions = ['376030', '389350', '389340', '388ec0']
    # functions = ['471af0', '32ffe0']
    # functions = ['35d7c0', '35d670']

    # Update ret pointer to callsite
    # functions = ['3302c0']

    # functions = ['44dab0']

    # virtfunc
    # functions = ['400f9e', '401076', '400e28']
    # functions = ['4011e0']

    # virtual_inheritance
    # functions = ['400659']

    # virtual_vtv
    # functions = ['4009b7']

    # filezilla
    # functions = ['8b1ac0']
    # functions = ['a02d50']
    # functions = ['83f660', '83f7c0']
    # functions = ['934d20', '9341b0', '989170']
    # functions = ['8200b0']
    # functions = ['8200b0']
    # functions = ['793a90', '790fd0']
    # functions = ['790fd0']
    # functions = ['934d20', '793a90', '790fd0']
    # functions = ['793a90', '790fd0']
    # functions = test_loop_function()
    # functions = ['759030']
    # functions = ['a03db0', 'a03d50', 'a06b80', 'a06c30']
    # functions = ['a03db0', 'a03d50', 'a06b80']
    # functions = ['8cab50', '912e70', '8cd430']
    # functions = ['7609c0', '803fb0', '8cd010', '7e1d40', '82c810', '7e25d0']
    # functions = ['957da0']
    # functions = ['83a740', '83b2d0']
    # functions = ['832b00']
    # functions = ['957da0', '954770']

    # array_alias
    # functions = ['a33', 'a13']

    # func-ptr-in-class
    # functions = ['d2c', 'b81']

    # swap-structindirect - test faild
    # functions = ['9f1', '9b3']

    # function_handle_test
    # functions = ['c5b', 'b3e', 'bcc']
    # functions = ['c5b', 'bcc']

    # loops_test
    # functions = ['9b3']
    # functions = ['c9f']
    # functions = ['a36']

    # context-sensitive-1
    # functions = ['aef', 'e32', '9f1', '6d0', 'ada']

    # constraint-cycle-copy
    # functions = ['963', '7c4', '7e1', '78a']

    # constraint-cycle-field
    # functions = ['8f3', '754']

    # Test icall recovery!
    # virtual_inheritance
    # functions = ['e3b', 'e5c', '114c']
    # functions = ['104e']

    # vsftpd
    # functions = ['40d330']
    # functions = ['4145d0']
    # functions = ['40bfc0']

    # httpd (arm)
    # Icall test
    # functions = ['1f9a0', '1ea0c']
    # functions = ['1f9a0', ]
    # functions = ['25bac', ]
    # functions = ['2d990', '29590']
    # functions = ['2d394', '23dc4']

    # strcpy sink test
    # functions = ['2bf64', '2c4b0', '2c614', '1d170']
    # functions = ['1d170']

    # read/fread source test
    # functions = ['1db6c', '2d228', '1cfb4', '1cf1c']
    # functions = ['1db6c', '2d228', '1cfb4']
    # functions = ['1f9a0', '2d228', '1db6c', '2cd44']
    # functions = ['1d170', '2c614', '2c4b0', '2bf64']
    # functions = ['11f44']
    # functions = ['1db6c', '2d228', '1cfb4', '1cf1c', '1f9a0', '2cd44', '2c614', '1d170', '2c4b0', '2bf64']
    # functions = ['1cfb4']
    # functions = ['18d44', '1d170']
    # functions = ['2a878', '35458', '1d170']
    # functions = ['52db4', '538c0', '1d170']
    # functions = ['1de00', '1f9a0']
    # functions = ['6e230', '1de00']
    # functions = ['7c064', '7c1d4', '7ca24', '722f8', '25bac', ]
    # functions = ['4cee0',]

    # openssl-arm
    # tls1_process_heartbeat, ssl3_read_bytes, ssl3_read_n
    # functions = ['67c34', '6fb94', '66fcc', 'c7b78']
    # functions = ['66fcc', 'c7b78']
    # functions = ['6fb94']

    # 0x2120c -> 0x2d228

    # Schneider WebServer
    # functions = ['918']
    # strcpy bug in websSecurityHandler
    # functions = ['895c']
    # functions = ['9b88', '937c', '8e0c', '8414', '83c0', '8484', '8874', '88e8', '94d0', '8814', '85dc', '80e0', '80a8', 'ffd8', '8778', '86a8', '9c8', '918', '65f0', '895c', '8074', '7a9c', '7730', 'f268']
    # functions = ['9b88', '937c', '8e0c', '8414', '83c0', '8484', '8874', '88e8', '94d0', '8814', '85dc', '80e0', '80a8', ]
    # functions = ['9b88', '937c', '8e0c', '8414', '83c0', '8484', ]
    # functions = ['86a8', '8484', '85dc', '8778']
    # functions = ['937c', ]
    # functions = ['8074', '7a9c']
    # functions = ['688c']
    # functions = ['2ebe8', '21074']

    # functions = ['65f0']
    # functions = ['17254', '6288', '65f0']
    # functions = ['6288']
    # functions = ['a924']
    # functions = ['f268']

    # cisco rv160 mini_httpd
    # functions = ['1c5b4', '16f60', '1c0f8', '1c75c', '1c13c']
    # functions = ['1c75c']

    # cisco rv160 admin.cgi
    # functions = ['1e410', '1e6fc']
    # functions = ['69694', '1b600', '1a89c', '3254c', '1962c', '18064', '56bf0', '1b7e8', '1b6f8']

    # cisco rv320 ssi.cgi (mips)
    # functions = ['1201034f0', ]
    # functions = ['12013a348', '12013a474', '120138d30', '12013b478', '12013b2f4', '120138e24', '12013ae14', '120139fa8', '120139360', '12000f7d8', '12000f634', '12000ec60', '12000be70', '120075ca8', '12005cee0', '12013a72c', '120139ddc', '120139798', '120073df4']
    # functions = ['12013a348', '12013a474', '120138d30', '12013b478', '12013b2f4', '120138e24', '12013ae14', '120139fa8', '120139360', '12000f7d8']
    # functions = ['12000f634', '12000ec60', '12000be70', '120075ca8', '12005cee0', '12013a72c', '120139ddc', '120139798', '120073df4']
    # functions = ['120075ca8','12005cee0', '12013a72c','120139ddc', '120139798', '120073df4']
    # functions = ['12005cee0', '12013a72c','120139ddc', '120139798', '12009f308']
    # functions = ['12005cee0', '12013a72c','120139ddc', '120139798', '120075ca8']
    # functions = ['12005cee0', '12013a72c','120139ddc', '120139798', '1200955d4']
    # functions = ['1200dc88c','12005cee0', '12013a72c']
    # functions = ['12005cee0', '12013a72c', '12006cfd4']
    # functions = ['12009f730']
    # functions = ['120073df4',]
    # 1200C342C

    # Trendnet tew-632brp httpd
    # 407f5c
    # functions = ['40a4bc', '406504', '405888', '4057bc', '40a108', '406990', '405750', '4124cc']
    # functions = ['406504', '406990']

    # Trendnet tew-827dru v2.04 ssi
    # functions = ['441df4', '442604', '4426a4', '4420d0']
    # functions = ['442204', '42dc48']
    # functions = ['442204', '4379a4', '437a04', '4378d4', '43793c', '40e390']
    # functions = ['40b680', '40b7a0', '42dc48', '42f788']
    # functions = ['43d7f4', '43b8fc']
    # functions = ['4a52fc', '45c820']
    # functions = ['43858c']
    # functions = ['438cbc']
    # functions = ['439288']
    # functions = ['43d7f4', '43b8fc']
    # functions = ['41fecc', '43b8fc', '4a52fc',]
    # functions = ['40e390', '442204', '437a04', '4378d4']
    # functions = ['4a5830', '4a52fc', '483618']

    # DIR-825 B-2.10 httpd
    # functions = ['414134', '4077c0']
    # functions = ['417280'] # sprintf return value ?
    # functions = ['431a80', '4243c8']
    # functions = ['413c60', '4077c0', '42f4d8']
    # functions = ['426650', '4077c0', '436278']
    # functions = ['41b6b0', '4077c0']
    # functions = ['40b32c', '410b20', '4078f8', '40782c', '419dc4', '40bfc4', '4077c0', '413c60']

    # DIR-823G goahead
    # functions = ['40b1f4', '423f90', '40b740']
    # functions = ['40ee2c', '41fba4', '40f498']
    # functions = ['42383c']
    # functions = ['498974', '49a47c', '49aee4', '49c32c', '402530', '45af28', '45ac00', '461704', '461cb4', '462b1c', '402540', '49ba44']
    # functions = ['40e550', '40ffc8', '40e144', '41cb7c', '40e7d8', '40d950', '40d1a4', '40d104', '41c488', '40b740', '42383c', ]

    # DGN2200
    # functions = ['40d70c', '40adc0', '40b970', '412d00', '41f6a4', '410f3c']

    # DGN1000
    # functions = ['413c7c', '413a88', '413908', '41458c', '4137a4', '414440', '408740', '4134dc', '414848', '4129c8', '409d64', '408924', '410ce8', '410eac']
    # functions = ['43d9b0']

    # DGN2200v4
    # functions = ['4a4f74', '4a573c', '4a55c0', '4a573c', '408f90']
    # functions = ['4140b0', '4143ec', '4914cc']
    # functions = ['4140b0', '4143ec']

    # R7800
    # functions = ['3139c']
    # functions = ['e5e0']

    # R6400
    # functions = ['18764', '1cd80']
    # functions = ['18764', '37058',]
    # functions = ['18764', '37058', '2c2f8', '19abc', 'fbe0', '14364', 'f414']
    # functions = ['1ce14', '1c058', ]

    # functions = ['67db8']

    # WNR3500Lv2
    # functions = ['41bf0c', '41c254']
    # functions = ['41c070', '427fac']
    # functions = ['41c070', '4532d0']

    # R9000
    # functions = ['1a7c4']

    # R7500v2
    # functions = ['31634']

    # R8300
    # functions = ['1a384']

    # functions = ['43e180', '43dc40']
    # functions = ['1a4ec', '18e08']

    # TP-Link NC260
    # functions = ['485524', '469de4', '46a060', '46a368', '46a17c', ]
    # functions = ['4f8dfc', '4f8738', '4f8b7c', '4f894c', '4f8dd0', '46a734', '46a368', '482590', '4f956c']
    # functions = ['482590', '4f956c', '4591e4', '459c10']

    # functions = ['410ec8', '4123cc', '40fa8c', '4110f4', '410140']

    # US_AC15V1.0BR-v15.03.05.18
    # functions = ['9f04', '998c', '9c40', 'ad7c', 'b1b0', '9b30', '9de8',]

    # functions = ['40d71c', '412bcc']

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

    # Setting the code section manually.

    # WebServer
    # section_regions['.rodata'] = (0x4fb88, 0x61be7)
    # section_regions['.extern'] = (0x1000000, 0x2000000)

    # TEW827DRU v2.04
    # section_regions['.text'] = (0x4054a0, 0x4b1f00)
    # section_regions['.rodata'] = (0x4b1f04, 0x4db790)
    # section_regions['.data'] = (0x4eb794, 0x5094d4)
    # section_regions['.bss'] = (0x5094d8, 0x1e5383b)

    # DIR-823G goahead
    # section_regions['.text'] = (0x401cb0, 0x4a03f4)
    # section_regions['.rodata'] = (0x4a03f8, 0x4afb9f)
    # section_regions['.data'] = (0x4afba0, 0x5895ab)
    # section_regions['.bss'] = (0x5898b8, 0x598763)


    binary_bytes = load_binary_bytes(binary_name)

    binary_parser = BinaryParser(proj, binary_bytes=binary_bytes)

    # binary_cfg_info_path = None
    # binary_block_info_path = None

    libary_objects = {}
    call_graph = CallGraph()

    # functions = ['41dff4', '41d208', '414054', '40769c']
    # functions = ['414054', '40769c', '412e30', '41d208', '41d418', '41ce18', '412bcc']
    # functions = ['42b778', '40d67c', '414010', '412e30']
    # functions = ['12000be70']
    start_funcea = 0x0
    # start_funcea = 0x42dcac
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

        # function_count = 0
        # for func in debug_ida_object.cg.graph.nodes():
        #     function_count += 1
        #     print(func)
        # print("All functions number: %d" % (function_count))

        start_func = debug_call_graph.get_function_by_addr(start_funcea)
        tree_nodes = debug_call_graph.get_all_nodes_by_root(start_func)
        for func in tree_nodes:
            # if func.addr in [0x12000bda4]:
            #     continue
            funcea_hex = '%x' % (func.addr)
            functions.append(funcea_hex)
            print(funcea_hex)
        # functions.append('12000f7d8')
        print(len(functions))
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
    # print(blocks_data_info)

    # for node in ida_object.ida_cfg.graph.nodes():
    #     print("xxx-> %s" % (node))
    # return

    # data_parser = DataParser(binary_parser, blocks_data_info)

    # cfg.print_cfg_graph()
    # cfg.print_cg_graph()

    # DEBUG
    # test_start_functions = [0x82c810]
    # test_start_functions = [0x7e8090]
    # test_start_functions = [0x912e70]
    start_functions = []
    # for funcea in test_start_functions:
    #     start_func = ida_object.cg._nodes[funcea]
    #     start_functions.append(start_func)

    # start_functions = []
    # print("start functions: %s" % (start_functions))

    # for node in ida_object.ida_cfg.graph.nodes():
    #     print("xxx-> %s" % (node))

    user_search_locatons = {}
    # user_search_locatons = custom_user_search()

    # user_sinks = {}
    user_sinks = custom_sink()

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

        for alias_id, cons_exprs in collector.constraints.items():
            for cons_expr in cons_exprs:
                print("collector-cons: %s %s %s %s" % (alias_id, cons_expr, cons_expr.expr.source, cons_expr.expr.invariant_loc))

        taint_name = 'taint_%d' % (resolve_icall)
        result_statistics[taint_name] = {}
        total_time = '%lf' % (time.time() - analyzed_time_start)
        result_statistics[taint_name]['time'] = total_time
        save_taint_statistics(ida_object, security_engine, statistics_path, result_statistics, resolve_icall)

    # for funcea in collector.analyzed_functions:
    #     print("0x%x " % (funcea))
    # from dataflow.sim_procedure import nvram_values
    # print(nvram_values)


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
