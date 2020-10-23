import sys
import logging

import angr
import claripy
from dataflow.parse_binary import BinaryParser
from dataflow.data_trace import FastSearch
from dataflow.ida_process import IDAProcess
from dataflow.data_process import DataParser
from dataflow.variable_expression import VarExpr, TraceExpr, SimAction, Sim
from dataflow.parse_ast import *

# from dataflow.global_config import initialize_global_config_with_default

# initialize_global_config_with_default()

# Global Nmae
_path = '/home/kai/Work/angr-work/binaries/'

_save_path = '/home/kai/Work/angr-work/exp_data/'


def load_binary(binary):
    proj = angr.Project(binary,
                        use_sim_procedures=True,
                        default_analysis_mode='symbolic',
                        load_options={'auto_load_libs': False},
                        )
    return proj


def get_binary_name(binary_location):
    bs = binary_location.split('/')
    return bs[-1]


def test_update_sim_action():

    s = claripy.BVS('s', 32, explicit_name=True)
    rax = claripy.BVS('rax', 32, explicit_name=True)
    t1 = claripy.BVS("t1", 32, explicit_name=True)
    t1_alias = claripy.Load(rax+0x30, 32)

    s_expr = VarExpr(s)
    print("s_expr: %s" % (s_expr))
    t1_alias_expr = s_expr.replace(s, t1_alias)
    print("t1_alias_expr: %s" % (t1_alias_expr))

    re_sim_actions = {}
    re_sim_actions[0] = SimAction(name=("rax", 0x30), binop='+', action_data=t1_alias)
    t1_alias_expr.update_sim_actions(s_expr, s, t1_alias, re_sim_actions=re_sim_actions)

    rbx = claripy.BVS("rbx", 32, explicit_name=True)
    t2 = claripy.Load(rbx+t1, 32) + t1
    t2_expr = VarExpr(t2)

    t2_sim_actions = t2_expr.sim_actions
    t2_sim_actions[0] = SimAction(name=("rbx", "t1"), binop='+', action_data=t2)

    up1_expr = t2_expr.replace(t1, t1_alias)
    print("up1_expr: %s" % (up1_expr))

    up1_expr.update_sim_actions(t2_expr, t1, t1_alias, re_sim_actions)

    up11_expr = up1_expr.replace(t1_alias, t1)
    print("up11_expr: %s" % (up11_expr))

    up11_expr.update_sim_actions(up1_expr, t1_alias, t1, {})

    up0_expr = up1_expr.replace(rax, rbx)
    print("up0_expr: %s" % (up0_expr))

    up0_expr.update_sim_actions(up1_expr, rax, rbx, {})

    # stype = get_mem_permission(0x20)
    # print("stype: %s" % (stype))

    # case 1: t1 = load(rax + 0x30)
    # update 1:
        # load(rbx + load(rax + 0x30)) + load(rax + 0x30)
        # load(rbx +t1) + t1

    # update 2:
        # t1 + load((load(rax) + 0x20)) + load(t1)
        # load(rax + 0x30) + load(load(rax) +0x20) + load(load(rax + 0x30))

    # case 2: store(rax + 0x30) = rdi
    # update 3:
        # load(rbx + load(rax + 0x30)) + load(rax + 0x30)
        # load(rbx + rdi) + rdi

    # update 4:
        # load(0x8 + rdi) + load(rax + 0x30)
        # load(0x8 + store(rax + 0x30)) + rdi

    # update 5: kill
        # load(0x8 + rdi) + load(rax + 0x30)
        # expr is killed, should remove.

    # case 3: rdi = load(load(rsi + 0x80) + 0x12)
    # update 6:
        # load(0x8 + rdi) + rsi
        # load(0x8 + rdi) + load(load(rsi + 0x8) + 0x12)

    # case 4: store(load(rsi + 0x80) + 0x68) = rdi
    # update 7:
        # load(0x14 + rdi) + load(0x8 + rdi)
        # load(0x14 + store(load(rsi + 0x80) + 0x68)) + load(xxx)

    # update 8:
        # load(load(rsi + 0x80) + 0x68) + load(rsi + 0x44)
        # rdi + load(rsi + 0x44)

    # case 5: store(rsp + 0x4) = load(load(rdi + 0x8) + 0x14)
    # update 8:
        # load(0x8 + rdi) + load(rsp + 0x4)
        # load(0x8 + rdi) + load(load(rid + 0x8) + 0x14)


# def main(binary):

    # binary_name = get_binary_name(binary)
    # proj = load_binary(binary)
    # ast_parser = ASTParser(proj)
    # binary_parser = BinaryParser(proj, ast_parser=ast_parser)


def test_shines(changed_ls_indexs, child_indexs, sub_indexs, rep_indexs):
    # old_indexs = [0, 1, 2, 3, 4, 5, 6, 7, 8]
    changed_ls_indexs = [0, 1, 2, 3, 4, 5, 6, 7, 8]
    # child_indexs = [3, 8]
    child_indexs = [1, 5]

    # old_indexs = []
    # changed_ls_indexs = [0, 1]
    # child_indexs = [0]

    sub_indexs = [0, 1]
    rep_indexs = [0]

    sub_len, rep_len = len(sub_indexs), len(rep_indexs)
    shines, new_indexs = [], []
    tmp_indexs = []
    pos, c = 0, 0

    # Case 1: rdi -> rsi
    if sub_len == 0 and rep_len == 0:
        print("1")
        # sim_actions not changed!
        pass

    # Case 2: rdi -> load(rsi + 0x80)
    elif sub_len == 0 and rep_len > 0:
        print("2")
        # sim_actions changed, add!
        for i in changed_ls_indexs:
            if i in child_indexs:
                new_indexs.append(pos)
                pos += rep_len
                c += 1

            else:
                old_i = i - c
                shine_old_i = pos
                pos += 1
                shines.append((old_i, shine_old_i))

    # Case 3: load(rsi + 0x80) -> rdi
    elif sub_len > 0 and rep_len == 0:
        print("3")
        # sim_actions changed, remove!
        for i in changed_ls_indexs:
            if i in tmp_indexs:
                continue

            if i in child_indexs:
                c += sub_len
                tmp_indexs = [i+j for j in sub_indexs]

            else:
                new_i = i - c
                shines.append((i, new_i))

    # Case 4: store(rsp + 0x24) -> load(rdi + 0x20)
    elif sub_len > 0 and sub_len == rep_len:
        print("4")
        # sim_actions changed, but index not chane!
        for i in changed_ls_indexs:
            if i in tmp_indexs:
                continue

            if i in child_indexs:
                new_indexs.append(i)
                tmp_indexs = [i+j for j in sub_indexs]

            else:
                shines.append((i, i))

    # Case 5: load(xxx) -> store(load(xxx))
    elif sub_len > 0 and rep_len > sub_len:
        # sim_actions changed, add!
        print("5")
        for i in changed_ls_indexs:
            if i in tmp_indexs:
                continue

            if i in child_indexs:
                new_indexs.append(pos)
                tmp_indexs = [i+j for j in sub_indexs]
                pos += rep_len

            else:
                old_i = i
                shine_old_i = pos
                pos += 1
                shines.append((old_i, shine_old_i))

    # Case 6: load(load(xxx)) -> load(xxx)
    elif sub_len > 0 and rep_len < sub_len:
        print("6")
        # sim_actions changed, remove!
        for i in changed_ls_indexs:
            if i in tmp_indexs:
                continue

            if i in child_indexs:
                c += sub_len - rep_len
                new_indexs.append(pos)
                tmp_indexs = [i+j for j in sub_indexs]
                pos += rep_len

            else:
                new_i = i - c
                pos += 1
                shines.append((i, new_i))

    print("shines: %s" % (shines))
    print("new indexs: %s" % (new_indexs))
    for ni in new_indexs:
        add_indexs = [ni+j for j in rep_indexs]
        print("add indexs: %s" % (add_indexs))

if __name__ == "__main__":
    # binary_location = sys.argv[1]
    # print("%s" % (binary_location))
    # main(binary_location)
    test_update_sim_action()
    # test_shines()
