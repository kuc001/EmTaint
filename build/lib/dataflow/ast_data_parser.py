#!/usr/bin/env python

import logging
l = logging.getLogger("ast_data_parser")
l.setLevel("INFO")


def find_all_load_datas(ast_data):
    """
    Find all child load ast variables in the ast_data.
    Only process the load(rax), load(rax + offset), or load(0x467890)
    """
    load_info = {}
    sub_datas = []
    if ast_data.op == 'BVS':
        return load_info

    elif ast_data.op == 'Load':
        sub_datas.append(ast_data)

    for child in ast_data.recursive_children_asts:
        if child.op == 'Load':
            sub_datas.append(child)

    for sub_data in sub_datas:
        addr = sub_data.args[0]
        if addr.op == 'BVS':
            v = addr.args[0]
            if v not in load_info:
                load_info[v] = {}
            load_info[v][0] = sub_data

        elif addr.op == 'BVV':
            v = addr.args[0]
            if 'con' not in load_info:
                load_info['con'] = {}
            load_info['con'][v] = sub_data

        elif addr.op == 'Load':
            continue

        else:
            if len(addr.args) == 2:
                try:
                    if addr.args[0].op == 'BVS' and addr.args[1].concrete:
                        v = addr.args[0].args[0]
                        offset = addr.args[1].args[0]
                        if v not in load_info:
                            load_info[v] = {}
                        load_info[v][offset] = sub_data

                    elif addr.args[1].op == 'BVS' and addr.args[0].concrete:
                        v = addr.args[1].args[0]
                        offset = addr.args[0].args[0]
                        if v not in load_info:
                            load_info[v] = {}
                        load_info[v][offset] = sub_data

                except:
                    l.info("The are error while parse variable %s" % (ast_data))

            else:
                # l.info("Can not get base and offset in ast %s with 3 or more args." % (ast_data))
                continue

    return load_info


def get_deref_info(ast_data):
    """
    Find all child load ast variables in the ast_data.
    Only process the load(rax), load(rax + offset), or load(0x467890)
    """
    deref_info = {}
    sub_datas = []
    if ast_data.op == 'BVS':
        return deref_info

    elif ast_data.op == 'Load':
        sub_datas.append(ast_data)

    for child in ast_data.recursive_children_asts:
        if child.op == 'Load':
            sub_datas.append(child)

    for index, sub_data in enumerate(sub_datas):
        addr = sub_data.args[0]
        if addr.op == 'BVS':
            v = addr.args[0]
            deref_info[index] = ('bvs', (v, 0))

        elif addr.op == 'BVV':
            v = addr.args[0]
            deref_info[index] = ('bvv', (v, 0))

        else:
            if len(addr.args) == 2:
                try:
                    if addr.args[0].op == 'BVS' and addr.args[1].concrete:
                        v = addr.args[0].args[0]
                        offset = addr.args[1].args[0]
                        deref_info[index] = (addr.op, (v, offset))

                    elif addr.args[1].op == 'BVS' and addr.args[0].concrete:
                        v = addr.args[1].args[0]
                        offset = addr.args[0].args[0]
                        deref_info[index] = (addr.op, (v, offset))

                    elif addr.args[1].op == 'BVS' and addr.args[0].op == 'BVS':
                        v0 = addr.args[0].args[0]
                        v1 = addr.args[1].args[0]
                        deref_info[index] = (addr.op, (v0, v1))

                except:
                    l.info("The are error while parse variable %s" % (ast_data))

            # TODO
            # Load(rbx + 0x68 + i * 0x8)

    return deref_info
