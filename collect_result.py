#!/usr/bin/env python

import sys
import json


def load_results(filename: str):
    """
    """
    results = json.load(open(filename, 'r'))
    # print(results)
    return results


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("The arguments is not true!")
        exit(1)

    filename = sys.argv[1]
    func = sys.argv[2]

    results = load_results(filename)

    if func == "alert":
        bugs_info = results.get("taint_1")
        print("=="*10+" Alerts produced by EmTaint "+"=="*10)
        print("Ana. Func: %d" % (bugs_info['analyzed_functions']))
        print("Tainted Sinks: %d" % (bugs_info['tainted_sinks']))
        print("Alerts: %d" % (bugs_info['buffer_overflow_num']+bugs_info['command_exec_num']))
        print("Time (s): %s" % (bugs_info['time']))

    elif func == "icall":
        icall_info = results.get("icall")
        print("=="*10+" Results of indirect call resolution "+"=="*10)
        print("All I-Calls: %d" % (icall_info['all_icall']))
        print("Resolved I-Calls: %d" % (icall_info['recovered_icall']))
        print("I-Call Targets: %d" % (icall_info['add_icall_target']))
        print("% of reolved I-Calls: {:.1%}".format(icall_info['recovered_icall']/icall_info['all_icall']))
        print("Time (s): %s" % (icall_info['time']))

    elif func == "compare":
        bug0 = results.get("taint_0")
        bug1 = results.get("taint_1")

        a0 = bug0['all_blocks']
        b0 = bug0['tainted_blocks']
        c0 = bug0['tainted_sinks']
        d0 = bug0['buffer_overflow_num'] + bug0['command_exec_num']

        a1 = bug1['all_blocks']
        b1 = bug1['tainted_blocks']
        c1 = bug1['tainted_sinks']
        d1 = bug1['buffer_overflow_num'] + bug1['command_exec_num']

        print("=="*10+" The impact of indirect call resolution "+"=="*10)
        print("               w/o I-Call Resolution               |                I-Call Resolution  ")
        print("Ana. Block   Tainted Block   Tainted Sink   Alerts | Ana. Block   Tainted Block   Tainted Sink   Alerts")
        print("   %d          %d           %d         %d         %d          %d            %d          %d"  % (a0, b0, c0, d0, a1, b1, c1, d1))

    else:
        print("Function %s is not supported!" % (func))
