import re
import claripy
import logging

from .global_config import section_regions
from .parse_ast import *
from .variable_type import get_expr_base_ptr
from .code_location import CodeLocation

from .errors import UpdateSimActionsError

l = logging.getLogger("variable_expression")
l.setLevel("INFO")


class Sim(object):

    def __init__(self, live=True, index=None, def_loc=None, var_type=None):

        self.live = live
        self.index = index
        self.def_loc = def_loc
        self.var_type = var_type

    def __repr__(self):
        return '<Sim %s (%s)>' % (self.live, self.var_type)


    def copy(self):

        new_sim = Sim.__new__(Sim)
        new_sim.live = self.live
        new_sim.index = self.index
        new_sim.var_type = self.var_type
        new_sim.def_loc = self.def_loc

        return new_sim


class SimAction(object):

    def __init__(self, name=None, binop=None, action_data=None, var_type=None, live=True):
        self.name = name
        self.binop = binop
        self.action_data = action_data
        self.live = live

        self.var_type = var_type
        self.def_locs = set()

    def __repr__(self):
        return "<SimAction %s (%s - %s) id:%s>" % (self.action_data, self.live, self.var_type, id(self))


    def copy(self):

        new_sim_action = SimAction.__new__(SimAction)
        new_sim_action.name = self.name
        new_sim_action.binop = self.binop
        new_sim_action.action_data = self.action_data
        new_sim_action.live = self.live
        new_sim_action.var_type = self.var_type
        new_sim_action.def_locs = set()

        for def_loc in self.def_locs:
            new_sim_action.def_locs.add(def_loc)

        return new_sim_action

    def re_store_def(self, base, offset, loc, binop=None):
        if self.name is None or loc in self.def_locs:
            return False

        elif binop and binop != self.binop:
            return False

        elif (((self.action_data.op == 'Store' and self.live) or
                (self.action_data.op == 'Load' and not self.live)) and
                self.name[0] == base and self.name[1] == offset):
            # print("Found store kill in %s %s" % (loc, self))
            return True

        else:
            return False

    def load_use(self, base, offset, loc, binop=None, var_type=None):

        def contain_base(ast, base):
            if not_contain_ls(ast):
                for leaf_ast in ast.recursive_leaf_asts:
                    if leaf_ast.args[0] == base:
                        return True
            return False

        if (loc in self.def_locs or (self.name and self.name[0] is None)):
            return False

        elif binop and self.binop and binop != self.binop:
            return False

        elif (((self.action_data.op == 'Store' and self.live) or
               (self.action_data.op == 'Load'))):
            if (self.name and self.name[0] == base and
                    (self.name[1] == offset or
                    type(self.name[1]) is str and 'o' in self.name[1])):
                return True

            elif (self.name is None and
                    'add' in self.action_data.args[0].op and
                    contain_base(self.action_data.args[0], base)):
                return True

            else:
                return False

        # elif (((self.action_data.op == 'Store' and self.live) or
        #         (self.action_data.op == 'Load')) and
        #         (self.name[0] == base and
        #         (self.name[1] == offset or
        #          type(self.name[1]) is str and 'o' in self.name[1]))):
        #     return True

        else:
            return False

    def get_binop_alias(self, binop, base, offset):
        """
        Find base+offset alias, e.g. Put r3, r4+0x4
        """
        if binop != self.binop or self.name is None:
            return None, None

        if base == self.name[0] and offset == self.name[1]:
            return self.action_data.args[0], 0

        elif (binop == '+' and base == self.name[0] and
                type(offset) is int and type(self.name[1]) is int and
                self.name[1]-offset < 24):
            alias = self.action_data.args[0]
            return alias, self.name[1]-offset

        else:
            return None, None


class TraceExpr(object):
    """
    A TraceExpr represents a live tracing expr in paht.
    """
    def __init__(self, expr, index=None):
        self.expr = expr
        self.index = index
        self.forward_path = set()
        self.backward_path = set()
        self.cycle_locs = []

        self.constraints = []  # the concrete value or single symbol
        self.cons_ids = []  # the constraint expr's alias_id
        self.guard = None

        self.loop_num = 0
        self.inter_icall_level = 0
        self.taint_propagaton_level = 0
        self.inter_funcs = []

    def deep_copy(self):
        new_trace_expr = TraceExpr.__new__(TraceExpr)
        new_trace_expr.expr = self.expr.copy()
        new_trace_expr.index = self.index
        new_trace_expr.guard = self.guard
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs.copy()
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()
        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        new_trace_expr.inter_funcs = self.inter_funcs.copy()
        return new_trace_expr

    def copy(self):
        new_trace_expr = TraceExpr.__new__(TraceExpr)
        new_trace_expr.expr = self.expr
        new_trace_expr.index = self.index
        new_trace_expr.guard = self.guard
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs.copy()
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()
        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        new_trace_expr.inter_funcs = self.inter_funcs.copy()
        return new_trace_expr

    def __repr__(self):
        if self.expr.value is None:
            return '<T-Expr %s (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.base_ptr, self.expr.var_type, self.expr.trace_dir, self.index)
        else:
            if isinstance(self.expr.value, int):
                return '<T-Expr %s: 0x%x (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.var_type,  self.expr.trace_dir, self.index)
            else:
                return '<T-Expr %s: %s (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.var_type, self.expr.trace_dir, self.index)

    def __eq__(self, other):
        """
        Check if self is the same as other.
        """
        if isinstance(other, TraceExpr):
            return self.expr == other.expr
        return False

    def __hash__(self):
        """
        returns the hash value of self.
        """
        return self.expr.__hash__()

    def print_path(self):
        for addr in self.forward_path:
            print("  --> Fpath 0x%x" % (addr))
        for addr in self.backward_path:
            print("  --> Bpath 0x%x" % (addr))
        print("")

    def print_sims(self):
        for var, sim in self.expr.sims.items():
            print(" -->sim %s %s" % (var, sim))

    @property
    def iid(self):
        return self.expr.iid

    @property
    def ast_iid(self):
        return self.expr.ast.__hash__()

    def set_taint_id(self):
        """
        Set taint expr's id in callsite that taint expr propagate to callee.
        """
        self.expr.taint_id = self.expr.ast.__hash__()

    def merge_state(self, new_expr):
        """
        Merge the flags's state between old_expr and new_expr.
        """
        new_flag = new_expr.expr.flag
        # print("old-flag: %x new-falg: %x" % (self.expr.flag, new_flag))
        if self.expr.flag & 0x200 and new_flag & 0x200 ==0:
            self.expr.flag &= 0xfdff
        elif self.expr.flag & 0x200 == 0:
            self.expr.flag |= new_flag
            self.expr.flag &= 0xfdff
        else:
            self.expr.flag |= new_flag

        if not self.expr.taint_source:
            self.expr.taint_source = new_expr.expr.taint_source
        if new_expr.expr.taint_source:
            self.expr.taint_sources.add(new_expr.expr.taint_source)
        if new_expr.expr.taint_sources:
            self.expr.taint_sources |= new_expr.expr.taint_sources

    def clear_sim_index(self):
        """
        Reset the sim.index to None
        """
        for sim in self.expr.sims.values():
            if sim:
                sim.index = None

    # def kill_store_action_live(self, code_location=None):
    #     self.expr.kill_store_action_live(code_location)

    def clear_cycle_locs(self):
        self.cycle_locs.clear()

    def clear_path(self):
        self.forward_path.clear()
        self.backward_path.clear()

    def clear_sim_actions_locs(self):
        for i, sim_action in self.expr.sim_actions.items():
            sim_action.def_locs.clear()

    def do_store_alias(self):
        flag = self.expr.flag
        return not (flag & 0x200)

    def do_load_alias(self):
        flag = self.expr.flag
        return not (flag & 0x200)

    def add_constraint(self, cons):
        if cons not in self.constraints:
            self.constraints = self.constraints[:]
            self.constraints.append(cons)

    def remove_constraint(self, cons):
        self.constraints = self.constraints[:]
        self.constraints.remove(cons)

    def contain_special_symbol(self, c):
        for var in self.expr.ast.variables:
            if c in var:
                return True
        return False

    def contain_special_symbols(self, syms):
        for var in self.expr.ast.variables:
            for c in syms:
                if c in var:
                    return True
        return False

    def replace(self, subvariable, replacement, re_sim_actions=None, sub_type=None, rep_type=None, rep_info=None, base_ptr=None):
        new_expr = self.expr.replace(subvariable, replacement, re_sim_actions=re_sim_actions, sub_type=sub_type, rep_type=rep_type, rep_info=rep_info, base_ptr=base_ptr)
        new_trace_expr = TraceExpr(new_expr)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()
        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        new_trace_expr.inter_funcs = self.inter_funcs.copy()

        return new_trace_expr

    def replace_with_recurisve_expr(self, subvariable, recurisve_expr, var_type=None):
        count = 0
        _position = None
        base = recurisve_expr.base
        replacement = recurisve_expr.expr.ast
        re_sim_actions = recurisve_expr.expr.sim_actions
        var_type = var_type if var_type else recurisve_expr.expr.var_type
        rep_info = {}
        for var, sim in recurisve_expr.expr.sims.items():
            rep_info[var] = sim.var_type

        base_ptr = recurisve_expr.expr.base_ptr if var_type == 'ptr' else None

        new_expr = self.replace(subvariable, replacement, re_sim_actions=re_sim_actions, rep_type=var_type, rep_info=rep_info, base_ptr=base_ptr)
        new_recur_expr = RecursiveExpr(new_expr.expr)

        for child_ast in new_expr.expr.ast.recursive_children_asts:
            count += 1
            if child_ast.__hash__() == base.__hash__():
                _position = count
                break

        if _position:
            new_recur_expr.position = _position
        else:
            l.info("Not find base position in new expr %s" % (new_recur_expr))

        new_recur_expr.offset = recurisve_expr.offset
        new_recur_expr.base = base
        new_recur_expr.forward_path = self.forward_path.copy()
        new_recur_expr.backward_path = self.backward_path.copy()
        new_recur_expr.cycle_locs = self.cycle_locs
        new_recur_expr.guard = self.guard
        new_recur_expr.constraints = self.constraints.copy()
        new_recur_expr.cons_ids = self.cons_ids.copy()
        new_recur_expr.loop_num = self.loop_num
        new_recur_expr.inter_icall_level = self.inter_icall_level
        new_recur_expr.taint_propagaton_level = self.taint_propagaton_level
        new_recur_expr.inter_funcs = self.inter_funcs.copy()

        return new_recur_expr

    def simple_replace(self, subvariable, replacement):
        self.expr.simple_replace(subvariable, replacement)

    def is_ast_equal(self, other):
        return self.expr.is_ast_equal(other.expr)

    def make_backward_copy(self):
        new_expr = self.expr.make_backward_copy()
        new_trace_expr = TraceExpr(new_expr, self.index)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs.copy()
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()
        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        new_trace_expr.inter_funcs = self.inter_funcs.copy()

        return new_trace_expr

    def make_forward_copy(self):
        new_expr = self.expr.make_forward_copy()
        new_trace_expr = TraceExpr(new_expr, self.index)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs.copy()
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()
        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        new_trace_expr.inter_funcs = self.inter_funcs.copy()

        return new_trace_expr

    def copy_sim_and_action(self):
        sim_actions = self.expr.sim_actions
        self.expr.sim_actions = {}
        for i, sim_action in sim_actions.items():
            self.expr.sim_actions[i] = sim_action.copy()


    def could_forward(self):
        if (self.expr.data_type == 'Aptr' and
                self.expr.value.op == 'Store' and
                self.expr.ast.op not in ['BVS', 'Load']):
            return False
        return True

    def get_trace_variable(self, killed_vars=set()):
        self.expr.get_trace_variable(killed_vars)

    def get_trace_symbols(self):
        return self.expr.get_trace_symbols()

    def contain_argument_ptr(self, arguments=None):
        return self.expr.contain_argument_ptr(arguments)

    def contain_argument_or_global(self, arguments=None):
        return self.expr.contain_argument_or_global(arguments)

    def only_contain_global(self):
        return self.expr.only_contain_global()

    def only_contain_argument(self, arguments=None):
        return self.expr.only_contain_argument(arguments)

    def argument_or_global(self, arguments=None):
        return self.expr.argument_or_global(arguments)

    def contain_symbol(self, symbol):
        """
        The expr whether contian some symbol, example ('t', 'r')
        :return bool
        """
        return self.expr.contain_symbol(symbol)

    def stack_def_expr_dir(self, sp_name):
        return self.expr.stack_def_expr_dir(sp_name)

    def is_stack_expr(self, sp_name):
        """
        The varialbe that allocated in stack.
        for example: deref(sp + offset)
        note: the expr deref(deref(sp+ofset) + offset) is not a stack variable.
        """
        return self.expr.is_stack_expr(sp_name)

    def parse_vex_data(self, data, ptr_sym):
        return self.expr.parse_vex_data(data, ptr_sym)

    def create_sim_action(self, action_data, def_loc=None, var_type=None, live=True):
        all_deref_info = get_all_deref_info(action_data)
        deref_info = all_deref_info[0]

        binop, name, data = deref_info[0], deref_info[1], deref_info[2]
        new_sim_action = SimAction(name, binop, data, var_type=var_type, live=live)
        if def_loc:
            new_sim_action.def_locs.add(def_loc)

        return new_sim_action

    def create_sim_actions(self, action_data, def_loc=None, var_type=None):
        new_sim_actions = {}
        all_deref_info = get_all_deref_info(action_data)
        for i, deref_info in all_deref_info.items():
            binop, name, data = deref_info[0], deref_info[1], deref_info[2]
            new_sim_action = SimAction(name, binop, data)
            new_sim_action.def_locs.add(def_loc)
            if var_type:
                new_sim_action.var_type = var_type

            new_sim_actions[i] = new_sim_action

        return new_sim_actions

class VarExpr(object):
    """
    A VarExpr represents a AST expression that describe a variable.
    """

    def __init__(self, ast, value=None, pattern=None, trace_dir=None, data_type=None, var_type=None, base_ptr=None):

        self.ast = ast
        self.value = value
        self.pattern = pattern
        self.trace_dir = trace_dir  # Lable the variable expr trace by forward or backward.
        self.var_type=var_type  # THe trace variable expression's type. (int, char, ptr, etc.)
        self.data_type = data_type  # The trace data type, include Vptr/Iptr/Fptr/Dptr/Ret etc.

        # Each 'base + offset' expr has a root base pointer (e.g. reg, global, stack ...)
        self.base_ptr = base_ptr
        self.scope = None

        # Label and record the different ID.
        self.alias_id = 0  # Update in different calling chains
        self.alias_ids = set()  # Contain different alias_id for expr merge
        self.invariant_loc = 0  # The invariant id, label the source of expr
        self.invariant_locs = set()  # Contain different invariant_loc for expr merge
        self.ptr_id = 0  # an uniquely tagged of a pointer
        self.taint_id = 0  # Label the taint context id.

        """
        cons_type=1: inet_pton / cons_type=2: strcmp / cons_type=3: copy function's length
        cons_type=4: atoi / cons_type=5: strlen / cons_type=6: tainted data (char, int, long)
        cons_type=7: malloc's size argument / cons_type=8: fdopen
        """
        self.cons_type = 0

        self.memory_size = 0

        # Label the live expr's state.
        """
        0x200 : lable the trace_expr is taint with char but not string copy.
        """
        self.flag = 0

        self.sim_actions = {}
        self.sims = {}

        # Record the variable update path.
        self.store_location = []

        self.is_ret = False

        self.source = None  # The trace expr's source location.
        self.taint_live = 0 # Where is the tianted data live.

        # Mark whether a varialbe defintion must occur.
        self.occur = 'may'
        self.loop = False

        # Label taint copy location (e.g. strcpy, system ...)
        self.taint_loc = None

        # Lable the taint source location (e.g. recv, read, ...)
        self.taint_source = 0
        self.taint_sources = set()

    def __repr__(self):
        if self.value is None:
            return '<Expr %s (%s)>' % (self.ast, self.trace_dir)
        else:
            if isinstance(self.value, int):
                return '<Expr %s: 0x%x (%s)>' % (self.ast, self.value, self.trace_dir)
            else:
                return '<Expr %s: %s (%s)>' % (self.ast, self.value, self.trace_dir)

    def __eq__(self, other):
        """
        Check if self is the same as other.
        """
        if isinstance(other, VarExpr) and other.data_type == self.data_type:
            if self.data_type == 'Aptr':
                return self.ast.__hash__() == other.ast.__hash__() and self.alias_id == other.alias_id and self.value.__hash__() == other.value.__hash__()
            else:
                return self.ast.__hash__() == other.ast.__hash__() and self.alias_id == other.alias_id
        return False

    def __hash__(self):
        """
        returns the hash value of self.
        """
        return hash((self.ast.__hash__(), self.alias_id))

    @property
    def iid(self):
        if (self.data_type == 'Vptr' or self.data_type == 'Dptr') and self.value is not None:
            return hash((self.ast.__hash__(), self.alias_id, self.value.__hash__()))
        else:
            return hash((self.ast.__hash__(), self.alias_id))


    #
    # public methods
    #

    def copy(self):
        """
        Make a copy of the VarExpr.
        :return: a copy of the VarExpr instance.
        """
        new_expr = VarExpr.__new__(VarExpr)
        new_expr.ast = self.ast
        new_expr.base_ptr = self.base_ptr
        new_expr.is_ret = self.is_ret
        new_expr.value = self.value
        new_expr.pattern = self.pattern
        new_expr.trace_dir = self.trace_dir
        new_expr.data_type = self.data_type
        new_expr.taint_id = self.taint_id
        new_expr.var_type = self.var_type
        new_expr.store_location = self.store_location[:]
        new_expr.alias_id = self.alias_id
        new_expr.alias_ids = self.alias_ids.copy()
        new_expr.invariant_loc = self.invariant_loc
        new_expr.invariant_locs = self.invariant_locs.copy()
        new_expr.source = self.source
        new_expr.occur = self.occur
        new_expr.loop = self.loop
        new_expr.flag = self.flag
        new_expr.scope = self.scope
        # new_expr.constraints = self.constraints[:]
        # new_expr.cons_ids = self.cons_ids[:]
        new_expr.taint_loc = self.taint_loc
        new_expr.taint_source = self.taint_source
        new_expr.taint_sources = self.taint_sources.copy()
        new_expr.taint_live = self.taint_live
        new_expr.ptr_id = self.ptr_id
        new_expr.cons_type = self.cons_type
        new_expr.memory_size = self.memory_size

        new_expr.sim_actions = {}
        for index, sim_action in self.sim_actions.items():
            new_expr.sim_actions[index] = sim_action.copy()

        new_expr.sims = {}
        for i, sim in self.sims.items():
            if sim is None:
                new_expr.sims[i] = sim

            else:
                new_expr.sims[i] = sim.copy()

        return new_expr

    def initial_sims(self, var_type=None):

        symbols = self.get_trace_symbols()

        for sym in symbols:
            self.sims[sym] = Sim(var_type=var_type)

        for child in self.ast.recursive_leaf_asts:
            if child.op == 'BVV':
                v = child.args[0]
                if get_mem_permission(v) != 'imm':
                    self.sims[v] = Sim(var_type='ptr')

    def initial_sim_actions(self, code_location, var_type=None):
        """
        Initial expr's sim_action.
        """
        deref_info = get_all_deref_info(self.ast)
        if len(deref_info) == 0:
            return

        for index, deref in deref_info.items():
            binop, base_offset, mem_data = deref
            self.add_sim_actions(index, name=base_offset, binop=binop, def_loc=code_location, action_data=mem_data, var_type=var_type)

    def add_sim_actions(self, index, name=None, def_loc=None, binop=None, action_data=None, var_type=None):

        sim_action = SimAction(name=name, binop=binop, action_data=action_data, var_type=var_type)
        sim_action.def_locs.add(def_loc)

        self.sim_actions[index] = sim_action


    def is_ast_equal(self, other):
        if isinstance(other, VarExpr):
            return self.ast.__hash__() == other.ast.__hash__()
        return False

    def make_backward_copy(self):
        new_expr = self.copy()
        new_expr.trace_dir = 'B'
        return new_expr

    def make_forward_copy(self):
        new_expr = self.copy()
        new_expr.trace_dir = 'F'
        return new_expr

    def add_store_action_loc(self, code_location):
        for sim_action in self.sim_actions.values():
            if sim_action.action_data.op == 'Store':
                sim_action.def_locs.add(code_location)

    def kill_store_action_by_loc(self, code_location=None):
        """
        Kill store sim_action's live.
        """
        for sim_action in self.sim_actions.values():
            if sim_action.action_data.op == 'Store':
                if code_location is None:
                    sim_action.live = False
                elif code_location in sim_action.def_locs:
                    sim_action.live = False

    def active_store_action_by_loc(self, code_location=None):
        for sim_action in self.sim_actions.values():
            if sim_action.action_data.op == 'Store':
                if code_location is None:
                    sim_action.live = True
                elif code_location in sim_action.def_locs:
                    sim_action.live = True

    def kill_store_action_in_callsite(self, code_location):
        for sim_action in self.sim_actions.values():
            sim_action.def_locs.add(code_location)
            if sim_action.action_data.op == 'Store':
                sim_action.live = False

    def active_store_action_in_callsite(self, code_location):
        for sim_action in self.sim_actions.values():
            sim_action.def_locs.add(code_location)
            if sim_action.action_data.op == 'Store':
                sim_action.live = True

    def kill_load_action_by_loc(self, code_location=None):
        """
        In load loc, if the trace_expr's trace_dir is 'F', then kill the load sim_action.
        So in forward, if has store re-define and the load's live is False, should kill the load expr.
        However, if the load's live is True, then should update the expr with store definition.
        """
        for sim_action in self.sim_actions.values():
            if (sim_action.action_data.op == 'Load' and (code_location is None or code_location in sim_action.def_locs)):
                sim_action.live = False

    def is_contain_load_ptr(self, ptr):
        if type(ptr) is tuple:
            op, ptr_data = ptr
            for index, sim_action in self.sim_actions.items():
                name = sim_action.name
                action_data = sim_action.action_data
                if name and action_data.op == 'Load' and sim_action.binop == op and name == ptr_data:
                    return True
        else:
            for sim_action in self.sim_actions.values():
                name = sim_action.name
                if name and sim_action.action_data.op == 'Load' and name[0] == ptr:
                    return True
        return False

    def contain_argument_ptr(self, arguments=None):
        """
        Whether expr contain argument pointer?
        """
        for var, sim in self.sims.items():
            if sim.var_type == 'ptr' and type(var) is str and is_arg_symbol(var, arguments):
                return True
        return False

    def contain_argument_or_global(self, arguments=None):
        """
        Whether expr contain argument or global pointer, but not contain stack pointer?
        """
        # stack_flag = False
        context_flag = False
        for var, sim in self.sims.items():
            if ((type(var) is str and is_arg_symbol(var, arguments) or
                     type(var) is int and get_scope(var) == 'global')):
                context_flag = True
            elif type(var) is int and get_scope(var) == 'stack':
                return False
        return context_flag

    def only_contain_global(self):
        """
        Whether expr only contain global pointer?
        """
        for var, sim in self.sims.items():
            if type(var) is str and 'o' not in var:
                return False
        return True

    def only_global(self):
        """
        Whether expr only contain global pointer?
        """
        if type(self.base_ptr) is not int:
            return False

        for var, sim in self.sims.items():
            if type(var) is str and 'o' not in var:
                return False

        if get_scope(self.base_ptr) == 'global':
            return True
        return False

    def only_argument(self, arguments=None):
        """
        Whether expr only contain arguments?
        """
        for var, sim in self.sims.items():
            if type(var) is str and not is_arg_symbol(var, arguments):
                return False

            elif type(var) is int:
                return False
        return True

    def only_contain_argument(self, arguments=None):
        """
        Whether expr only contain arguments?
        """
        for var, sim in self.sims.items():
            if type(var) is str and not is_arg_symbol(var, arguments):
                return False

            elif type(var) is int and get_scope(var) == 'stack':
                return False

        return True

    def argument_or_global(self, arguments=None):
        """
        Judge the expr only contain arguments or global, this expr could push to caller.
        """
        # print(self.sims)
        if len(self.sims) == 0:
            return False

        for var in self.ast.variables:
            if '_' in var:
                return False

        for var, sim in self.sims.items():
            if type(var) is str and not is_arg_symbol(var, arguments):
                return False

            elif type(var) is int and get_scope(var) == 'stack':
                return False

        return True

    def get_trace_variable(self, killed_vars=set()):
        self.trace_vars = set()
        for v in self.ast.variables:
            if v in killed_vars:
                continue
            p = re.match(r'^[srt][\d]+$', v)
            if p:
                self.trace_vars.add(p.string)
        same_vars = [v for v in killed_vars if v in self.ast.variables]
        if len(same_vars):
            self.killed_vars = set(same_vars)
        else:
            self.killed_vars = set()

    def get_trace_symbols(self):
        symbols = set()
        for v in self.ast.variables:
            p = re.match(r'^[srt][\d]+$', v)
            if p:
                symbols.add(p.string)

        return symbols


    def replace(self, subvariable, replacement, re_sim_actions=None, sub_type=None, rep_type=None, rep_info=None, base_ptr=None):
        """
        Use replacement to replace subvariable in expr.
        param: subvariable, type is [str, BV]
        param: replacement, type is [int, str, BV]
        """
        # print("update: %s" % (self))
        # print("with sims: %s" % (self.sims))
        # print("replace: %s %s" % (subvariable, replacement))
        if isinstance(subvariable, str):
            if sub_type is None:
                sub_type = self.sims[subvariable].var_type

            for leaf_data in self.ast.recursive_leaf_asts:
                if subvariable in leaf_data.variables:
                    subvariable = leaf_data
                    break

        elif isinstance(subvariable, int):
            if sub_type is None:
                sub_type = self.sims[subvariable].var_type

            for leaf_data in self.ast.recursive_leaf_asts:
                if leaf_data.op == 'BVV' and leaf_data.args[0] == subvariable:
                    subvariable = leaf_data
                    break

        # print("subvariable: %s" % (subvariable))
        if isinstance(replacement, str):
            replacement = claripy.BVS(replacement, subvariable.size(), explicit_name=True)

        elif isinstance(replacement, int):
            replacement = claripy.BVV(replacement, subvariable.size())

        # print(subvariable, replacement, replacement.op)
        # print(subvariable.size(), replacement.size())
        sub_size = subvariable.size()
        rep_size = replacement.size()
        if sub_size != rep_size:
            if replacement.op == 'BVS':
                replacement = claripy.BVS(replacement.args[0], sub_size, explicit_name=True)

            elif replacement.op == 'BVV':
                replacement = claripy.BVV(replacement.args[0], sub_size)

            else:
                if rep_size > sub_size:
                    replacement = claripy.Extract(sub_size-1, 0, replacement)
                else:
                    replacement = claripy.ZeroExt(sub_size-rep_size, replacement)

        new_data = self.ast.replace(subvariable, replacement)
        new_expr = VarExpr(new_data)
        new_expr.value = self.value
        new_expr.pattern = self.pattern
        new_expr.data_type = self.data_type
        new_expr.var_type = self.var_type
        new_expr.store_location = self.store_location[:]
        new_expr.alias_id = self.alias_id
        new_expr.alias_ids = self.alias_ids
        new_expr.invariant_loc = self.invariant_loc
        new_expr.invariant_locs = self.invariant_locs
        new_expr.taint_id = self.taint_id
        new_expr.source = self.source
        new_expr.is_ret = self.is_ret
        new_expr.loop = self.loop
        new_expr.flag = self.flag
        # new_expr.constraints = self.constraints[:]
        # new_expr.cons_ids = self.cons_ids[:]
        new_expr.taint_loc = self.taint_loc
        new_expr.taint_source = self.taint_source
        new_expr.taint_sources = self.taint_sources.copy()
        new_expr.taint_live = self.taint_live
        new_expr.ptr_id = self.ptr_id
        new_expr.cons_type = self.cons_type
        new_expr.memory_size = self.memory_size

        new_expr.update_sims(self)
        new_expr.update_sim_actions(self, subvariable, replacement, re_sim_actions=re_sim_actions)

        new_expr.update_var_type(subvariable, replacement, sub_type, rep_type, rep_info)
        # print("update sims: %s" % (new_expr.sims))

        # print("update_b base_ptr: %s" % (self.base_ptr))
        if self.base_ptr is None:
            new_expr.base_ptr = get_expr_base_ptr(new_expr)

        elif self.base_is_change(subvariable):
            # print("base-1")
            if base_ptr is None:
                new_expr.update_base_ptr(self.base_ptr, subvariable, replacement, re_sim_actions, rep_info)
            else:
                new_expr.base_ptr = base_ptr
        else:
            # print("base-2")
            new_expr.base_ptr = self.base_ptr
        # print("update_f base_ptr: %s" % (new_expr.base_ptr))

        return new_expr

    def update_base_ptr(self, old_base_ptr, subvariable, replacement, re_sim_actions, rep_info):
        """
        Update expr's base pointer.
        """
        if (type(old_base_ptr) is str and subvariable.op == 'BVS' and
                old_base_ptr == subvariable.args[0]):
            self.base_ptr = self.get_base_ptr_v1(replacement, re_sim_actions, rep_info)

        elif (type(old_base_ptr) is int and subvariable.op == 'BVV' and
                old_base_ptr == subvariable.args[0]):
            self.base_ptr = self.get_base_ptr_v1(replacement, re_sim_actions, rep_info)

        else:
            self.base_ptr = get_expr_base_ptr(self)

    def base_is_change(self, subvariable):
        for leaf_ast in subvariable.recursive_leaf_asts:
            if leaf_ast.args[0] == self.base_ptr:
                return True
        return False

    def get_base_ptr_v1(self, replacement, re_sim_actions, rep_info):

        def get_ptr(var_info):
            if var_info is None:
                return None

            for var, ty in var_info.items():
                if ty == 'ptr':
                    return var
            return None

        base_ptr = None
        if replacement.op == 'BVS':
            base_ptr = replacement.args[0]

        elif replacement.op == 'BVV':
            base_ptr = replacement.args[0]
            if base_ptr not in self.sims:
                base_ptr = get_expr_base_ptr(self)

        elif replacement.op in ['Load', 'Store'] and len(re_sim_actions) == 1:
            if replacement.args[0].op == 'BVV':
                base_ptr = replacement.args[0].args[0]

            else:
                base_ptr = get_ptr(rep_info)

        elif re_sim_actions is None:
            base_ptr = get_ptr(rep_info)

        return base_ptr

    def update_var_type(self, subvariable, replacement, sub_type, rep_type, rep_info):
        """
        When update a var expression, each sub varialbe in expression should update its var_type.
        """
        if replacement.op in ['BVV', 'BVS']:
            rep_var = replacement.args[0]
            if rep_var in self.sims:
                self.sims[rep_var].var_type = sub_type if sub_type else rep_type

        elif rep_info:
            for v, vtype in rep_info.items():
                if v in self.sims:
                    self.sims[v].var_type = vtype

    # TODO How to merge old_expr and new_expr's sims?
    def update_sims(self, old_expr=None):

        def add_sim_v1(s, new_sims, old_sims):
            if s not in old_sims:
                new_sims[s] = Sim()
            else:
                new_sims[s] = old_sims[s]

        def add_sim_v2(v, new_sims, old_sims, var_type):
            if v not in old_sims:
                new_sims[v] = Sim(var_type=var_type)
            else:
                new_sims[v] = old_sims[v]
                new_sims[v].var_type = var_type

        trace_vs = set()
        old_sims = old_expr.sims if old_expr else {}
        self.sims = {}
        new_sims = self.sims

        # print("update sims before: %s" % (new_sims))
        for child in self.ast.recursive_leaf_asts:
            if child.op == 'BVS':
                sym = child.args[0]
                p = re.match(r'^[srt][\d]+$', sym)
                if p and p.string not in trace_vs:
                    s = p.string
                    trace_vs.add(s)
                    add_sim_v1(s, new_sims, old_sims)

            elif child.op == 'BVV':
                v = child.args[0]
                if v not in trace_vs:
                    trace_vs.add(v)
                    if get_mem_permission(v) != 'imm':
                        var_type = 'ptr'
                        add_sim_v2(v, new_sims, old_sims, var_type)

    def initialize_sim_actions(self, def_loc, var_type=None):
        """
        Initialize expr's sim_actions.
        """
        all_deref_info = get_all_deref_info(self.ast)

        for i, deref_info in all_deref_info.items():
            if deref_info is None:
                new_sim_action = SimAction()
                new_sim_action.var_type = var_type
                new_sim_action.def_locs.add(def_loc)
                self.sim_actions[i] = new_sim_action

            else:
                binop, name, data = deref_info[0], deref_info[1], deref_info[2]
                new_sim_action = SimAction(name, binop, data)
                new_sim_action.var_type = var_type
                new_sim_action.def_locs.add(def_loc)
                self.sim_actions[i] = new_sim_action

        self.merge_sim_actions()

    def merge_sim_actions(self):
        """
        Merge the same load sim_actions with same name.
        """
        same_actions = {}
        remove_actions = []

        for index, sim_action in self.sim_actions.items():
            name = sim_action.name

            if name is not None and name[0]:
                if name in same_actions:
                    pre_sim_action = same_actions[name]
                    for loc in sim_action.def_locs:
                        pre_sim_action.def_locs.add(loc)
                    remove_actions.append(index)

                else:
                    same_actions[name] = sim_action

        for index in remove_actions:
            self.sim_actions.pop(index)

    def update_sim_actions(self, old_expr, subvariable, replacement, re_sim_actions=None):
        """
        update self sim_actions with old expr's sim_actions.
        """
        same_actions = {}
        old_sim_actions = old_expr.sim_actions
        new_sim_actions = self.sim_actions

        # print("old sim actions: %s" % (old_sim_actions))
        # print("new sim actions: %s" % (new_sim_actions))
        # print("subvar: %s, replacevar: %s" % (subvariable, replacement))
        # print("replacement sim actoins: %s" % (re_sim_actions))

        old_ast = old_expr.ast
        changed_ls_indexs, child_indexs = get_index_info_with_child_ast(old_ast, subvariable)

        sub_indexs = get_ls_indexs(subvariable)
        rep_indexs = get_ls_indexs(replacement)

        if len(rep_indexs) and re_sim_actions is None:
            raise UpdateSimActionsError

        elif len(rep_indexs) == 0:
            re_sim_actions = {}

        shines, new_indexs = self._action_shines(old_sim_actions, changed_ls_indexs, child_indexs, sub_indexs, rep_indexs)

        all_deref_info = get_all_deref_info(self.ast)
        # print("new ast %s has:\n deref info: %s" % (self.ast, all_deref_info))

        for old_i, old_sim_action in old_sim_actions.items():
            if old_i not in shines:
                continue

            new_i = shines[old_i]
            old_name = old_sim_action.name
            new_info = all_deref_info[new_i]

            if new_info[1] is None:
                # if old_name is None:
                #     new_sim_actions[new_i] = old_sim_action

                # else:
                new_sim_action = SimAction(action_data=new_info[2], var_type=old_sim_action.var_type)
                new_sim_action.live = old_sim_action.live
                for loc in old_sim_action.def_locs:
                    new_sim_action.def_locs.add(loc)
                new_sim_actions[new_i] = new_sim_action

            else:
                new_name = new_info[1]
                if old_name == new_name and new_name[0]:
                    new_sim_actions[new_i] = old_sim_action

                else:
                    binop = new_info[0]
                    data = new_info[2]
                    new_sim_actions[new_i] = self._create_sim_action(new_name, binop, data, def_locs=old_sim_action.def_locs, live=old_sim_action.live, var_type=old_sim_action.var_type)

        for new_i in new_indexs:
            for ri in rep_indexs:
                if ri in re_sim_actions:
                    new_sim_actions[new_i+ri] = re_sim_actions[ri]

        self.merge_sim_actions()
        # print("new sim_actions: %s" % (new_sim_actions))

    def _create_sim_action(self, name, binop, data, def_locs=None, live=True, var_type=None):

        new_sim_action = SimAction(name, binop, data, var_type=var_type)
        new_sim_action.live = live
        if def_locs is not None:
            for loc in def_locs:
                new_sim_action.def_locs.add(loc)

        # print("action: %s" % (new_sim_action.name))
        return new_sim_action

    def _action_shines(self, old_sim_actions, changed_ls_indexs, child_indexs, sub_indexs, rep_indexs):
        """
        calcurate the shines between expr's sim_actions update before and after.
        """

        sub_len, rep_len = len(sub_indexs), len(rep_indexs)
        shines, new_indexs = {}, []
        tmp_indexs = []
        pos, c = 0, 0

        # print(changed_ls_indexs, child_indexs, sub_indexs, rep_indexs)

        # Case 1: rdi -> rsi
        if sub_len == 0 and rep_len == 0:
            # print("1")
            # sim_actions not changed!
            for i in old_sim_actions:
                shines[i] = i

        # Case 2: rdi -> load(rsi + 0x80)
        elif sub_len == 0 and rep_len > 0:
            # print("2")
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
                    # shines.append((old_i, shine_old_i))
                    shines[old_i] = shine_old_i

        # Case 3: load(rsi + 0x80) -> rdi
        elif sub_len > 0 and rep_len == 0:
            # print("3")
            # sim_actions changed, remove!
            for i in changed_ls_indexs:
                if i in tmp_indexs:
                    continue

                if i in child_indexs:
                    c += sub_len
                    tmp_indexs = [i+j for j in sub_indexs]

                else:
                    new_i = i - c
                    # shines.append((i, new_i))
                    shines[i] = new_i

        # Case 4: store(rsp + 0x24) -> load(rdi + 0x20)
        elif sub_len > 0 and sub_len == rep_len:
            # print("4")
            # sim_actions changed, but index not chane!
            for i in changed_ls_indexs:
                if i in tmp_indexs:
                    continue

                if i in child_indexs:
                    new_indexs.append(i)
                    tmp_indexs = [i+j for j in sub_indexs]

                else:
                    # shines.append((i, i))
                    shines[i] = i

        # Case 5: load(xxx) -> store(load(xxx))
        elif sub_len > 0 and rep_len > sub_len:
            # sim_actions changed, add!
            # print("5")
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
                    # shines.append((old_i, shine_old_i))
                    shines[old_i] = shine_old_i

        # Case 6: load(load(xxx)) -> load(xxx)
        elif sub_len > 0 and rep_len < sub_len:
            # print("6")
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
                    # shines.append((i, new_i))
                    shines[i] = new_i

        # print("shines: %s" % (shines))
        # print("new indexs: %s" % (new_indexs))
        for ni in new_indexs:
            add_indexs = [ni+j for j in rep_indexs]
            # print("add indexs: %s" % (add_indexs))

        return shines, new_indexs

    def simple_replace(self, subvariable, replacement):
        """
        Use replacement to replace subvariable in expr.
        param: subvariable, type is [str, BV]
        param: replacement, type is [str, BV]
        """
        if isinstance(subvariable, str):
            for leaf_data in self.ast.recursive_leaf_asts:
                if subvariable in leaf_data.variables:
                    subvariable = leaf_data
                    break

        if isinstance(replacement, str):
            replacement = claripy.BVS(replacement, subvariable.size(), explicit_name=True)

        if subvariable.size() != replacement.size():
            l.info("Variable expr replace error, the size different.")
            return

        new_data = self.ast.replace(subvariable, replacement)
        self.ast = new_data

    def contain_symbol(self, symbol):
        """
        The expr whether contian some symbol, example ('t', 'r')
        :return bool
        """
        for var in self.sims:
            if type(var) is str and symbol in var:
                return True
        return False

    def stack_def_expr_dir(self, sp_name):
        data = self.ast
        if self.pattern == 'Cptr':
            return 'B'
        if sp_name not in self.sims:
            # print("%s not a stack expr!" % (self))
            return None
        if data.op != 'Load':
            print("Error, %s not a def!" % (self))
            return None
        for child_data in data.recursive_children_asts:
            if child_data.op == 'Load':
                return 'N'
        return 'F'

    def is_stack_expr(self, sp_name):
        """
        The varialbe that allocated in stack.
        for example: deref(sp + offset)
        note: the expr deref(deref(sp+ofset) + offset) is not a stack variable.
        """
        data = self.ast
        if sp_name not in self.sims or data.op != 'Load':
            return False
        for child_data in data.recursive_children_asts:
            if child_data.op == 'Load':
                return False
        return True

    def parse_vex_data(self, data, ptr_sym):
        ptr_info = {}
        sub_datas = []
        if data.op == 'BVS':
            return ptr_info

        elif data.op == 'Load':
            sub_datas.append(data)

        for child in data.recursive_children_asts:
            if child.op == 'Load':
                sub_datas.append(child)

        for sub_data in sub_datas:
            addr = sub_data.args[0]
            if addr.op == 'BVS':
                v = addr.args[0]
                if v == ptr_sym:
                    ptr_info[0] = sub_data
            elif addr.op == 'BVV':
                v = addr.args[0]
                if ptr_sym == 'concrete':
                    ptr_info[v] = sub_data
            else:
                if len(addr.args) == 2:
                    try:
                        if addr.args[0].op == 'BVS' and addr.args[1].concrete:
                            v = addr.args[0].args[0]
                            offset = addr.args[1].args[0]
                            if v == ptr_sym:
                                ptr_info[offset] = sub_data
                        elif addr.args[1].op == 'BVS' and addr.args[0].concrete:
                            v = addr.args[1].args[0]
                            offset = addr.args[0].args[0]
                            if v == ptr_sym:
                                ptr_info[offset] = sub_data
                    except:
                        print("The are error while parse variable %s" % (data))
        return ptr_info


class RecursiveExpr(TraceExpr):
    def __init__(self, expr, index=None, base=None, offset=None, position=None):

        super(RecursiveExpr, self).__init__(expr, index=index)

        self.base = base
        self.offset = offset
        self.position = position

        self.inc_records = []

    # def __repr__(self):
    #     if self.expr.value is None:
    #         return '<R-Expr %s (%s) (%s)>' % (self.expr.ast, self.expr.base_ptr, self.expr.trace_dir)
    #     else:
    #         if isinstance(self.expr.value, int):
    #             return '<R-Expr %s: 0x%x (%s) (%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.trace_dir)
    #         else:
    #             return '<R-Expr %s: %s (%s) (%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.trace_dir)

    def __repr__(self):
        if self.expr.value is None:
            return '<R-Expr %s (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.base_ptr, self.expr.var_type, self.expr.trace_dir, self.index)
        else:
            if isinstance(self.expr.value, int):
                return '<R-Expr %s: 0x%x (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.var_type,  self.expr.trace_dir, self.index)
            else:
                return '<R-Expr %s: %s (%s) (%s) (%s-%s)>' % (self.expr.ast, self.expr.value, self.expr.base_ptr, self.expr.var_type, self.expr.trace_dir, self.index)


    def __eq__(self, other):
        if isinstance(other, RecursiveExpr):
            return self.expr == other.expr
        return False

    def __hash__(self):
        """
        returns the hash value of self.
        """
        return self.expr.__hash__()

    def deep_copy(self):
        new_recursive_expr = RecursiveExpr.__new__(RecursiveExpr)
        new_recursive_expr.__init__(self.expr.copy(), index=self.index)

        new_recursive_expr.forward_path = self.forward_path.copy()
        new_recursive_expr.backward_path = self.backward_path.copy()
        new_recursive_expr.inc_records = self.inc_records
        new_recursive_expr.cycle_locs = self.cycle_locs
        new_recursive_expr.guard = self.guard
        new_recursive_expr.constraints = self.constraints.copy()
        new_recursive_expr.cons_ids = self.cons_ids.copy()

        new_recursive_expr.loop_num = self.loop_num
        new_recursive_expr.inter_funcs = self.inter_funcs.copy()
        new_recursive_expr.inter_icall_level = self.inter_icall_level
        new_recursive_expr.taint_propagaton_level = self.taint_propagaton_level

        new_recursive_expr.base = self.base
        new_recursive_expr.offset = self.offset
        new_recursive_expr.position = self.position
        new_recursive_expr.inc_records = self.inc_records[:]
        return new_recursive_expr

    def copy(self):
        new_recursive_expr = RecursiveExpr.__new__(RecursiveExpr)
        new_recursive_expr.__init__(self.expr, index=self.index)

        new_recursive_expr.forward_path = self.forward_path.copy()
        new_recursive_expr.backward_path = self.backward_path.copy()
        new_recursive_expr.inc_records = self.inc_records
        new_recursive_expr.cycle_locs = self.cycle_locs
        new_recursive_expr.guard = self.guard
        new_recursive_expr.constraints = self.constraints.copy()
        new_recursive_expr.cons_ids = self.cons_ids.copy()

        new_recursive_expr.loop_num = self.loop_num
        new_recursive_expr.inter_funcs = self.inter_funcs.copy()
        new_recursive_expr.inter_icall_level = self.inter_icall_level
        new_recursive_expr.taint_propagaton_level = self.taint_propagaton_level

        new_recursive_expr.base = self.base
        new_recursive_expr.offset = self.offset
        new_recursive_expr.position = self.position
        new_recursive_expr.inc_records = self.inc_records
        return new_recursive_expr

    def get_recursive_base_positon(self):
        count, position = 0, 0
        base_hash = self.base.__hash__()
        for child_ast in self.expr.ast.recursive_children_asts:
            count += 1
            if child_ast.__hash__() == base_hash:
                position = count
                break

        # if position == 0:
        #     raise Exception("Not find base %s in %s" % (self.base, self))

        return position

    def replace(self, subvariable, replacement, re_sim_actions=None, sub_type=None, rep_type=None, rep_info=None, base_ptr=None):
        new_expr = self.expr.replace(subvariable, replacement, re_sim_actions=re_sim_actions, sub_type=sub_type, rep_type=rep_type, rep_info=rep_info)
        new_recursive_expr = RecursiveExpr(new_expr)
        count = 0
        new_base = None
        # l.info("test expr %s, position " % (self))
        for child_ast in new_expr.ast.recursive_children_asts:
            count += 1
            if count == self.position:
                new_base = child_ast
                break
        if new_base is not None:
            new_recursive_expr.base = new_base
        else:
            l.debug("Not find new base in new expr %s" % (new_expr))
            new_recursive_expr.base = self.base

        new_recursive_expr.offset = self.offset
        new_recursive_expr.position = self.position
        new_recursive_expr.forward_path = self.forward_path.copy()
        new_recursive_expr.backward_path = self.backward_path.copy()
        new_recursive_expr.inc_records = self.inc_records
        new_recursive_expr.cycle_locs = self.cycle_locs
        new_recursive_expr.guard = self.guard
        new_recursive_expr.constraints = self.constraints.copy()
        new_recursive_expr.cons_ids = self.cons_ids.copy()

        new_recursive_expr.loop_num = self.loop_num
        new_recursive_expr.inter_funcs = self.inter_funcs.copy()
        new_recursive_expr.inter_icall_level = self.inter_icall_level
        new_recursive_expr.taint_propagaton_level = self.taint_propagaton_level

        return new_recursive_expr

    def replace_v2(self, subvariable, replacement, re_sim_actions=None, sub_type=None, rep_type=None, rep_info=None, base_ptr=None):
        new_expr = self.expr.replace(subvariable, replacement, re_sim_actions=re_sim_actions, sub_type=sub_type, rep_type=rep_type, rep_info=rep_info)
        new_trace_expr = TraceExpr(new_expr)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()

        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_funcs = self.inter_funcs.copy()
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level

        return new_trace_expr

    def make_backward_copy(self):
        new_expr = self.expr.make_backward_copy()
        new_trace_expr = RecursiveExpr(new_expr, index=self.index, base=self.base, offset=self.offset, position=self.position)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()

        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_funcs = self.inter_funcs.copy()
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        return new_trace_expr

    def make_forward_copy(self):
        new_expr = self.expr.make_forward_copy()
        new_trace_expr = RecursiveExpr(new_expr, index=self.index, base=self.base, offset=self.offset, position=self.position)
        new_trace_expr.forward_path = self.forward_path.copy()
        new_trace_expr.backward_path = self.backward_path.copy()
        new_trace_expr.cycle_locs = self.cycle_locs
        new_trace_expr.guard = self.guard
        new_trace_expr.constraints = self.constraints.copy()
        new_trace_expr.cons_ids = self.cons_ids.copy()

        new_trace_expr.loop_num = self.loop_num
        new_trace_expr.inter_funcs = self.inter_funcs.copy()
        new_trace_expr.inter_icall_level = self.inter_icall_level
        new_trace_expr.taint_propagaton_level = self.taint_propagaton_level
        return new_trace_expr

    def with_same_inc_info(self, base, offset):
        if self.base is not None and base is not None and self.base.__hash__() == base.__hash__():
            if self.offset is None and offset is None:
                return True

            elif self.offset is not None and offset is not None and self.offset.__hash__() == offset.__hash__():
                return True
        return False

    def is_update_base(self, base_var):
        if self.base.op == 'BVS' and base_var in self.base.variables:
            return True
        return False



def construct_trace_expr(ast, value=None,
                         pattern=None,
                         data_type=None,
                         trace_dir=None,
                         var_type=None,
                         index=None,
                         code_location=None,
                         block_addr=None,
                         stmt_idx=None,
                         base_ptr=None):
    """
    Create a new trace expr.
    """
    expr = VarExpr(ast, value=value, pattern=pattern, trace_dir=trace_dir, data_type=data_type, var_type=var_type, base_ptr=base_ptr)

    if code_location is None and block_addr is None:
        raise Exception("The code_location and block_addr can not be None in same time.")

    code_location = CodeLocation(block_addr, stmt_idx) if code_location is None else code_location
    eid = code_location.__hash__()
    expr.alias_id = eid
    expr.invariant_loc = code_location
    expr.source = code_location
    # ALL_SOURCES[expr.alias_id] = code_location

    expr.initial_sims(var_type=var_type)
    expr.initial_sim_actions(code_location, var_type=var_type)

    trace_expr = TraceExpr(expr, index=index)

    return trace_expr
