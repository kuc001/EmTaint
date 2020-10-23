import claripy
import dataflow
from dataflow.parse_ast import BVV, BVS, get_value

class hsearch_r(dataflow.SimProcedure):
    """
    int hsearch_r(ENTRY item, ACTION action, ENTRY **retval, struct hsearch_data *htab)
    """

    def run(self, key, data, act, retptr, htab):
        # print("run hsearch_r")
        act_value = get_value(self.block, act)
        if act_value == 0 and self.flow_dir == 'F' and self.purpose == 0:
            self.find_data(retptr, htab)
        elif act_value == 1 and self.flow_dir == 'F' and self.purpose == 0:
            self.insert_data(key, data, htab)
        return 1

    def infer_type(self, key, data, act, retptr, htab):
        self.label_variable_type(key, 'ptr')
        self.label_variable_type(data, 'ptr')
        self.label_variable_type(act, 'N')
        self.label_variable_type(retptr, 'ptr')
        self.label_variable_type(htab, 'ptr')
        self.label_return_type('N')

    def find_data(self, retptr, htab):
        """
        Find a data by the key from the hash table.
        <BV32 Store(Load(htab) + o)>
        """
        def find_htab_taint(taint_ast):
            if taint_ast.op == 'Store':
                s_addr_ast = taint_ast.args[0]
                if len(s_addr_ast.args) == 2:
                    ptr_ast = s_addr_ast.args[0]
                    offset_ast = s_addr_ast.args[1]
                    if ptr_ast.op == 'Load' and offset_ast.op == 'BVS' and 'o' in offset_ast.args[0]:
                        return True
            return False

        def create_hsearch_return(retptr):
            ret_ast = BVS(retptr)
            ret_ast = claripy.Store(ret_ast, ret_ast.size())
            ret_ast = claripy.Store(ret_ast + BVV(0x4, ret_ast.size()), ret_ast.size())
            return ret_ast

        print("Find-data-in-hashTable: %s" % (self.block))
        result_expr = None
        if 's' in htab:
            htab_ptr = self.get_stack_arg_ptr(htab)
        else:
            htab_ptr = htab

        for trace_expr in self.block.forward_exprs:
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast

            if htab_ptr == trace_expr.expr.base_ptr and find_htab_taint(trace_ast):
                taint_ast = create_hsearch_return(retptr)
                print("Found-hsearch-tainted--> %s\n -->with ret: %s" % (trace_expr, taint_ast))
                result_expr = self.generate_ret_taint_expr(taint_ast, retptr, trace_expr)
                break

        if result_expr is None:
            return

        for pre_block in self.block.predecessors:
            result_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            result_expr.expr.kill_store_action_by_loc(result_expr.expr.source)
            result_expr.expr.flag &= 0xfeff
            result_expr.taint_propagaton_level += 1
            pre_block.backward_exprs.append(result_expr)

    def insert_data(self, key, data, htab):
        """
        Insert a key:data to the hash table.
        """
        def create_hsearch_htab(htab_ptr):
            if type(htab_ptr) is int:
                ast = BVV(htab_ptr)
                data_ast = claripy.Load(ast, ast.size())
            else:
                data_ast = BVS(htab_ptr)
            data_ast = claripy.Load(data_ast, data_ast.size())
            offset = BVS('o')
            data_ast = claripy.Store(data_ast+offset, data_ast.size())
            return data_ast

        print("Insert-data-in-hashTable: %s" % (self.block))
        taint_expr = None
        for trace_expr in self.block.forward_exprs:
            trace_sims = trace_expr.expr.sims
            trace_ast = trace_expr.expr.ast
            if data in trace_sims and trace_ast.op == 'BVS':
                # print("Hast-table is tainted! %s" % (htab))
                if 's' in htab:
                    htab_ptr = self.get_stack_arg_ptr(htab)
                else:
                    htab_ptr = htab

                if htab_ptr:
                    taint_ast = create_hsearch_htab(htab_ptr)
                    taint_expr = self.generate_htab_taint_expr(taint_ast, htab_ptr, trace_expr)
                    break
                    # tainted_exprs.append(taint_expr)
                    # if type(stack_addr) is not int:
                    #     taint_expr = self.generate_htab_taint_expr(stack_addr, trace_expr)
                    #     tainted_exprs.append(taint_expr)
                # else:
                    # taint_ast =

        if taint_expr is None:
            return

        for pre_block in self.block.predecessors:
            # for taint_expr in tainted_exprs:
            taint_expr.index = len(pre_block.irsb.statements) if pre_block.irsb else 0
            taint_expr.expr.kill_store_action_by_loc(taint_expr.expr.source)
            taint_expr.expr.flag &= 0xfeff
            taint_expr.taint_propagaton_level += 1
            pre_block.backward_exprs.append(taint_expr)

    def generate_htab_taint_expr(self, taint_ast, stack_addr, trace_expr):
        # ast = BVV(stack_addr)
        # data_ast = claripy.Load(ast, ast.size())
        # data_ast = claripy.Load(data_ast, data_ast.size())
        # offset = BVS('o')
        # data_ast = claripy.Store(data_ast+offset, data_ast.size())
        # print("Get-htab-tained: %s" % (data_ast))
        code_location = trace_expr.expr.source.copy()
        code_location.block_addr = self.block.addr
        code_location.stmt_idx = 0
        new_expr = trace_expr.deep_copy()
        new_expr.expr.ast = taint_ast
        new_expr.expr.base_ptr = stack_addr
        new_expr.expr.scope = 'stack'
        new_expr.expr.source = code_location
        new_expr.expr.trace_dir = 'B'
        # new_expr.expr.taint_loc = self.block.addr
        new_expr.expr.ptr_id = self.block.addr
        new_expr.expr.sim_actions = {}
        new_expr.expr.sims = {}
        new_expr.expr.initial_sims(var_type='ptr')
        new_expr.expr.initial_sim_actions(code_location, var_type='ptr')
        print("Htab-expr: %s" % (new_expr))
        for i, sim_action in new_expr.expr.sim_actions.items():
            print(i, sim_action)
        for i, sim in new_expr.expr.sims.items():
            print(i, sim)
        return new_expr

    def generate_ret_taint_expr(self, taint_ast, retptr, trace_expr):
        code_location = trace_expr.expr.source.copy()
        code_location.block_addr = self.block.addr
        code_location.stmt_idx = 0
        new_expr = trace_expr.deep_copy()
        new_expr.expr.ast = taint_ast
        new_expr.expr.base_ptr = retptr
        new_expr.expr.scope = 'aptr'
        new_expr.expr.source = code_location
        new_expr.expr.trace_dir = 'B'
        # new_expr.expr.taint_loc = self.block.addr
        new_expr.expr.ptr_id = self.block.addr
        new_expr.expr.sim_actions = {}
        new_expr.expr.sims = {}
        new_expr.expr.initial_sims(var_type='ptr')
        new_expr.expr.initial_sim_actions(code_location, var_type='ptr')
        print("Hsearch-ret-expr: %s" % (new_expr))
        for i, sim_action in new_expr.expr.sim_actions.items():
            print(i, sim_action)
        for i, sim in new_expr.expr.sims.items():
            print(i, sim)
        return new_expr
