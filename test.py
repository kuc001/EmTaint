# import angr
# import claripy
# from variable_expression import TraceExpr, VarExpr, RecursiveExpr

# data = claripy.BVS('t', 32)
# expr = VarExpr(data)
# trace_expr = TraceExpr(expr, 0)

# recur_expr = RecursiveExpr(data)
# recur_data = TraceExpr(recur_expr, 0)

# print(type(trace_expr.expr), type(recur_data.expr))
# if trace_expr == recur_data:
#     print("Yes")

# trace_exprs = [trace_expr]
# if recur_data in trace_exprs:
#     print("In")

# recur_expr2 = RecursiveExpr(data)
# recur_data2 = TraceExpr(recur_expr2, 0)
# print(recur_data2)

# if recur_data2 == recur_data:
#     print("Yes")

# print(recur_data, recur_data.expr.pattern)

# new_rec = recur_data.replace('t', 'r')
# print(new_rec, type(new_rec.expr))

# print("Test copy...")
# copy_rec = recur_data.copy()
# print(type(recur_data.expr))
# print(type(copy_rec.expr))

# copy_expr = expr.copy()
# print(type(copy_expr))

# copy_data = recur_expr.copy()
# print(type(copy_data))

# import itertools

# def get_all_combinations(alias_names, arg_ptr_alias):

#     def _combinations(l):
#         r = []
#         for i in range(1, len(l)+1):
#             iter = itertools.combinations(l,i)
#             r.append(list(iter))

#         return r

#     all_combination = {}
#     # s = 0
#     info = {}

#     for index, alias_name in enumerate(alias_names):
#         info[index] = []
#         has_alias_count = len(arg_ptr_alias[alias_name])

#         # for n in range(s, s+has_alias_count):
#         for n in range(has_alias_count):
#             info[index].append(n)

#         # s = s + has_alias_count

#     alias_list = info.keys()
#     diff_alias = _combinations(alias_list)

#     print(diff_alias)

#     for comb_list in diff_alias:
#         for t in comb_list:
#             p = [info[i] for i in t]
#             r = list(itertools.product(*p))

#             all_combination[t] = r

#     return all_combination

# alias_names = ['1', '2', '3']
# arg_ptr_alias = {'1': [1, 2, 3], '2': [4, 5], '3': [6, 7, 8]}

# print(alias_names)
# print(arg_ptr_alias)

# comb = get_all_combinations(alias_names, arg_ptr_alias)

# for t, c in comb.items():
#     print("%s %s" % (str(t), str(c)))

# for t, c in comb.items():
#     names = [alias_names[i] for i in t]

#     print(names)
#     for info in c:
#         # print(info)
#         cc = []
#         for j in range(len(names)):
#             a = info[j]
#             r = (names[j], arg_ptr_alias[names[j]][a])
#             cc.append(r)
#         print(cc)


from dataflow.variable_expression import Sim

sims = {}
sims[1] = Sim(live=True, def_loc=0x1234)
sims[2] = Sim(live=False, def_loc=0x4532)

print("%s" % (sims))

sims_copy = {}
for i, sim in sims.items():
    sims_copy[i] = sim.copy()
# sims_copy = sims.copy()
print("copy: %s" % (sims_copy))

sims_copy[1].live = False
print("%s" % (sims))
print("copy: %s" % (sims_copy))
