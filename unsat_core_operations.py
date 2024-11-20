from unittest import skip
from z3 import *
from asyncio.windows_events import NULL
import re
import dfa_operations


p = Int('p')
n = Int('n')
# counters = {"global": 0}

# 拆解 s 之 assertion，添加與變數相關之 statement，並回傳 solver
def tracked_wp(wp, s, tracked_conditions, i):
    if is_implies(wp):
        pre_condition = wp.arg(0)
        post_condition = wp.arg(1)
        tracked_cond = Bool(f'track_cond_{i}')
        # tracked_cond = Bool(f'track_cond_{counters["global"]}')
        i = i + 1
        # counters["global"] += 1

        s.assert_and_track(pre_condition, tracked_cond)
        tracked_conditions[tracked_cond] = pre_condition
        tracked_wp(post_condition, s, tracked_conditions, i)
        if is_false(post_condition):
            return s

    if is_not(wp) or is_and(wp):
        post_condition = wp.arg(0)
        tracked_wp(post_condition, s, tracked_conditions, i)
    return s


# 更新 unsat core 中的賦值表達式回原本的表達式
def update_unsat_core(core):
    condition_str = str(core) # 將條件轉換為字符串表示形式
    updated_condition_str = re.sub(r'(\w+)\d+', r'\1', condition_str) # 移除變量名稱中的數字部分
    updated_condition_str = updated_condition_str.replace('==', '=') # 將 == 替換為 = 
    return updated_condition_str

"""取出 solvor 的條件，並找出 unsat var 與 unsat core"""
def find_unsat_core(assertions, edges):
    tracked_conditions = {} # 用來追蹤此 infeasible path 經過哪些 statement
    unsat_core = [] # 存放 unsat core
    s = Solver()
    s.set(unsat_core = True)
    
    assertions = assertions.assertions()
    for assertion in assertions :  # 取出 s 的條件，拆解出一個一個 statement
        tracked_wp(assertion, s, tracked_conditions, 0)
    s.check()
    core = s.unsat_core() # 找出 unsat core set
    for statement in core:  
        if str(tracked_conditions[statement]) in edges:
            unsat_core.append(tracked_conditions[statement])
        else:
            condition = update_unsat_core(tracked_conditions[statement])
            unsat_core.append(condition)
    for constraint in unsat_core: # 找出衝突變數
        if isinstance(constraint, str) == False:
            for child in constraint.children():
                    if p.eq(child): # 如果子節點與變量 p 相等
                        return p, unsat_core
                    if n.eq(child):
                        return n, unsat_core

"""根據 control flow graph，找出 unsat condition"""
def find_unsat_condition(G, unsat_var):
    path_edges = set()
    assignment_pattern = rf'({unsat_var})\s*=\s*([^=].*)'
    unsat_condition = NULL
    total_edges = G.edges()
    for edge in total_edges: # 紀錄 control flow graph 中所有的邊
        label = dfa_operations.get_symbol(G, edge[0], edge[1])
        path_edges.add(label)
    for edge in path_edges: # 若有賦值操作，則變量被修改
        value = dfa_operations.symbol_to_value(edge)
        if re.match(assignment_pattern, str(value)): 
            unsat_condition = value
    return unsat_condition


