from z3 import *
import re


# 拆解 s 之 assertion，添加與變數相關之 statement，並回傳 solver
def tracked_wp(wp, s, tracked_conditions, i): 
    if is_implies(wp):
        pre_condition = wp.arg(0)
        post_condition = wp.arg(1)
        tracked_cond = Bool(f'track_cond_{i}')
        i = i + 1

        if is_true(pre_condition):
            tracked_wp(post_condition, s, tracked_conditions, i)
        else:
            s.assert_and_track(pre_condition, tracked_cond)
            tracked_conditions[tracked_cond] = pre_condition
            tracked_wp(post_condition, s, tracked_conditions, i)
        if is_false(post_condition):
            return s    

    if is_not(wp) or is_and(wp):
        post_condition = wp.arg(0)
        tracked_wp(post_condition, s, tracked_conditions, i)

    return s

"""更新 unsat core 中的賦值表達式"""
def update_unsat_core(core):
    p, n = Ints("p n")
    condition_str = str(core) # 將條件轉換為字符串表示形式
    updated_condition_str = re.sub(r'(\w+)\d+', r'\1', condition_str) # 移除變量名稱中的數字部分
    updated_condition_str = updated_condition_str.replace('==', '=') # 將 == 替換為 = 
    return updated_condition_str

"""取出 solvor 的條件，並找出衝突變數與 unsat core"""
def find_unsat_core(assertions, edges):
    tracked_conditions = {} # 用來追蹤此 infeasible path 經過哪些 statement
    unsat_core = [] # 存放 unsat core
    s = Solver()
    s.set(unsat_core = True)
    p = Int('p')
    n = Int('n')
    
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
                    if p.eq(child):
                        return p, unsat_core
                    if n.eq(child):
                        return n, unsat_core