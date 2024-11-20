from z3 import *
import re
import dfa_operations

# 替換賦值表達式的變量為新變量
def update_var(v, e): # 改新變數
    def substitute_variable(post, num):
        new_var_name = f"{v}{num}"  # 創建新變量名稱，例如 n -> n1
        new_var = Int(new_var_name)  # 創建新的 Z3 整數變量 n1
        updated_expr = substitute(post, (v, new_var))  # 使用 substitute 進行變量替換
        return new_var, new_var == e, updated_expr  # 返回新的變量、條件、新表達式
    return substitute_variable

# 查看路徑是否 infeasible
def begin(*args): # args 為一連串的表達式
    def res(post):
        wp = post # 紀錄 imply 結尾表達式
        counter = {}  # 用來記錄每個變量的替換次數
        intermediate_condition = []  # 儲存替換後的條件

        for s in reversed(args): # 假設 s 是函數
            if callable(s):
                # 執行 s 函數，得到賦值操作表達式
                new_var, new_condition, wp = s(wp, 1)  # 使用 1 作為初始替換計數
                if new_var not in counter: # 初始化計數器
                    counter[new_var] = 1
                else: 
                    counter[new_var] += 1 # 增加計數器
                new_var, new_condition, wp = s(wp, counter[new_var])
                wp = Implies(new_condition, wp)
                intermediate_condition.append(new_condition)
            else: # 若 s 是 Z3 的 BoolRef 對象，使用 Implies
                wp = Implies(s, wp) # 紀錄 imply 過程
                intermediate_condition.append(s)
        return wp
    return res

"""利用 weakest precondition，將條件式 imply 起來"""
def weakest_precondition(G, path):
    edge_labels = [] # 記錄此路徑的邊
    p, n = Ints("p n") 
    # 取得邊的內容，並轉成 z3 可讀的形式
    for i in range(0, len(path)-1, 1):
        label = dfa_operations.find_edge(G, path[i], path[i+1])

        # 處理賦值表達式，使其在 begin 中能使用
        assignment_pattern = r'(\w+)\s*=\s*([^=].*)'  # 將等式的左值與右值分開
        match = re.match(assignment_pattern, label)
        if match:
            left_side = match.group(1).strip()
            right_side = match.group(2).strip()
            left_side = Int(left_side)
            if right_side.isdigit():  # 處理右式，將數字與表達式分開處理
                right_side = IntVal(right_side)
            else:
                right_side = eval(right_side)
            edge_labels.append(update_var(left_side, right_side))
        else:
            edge_labels.append(eval(label))
    prog = begin(
        *edge_labels
    )
    result = Implies(BoolVal(True), And(prog(BoolVal(False))))
    return result

# 查看一組條件式是否可從起始位置走到 error location
def proof(G, path):
    prove_item = weakest_precondition(G, path)
    result, s = prove_path(prove_item)
    return result, s

def prove_path(claim, show=False, **keywords):
    s = Solver()
    s.set(**keywords)
    s.add(Not(claim))
    if show:
        print(s)
    r = s.check()
    if r == unsat: # path is valid，永遠成立 proved
        return("unsat", s)
    elif r == unknown: # failed to prove
        return("unknown", s)
    else: # 有 counterexample
        return("counterexample", s)