from z3 import *
import re

# 替換賦值表達式的變量為新變量
def update_var(v, e): # 改新變數
    def substitute_variable(post, num):
        new_var_name = f"{v}{num}"  # 創建新變量名稱，例如 n -> n1
        new_var = Int(new_var_name)  # 創建新的 Z3 整數變量 n1
        updated_expr = z3.substitute(post, (v, new_var))  # 使用 substitute 進行變量替換
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
                else: counter[new_var] += 1 # 增加計數器
                new_var, new_condition, wp = s(wp, counter[new_var])
                intermediate_condition.append(new_condition)
                # wp = Implies(new_condition, wp)
            else: # 若 s 是 Z3 的 BoolRef 對象，使用 Implies
                intermediate_condition.append(s)
                # wp = Implies(s, wp) # 紀錄 imply 過程
        # return wp
        return intermediate_condition
    return res

# 將替換結果組合成 Implies 條件
def combine_implies(intermediate_condition, post):
    for _, condition, expr in intermediate_condition:
        if condition is not None:
            post = Implies(condition, post)
        elif expr is not None:
            post = Implies(expr, post)
    return post

# 變量替換函式，回傳替換後的條件列表
# def substitute_conditions(args, post):
#     counter = {}  # 用來記錄每個變量的替換次數
#     intermediate_results = []  # 儲存替換後的條件

#     for s in reversed(args):  # 從右到左依序處理表達式
#         if callable(s):
#             new_var, new_condition, post = s(post, counter.get(new_var, 1))  # 初次替換使用計數1
#             counter[new_var] = counter.get(new_var, 1) + 1  # 增加計數器
#             intermediate_results.append((new_var, new_condition, post))
#         elif isinstance(s, BoolRef):
#             intermediate_results.append((None, s, None))

#     return intermediate_results, post

# 處理一組條件式，替換變量後組成完整的 Implies 表達式
def process_conditions(*args):
    def substitute_and_imply(post):
        intermediate_results, final_post = begin(args, post)
        return combine_implies(intermediate_results, final_post)
    return substitute_and_imply


"""利用 weakest precondition，建構不可行證明"""
def proof(G, path, edges):
    edge_label = [] # 記錄此路徑的邊
    p, n = Ints("p n")
    # 取得邊的內容，並轉成 z3 可讀的形式
    for i in range(0, len(path)-1, 1):
        edge = G[path[i], path[i+1]]  # 取出 trace 中的邊
        # 處理賦值表達式，使其在 begin 中能使用
        assignment_pattern = r'(\w+)\s*=\s*([^=].*)'  # 將等式的左值與右值分開
        match = re.match(assignment_pattern, edge['label'])
        if match:
            left_side = match.group(1).strip()
            right_side = match.group(2).strip()
            left_side = Int(left_side)
            if right_side.isdigit():  # 處理右式，將數字與表達式分開處理
                right_side = IntVal(right_side)
            else:
                right_side = eval(right_side)
            edge_label.append(update_var(left_side, right_side))
        else:
            edge_label.append(eval(edge['label']))
    prog = process_conditions(
        *edge_label
    )
    # 查看一組條件式是否可從起始位置走到 error location
    result, s =  prove(Implies(BoolVal(True), And(prog(BoolVal(False)))))
    return result, s