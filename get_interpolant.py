from pysmt.shortcuts import Symbol, Bool, Int, Not, Equals, GE, LE, GT, LT, Plus, Minus, Interpolator
from pysmt.typing import INT
from z3 import Int as Z3Int, And as Z3And, Solver
import re

# 運算符字典，優先匹配較長的運算符 (>= 和 <=)
operators = {
    '>=': lambda x, y: GE(x, y),
    '<=': lambda x, y: LE(x, y),
    '!=': lambda x, y: Not(Equals(x, y)),
    '==': lambda x, y: Equals(x, y),
    '>': lambda x, y: GT(x, y),
    '<': lambda x, y: LT(x, y),
    '=': lambda x, y: Equals(y, x),  # 賦值操作
    '+': lambda x, y: Plus(x, y),
    '-': lambda x, y: Minus(x, y)
}

"""給定 condition list，找出 interpolant"""
def creat_interpolant(conditions):
    extract_variables(conditions) # 取得變量
    interpolant_list = []
    
    # 將條件從 list 解析為 PySMT 公式
    parsed_conditions = [parse_expression(cond) for cond in conditions]
    itp = Interpolator(name = "msat")
    try:
        interpolants = itp.sequence_interpolant(parsed_conditions)
        # 印出 interpolants
        for i, interp in enumerate(interpolants):
            interpolant_list.append(interp)
        print("interpolant_list:",interpolant_list)
        return(interpolant_list[-1])
    except:
        print("the path is sat")


# 根據條件式中的變量自動創建 Symbol
variables = {}
def extract_variables(expressions):
    for expr in expressions:
        if expr == True or expr == False:
            continue
        else:
            # 使用正則表達式來提取變量名稱
            matches = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expr)
            for var in matches:
                # 如果變量還沒有創建 Symbol，則創建並添加到字典中
                if var not in variables:
                    variables[var] = Symbol(var, INT)
    return variables


# 解析一個條件並轉換為 PySMT 公式
def parse_expression(expr):
    if expr.strip() == 'True':
        return Bool(True)
    elif expr.strip() == 'False':
        return Bool(False)
    for op in operators:
        if op in expr:
            left, right = map(str.strip, expr.split(op))
            # left_var 的解析：若是數字則轉為 Int，若是變數則從 variables 獲取，否則解析表達式
            left_var = Int(int(left)) if left.isdigit() else variables.get(left) if left in variables else parse_expression(left)
            # right_var 的解析：若是數字則轉為 Int，若是變數則從 variables 獲取，否則解析表達式
            right_var = Int(int(right)) if right.isdigit() else variables.get(right) if right in variables else parse_expression(right)

            return operators[op](left_var, right_var)
    raise ValueError(f"無法解析的條件: {expr}") # 若無法匹配到運算符，則拋出例外

def get_z3_from_pysmt(formula):
    # 映射 PySMT 符號為 Z3 符號
    variables = {var.symbol_name(): Z3Int(var.symbol_name()) for var in formula.get_free_variables()}

    # 遍歷公式並替換 PySMT 符號為 Z3 符號
    def translate(sub_formula):
        if sub_formula.is_symbol():  # 處理變量
            return variables[sub_formula.symbol_name()]
        elif sub_formula.is_and():  # 處理 And
            return Z3And(*map(translate, sub_formula.args()))
        elif sub_formula.is_equals():  # 處理 Equals
            left, right = map(translate, sub_formula.args())
            return left == right
        elif sub_formula.is_ge():  # 處理 Greater or Equal
            left, right = map(translate, sub_formula.args())
            return left >= right
        elif sub_formula.is_lt():  # 處理 Less Than
            left, right = map(translate, sub_formula.args())
            return left < right
        elif sub_formula.is_plus():  # 處理 Plus
            return sum(map(translate, sub_formula.args()))
        elif sub_formula.is_int_constant():  # 處理整數常量
            return sub_formula.constant_value()
        else:
            raise ValueError(f"Unsupported formula: {sub_formula}")

    return translate(formula)

def interpolant_proof():

    return

# 將一個 PySMT 公式轉換為 z3 形式

# conditions = [True, 'p != 0', 'n >= 0', 'n == 0', '0 = p1', 'n1 == n - 1', 'n1 >= 0', 'p1 == 0']
# conditions = ['p != 0', 'n >= 0', 'n == 0', '0 == p1', 'n1 == n - 1', 'n1 >= 0', 'p1 == 0']
# conditions = ['p != 0', 'n >= 0', 'n != 0', 'n1 == n - 1', 'n1 >= 0', 'p == 0']
# conditions = ['True', 'p != 0', 'n >= 0']
# creat_interpolant(conditions)
get_z3_from_pysmt(GE(x, y))