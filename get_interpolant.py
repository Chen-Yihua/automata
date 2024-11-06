from pysmt.shortcuts import Symbol, Int, Not, Equals, GE, LE, GT, LT, Plus, Minus, Interpolator
from pysmt.typing import INT
import re

# 運算符字典，優先匹配較長的運算符 (>= 和 <=)
operators = {
    '>=': lambda x, y: GE(x, y),
    '<=': lambda x, y: LE(x, y),
    '!=': lambda x, y: Not(Equals(x, y)),
    '==': lambda x, y: Equals(x, y),
    '>': lambda x, y: GT(x, y),
    '<': lambda x, y: LT(x, y),
    '=': lambda x, y: Equals(x, y),  # 賦值操作
    '+': lambda x, y: Plus(x, y),
    '-': lambda x, y: Minus(x, y),
}

"""給定 condition list，找出 interpolant"""
def creat_interpolant(conditions):
    extract_variables(conditions) # 取得變量
    
    # 將條件從 list 解析為 PySMT 公式
    parsed_conditions = [parse_expression(cond) for cond in conditions]
    itp = Interpolator(name = "msat")
    interpolants = itp.sequence_interpolant(parsed_conditions)

    # 印出 interpolants
    for i, interp in enumerate(interpolants):
            print(f"I_{i}: {interp}")


# 根據條件式中的變量自動創建 Symbol
variables = {}
def extract_variables(expressions):
    for expr in expressions:
        # 使用正則表達式來提取變量名稱
        matches = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expr)
        for var in matches:
            # 如果變量還沒有創建 Symbol，則創建並添加到字典中
            if var not in variables:
                variables[var] = Symbol(var, INT)
    return variables


#解析一個條件並轉換為 PySMT 公式
def parse_expression(expr):
    for op in operators:
        if op in expr:
            left, right = map(str.strip, expr.split(op))
            left_var = variables.get(left, Int(int(left)) if left.isdigit() else None)
            right_var = variables.get(right, Int(int(right)) if right.isdigit() else parse_expression(right))
            return operators[op](left_var, right_var)
    raise ValueError(f"無法解析的條件: {expr}")


conditions = ['p == 0', 'n == 0', 'p != 0']
creat_interpolant(conditions)