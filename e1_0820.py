from asyncio.windows_events import NULL
from z3 import *
from graphviz import Digraph
from automata.fa.dfa import DFA
# from visual_automata.fa.dfa import VisualDFA
import heapq
import re
 
# 畫出 dfa
def draw_dfa(dfa, edge_mapping):
    G = {}
    dot = Digraph()
    states = dfa.states
    transitions = dfa.transitions
    final_states = dfa.final_states

    def get_key_from_value(mapping, value):  # 將邊由編號改成文字
        for key, val in mapping.items():
            if val == value:
                return key
        return None

    for state in states:  # 加入節點
        if state in final_states:
            dot.node(str(state), shape='doublecircle')
        else: dot.node(str(state))
    for from_state, edges in transitions.items():  # 加入邊
        for symbol, to_state in edges.items():
            value = get_key_from_value(edge_mapping, symbol)
            dot.edge(str(from_state), str(to_state), label=value)
            G[(from_state, to_state)] = {'label': value}

    dot.render('dfa', format='png', view=True)
    return G

# 找出 trace 最短路徑，並建構證明
def find_trace(G, error_location, edge_mapping, start, edge):
    finded = False
    # add_cycle = []
    # G_copy = copy.deepcopy(G)  # 複製圖
    # print(G_copy)
    while finded == False:
        path = dijkstra(G, error_location, start)  # 找出走到 error location 的最短 trace
        expr1, unsat_var, unsat_core = weakest_precondition(True, False, path, edges)  # 計算其 annotation 判斷要加進去嗎
        # 找最短路徑、算ano、若為unsat 做dfa、否則找別條最短路徑
        if expr1 == True:
            print("shortest_error_path :", path)
            unsat_condition = find_unsat_condition(unsat_var)
            print("unsat_condition:",unsat_condition)
            dfa = build_dfa(G, path, edge_mapping, start, error_location, unsat_condition)  # 製作 dfa
            draw_dfa(dfa, edge_mapping)
            finded = True # 找到最短路徑
        # else: # 繼續找其他路徑
        #     path, G_copy = del_shortest_paths(G_copy, path) # 在 G_copy 刪除最短路徑
        #     print(G_copy)
    # del G_copy # 刪除複製的圖

    cycles = find_all_cycles(start)  # 找出程式中的 loop
    for cycle in cycles: # 針對每個 loop
        new_path, modified = update_path(path, cycle, unsat_condition, unsat_core, edge)  # 將 loop 加入 path
        if modified == False:
             # 若實際程式走不到且 unsat core 一樣，以此新的 path 更新 dfa
            dfa = build_dfa(G, new_path, edge_mapping, start, error_location, unsat_condition)
            print("add cycle:", cycle)
            path = new_path
    print("trace : ", path)
    draw_dfa(dfa, edge_mapping)  # 畫出 p 之 dfa
    return path, dfa

# 找出最短路徑
def dijkstra(G, end, start):
    nodes = set()  # 存放節點與邊
    for edge in G:
        u, v = edge
        nodes.add(u)
        nodes.add(v)
    # 初始化 (每個節點的初始距離為無限大、起始節點的為0)
    distances = {node: float('inf') for node in set(
        x for edge in G.keys() for x in edge)}
    distances[start] = 0
    # 做 min heap，以選擇最短距離的節點
    priority_queue = [(0, start)]
    heapq.heapify(priority_queue)
    # 記錄前一個節點(從哪個點走來的)
    previous_nodes = {node: None for node in distances}

    while priority_queue:
        # 取當前距離最小的節點與距離
        current_distance, current_node = heapq.heappop(priority_queue)
        # 結束設定
        if current_node == end:
            break
        # 更新鄰居節點的距離
        for (u, v), attrs in G.items():
            if u == current_node:
                weight = 1
                distance = current_distance + weight
                if distance < distances[v]:
                    distances[v] = distance
                    previous_nodes[v] = current_node
                    heapq.heappush(priority_queue, (distance, v))

    # 輸出路徑
    path = []
    node = end
    while node is not None:
        path.append(node)
        node = previous_nodes[node]
    path.reverse()
    return path

# 排除最短路徑，以找第二短的路徑
# def del_shortest_paths(G, path):
#     # paths = []
#     # for _ in range(2):
#     #     path = dijkstra(G, start, end)
#     #     if not path:
#     #         break
#     #     paths.append(path)
        
#     # 排除當前找到的路徑的每一條邊
#     for i in range(len(path) - 1):
#         u = path[i]
#         v = path[i + 1]
#         if (u, v) in G:
#             del G[(u, v)]
#     return path, G

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

# 取出 solvor 的條件，遞迴拆解條件
def find_unsat_core(assertions, edges, edge_label):
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

    print("unsat core : ", unsat_core)
    
    for constraint in unsat_core: # 找出衝突變數
        if isinstance(constraint, str) == False:
            for child in constraint.children():
                    if p.eq(child):
                        return p, unsat_core
                    if n.eq(child):
                        return n, unsat_core

# 更新 unsat_core
def update_unsat_core(core):
    p, n = Ints("p n")
    condition_str = str(core) # 將條件轉換為字符串表示形式
    updated_condition_str = re.sub(r'(\w+)\d+', r'\1', condition_str) # 移除變量名稱中的數字部分
    updated_condition_str = updated_condition_str.replace('==', '=') # 將 == 替換為 = 
    return updated_condition_str

# 找出 unsat condition
def find_unsat_condition(unsat_var):
    edges = set()
    assignment_pattern = rf'({unsat_var})\s*=\s*([^=].*)'
    unsat_condition = NULL
    for edge, properties in G.items(): # 紀錄 control flow graph 中所有的邊
        edges.add(properties['label'])
    for edge in edges: # 若有賦值操作，則變量被修改
        if re.match(assignment_pattern, str(edge)): 
            unsat_condition = edge
    return unsat_condition

def substitute(t, *m, num):
    v, e = m[0]  # 取出變量 v 和表達式 e
    new_var_name = f"{v}{num}"  # 將變數名改為新變數，如 n -> n1
    new_var = Int(new_var_name)  # 創建新的 Z3 整數變量 n1
    updated_expr = z3.substitute(t, (v, new_var)) # 使用 substitute 進行變量替換
    return new_var, new_var == e, updated_expr

def set_(v, e): # 改新變數
    return lambda post, num: substitute(post, (v, e), num=num)
    
def verify_fun(pre, post, body): # check unsat
    return prove(Implies(pre, And(body(post))))

def begin(*args): # args 為一連串的表達式
    def res(post):
        wp = post # 紀錄 imply 結尾表達式
        counter = {}  # 用來記錄每個變量的替換次數

        for s in reversed(args): # 假設 s 是函數
            if callable(s):
                # 執行 s 函數，得到賦值操作表達式
                new_var, new_condition, wp = s(wp, 1)  # 使用 1 作為初始替換計數
                if new_var not in counter: # 初始化計數器
                    counter[new_var] = 1
                else: counter[new_var] += 1 # 增加計數器
                new_var, new_condition, wp = s(wp, counter[new_var])
                wp = Implies(new_condition, wp)
            else: # 若 s 是 Z3 的 BoolRef 對象，使用 Implies
                wp = Implies(s, wp) # 紀錄 imply 過程
        return wp
    return res

# 利用 weakest precondition，算出 annotation，Construct proof
def weakest_precondition(pre, post, path, edges, invariant = None):
    edge_label = [] # r記錄此路徑的邊
    p, n = Ints("p n")
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
            edge_label.append(set_(left_side, right_side))
        else:
            edge_label.append(eval(edge['label']))  # 取得邊的內容，並轉成 z3 可讀的形式
    prog = begin(
        *edge_label
    )
    # 查看是否可從起始位置走到 error location
    result, s = verify_fun(BoolVal(True), BoolVal(False), prog)  
    if str(result) == "unsat":
        unsat_var, unsat_core = find_unsat_core(s, edges, edge_label) # 找出 unsat core
        return True, unsat_var, unsat_core
    else: return False, NULL, NULL

# 做 DFA
def build_dfa(G, path, mapping, start, end, unsat_condition):
    states = set()
    input_symbols = set()
    path_edge = [] # 此 path 的邊
    unsat_node = []

    # 紀錄此 path 的邊
    for i in range(len(path)-1):
        edge = G[path[i], path[i+1]]
        path_edge.append(edge)
    # 製作 input_symbols
    for edge, properties in G.items():
        input_symbols.add(mapping[properties['label']])
        if properties['label'] == unsat_condition and edge[0] != edge[1]: # 找出 unsat node
            unsat_node.append(edge[0])
        states.add(str(edge[0]))
    # 添加 reject state
    if unsat_condition != 0:
        states.add('reject_node')
    # 製作 transitions
    transitions = {state: {value: state for key, value in mapping.items()}
                   for state in states}  # 初始化 transition
    # 對於 path 中每個點，找出與此點相連的邊，並調整其 transition，將點相連
    for i in range(len(path)-1):
        for edge, properties in G.items():
            if edge[0] == path[i] and edge[1] == path[i+1]:  
                transitions[str(path[i])][mapping.get(properties['label'])] = str(edge[1]) 
            
    # 將 unsat node 連至 reject_node
    for node in unsat_node:
        if node not in path:
            transitions[str(node)][mapping.get(unsat_condition)] = 'reject_node'
            # 若 unsat_node 不在 path 裡，更改走進 unsat node 的邊
            for edge, properties in G.items():
                if edge[1] == node:
                    transitions[str(edge[0])][mapping.get(properties['label'])] = str(node)

    dfa = DFA(
        states = states,
        input_symbols = input_symbols,
        transitions = transitions,
        initial_state = str(start),
        final_states = {str(end)}
    )
    return dfa

# 製作 forzenset_mapping
def forzenset_mapping(dfa):
    forzenset_mapping = {}
    for node in dfa.final_states:
        forzenset_mapping[node] = node
    state = forzenset_mapping[node]
    return state

# 判斷 loop 有無更改衝突變數，若無則可加入 path
def update_path(path, cycle, unsat_condition, unsat_core, edges):
    new_paths = path.copy()
    new_unsat_core = unsat_core.copy()
    is_connect = False
    modified = False

    # 判斷 loop 與 最短路徑相連嗎
    for node in cycle: 
        if node in path:
            loop_start = path.index(node) + 1
            is_connect = True
            break
                
    # 找 unsat_core 的位置
    core_index = []
    index = 0 # 紀錄查看到 path 的哪個位置
    for i in range(len(new_unsat_core)):
        for j in range(len(path)-1):
            edge = G[path[j], path[j+1]]
            if edge['label'] == str(new_unsat_core[i]) and j >= index:
                core_index.append(j)
                index = j

    # 檢查 unsat_condition 是否在它們之間，且變量有無被修改
    for i in range(len(core_index)-1):
        if core_index[i] < loop_start and core_index[i+1] >= loop_start:
            for j in range(len(cycle)-1):
                edge = G[cycle[j], cycle[j+1]]
                if edge['label'] == unsat_condition:
                    modified = True
                    break
    
     # 若相連，且變量未被修改，則將 loop 加入 path  
    if is_connect == True and modified == False: 
        # 將 cycle 加入 path
        for node in cycle[1:]:  # 從第二個元素開始加
            new_paths.insert(loop_start, node)
            loop_start = loop_start + 1
        return new_paths, modified
    else :
        return path, modified

def dfs(v, visited, stack, all_cycles):  # 尋找迴圈 
        stack.append(v) # 用來記錄從起點到當前節點的整個搜尋路徑，以判斷 loop 的位置
        visited.append(v) # 記錄已經拜訪過的節點

        for key, value in G.items():  # 找出 neighbor
            if v == key[0]:
                neighbor = key[1]
                if neighbor == v: # 如果 neighbor 等於 v，則跳過自我迴圈的檢查
                    continue 
                if neighbor not in visited:
                    dfs(neighbor, visited, stack, all_cycles)
                elif neighbor in stack: # 在 stack 找 neighbor 的位置
                    cycle_start = stack.index(neighbor)
                    cycle = stack[cycle_start:] + [neighbor]
                    if cycle not in all_cycles:  # 若此 loop 沒被找過，則加入 loop 集合
                        all_cycles.append(tuple(cycle))
        stack.pop()
        visited.remove(v)

# 尋找圖中的 loop 有無self loop
def find_all_cycles(start): 
    visited = []
    stack = []
    all_cycles = []

    dfs(start, visited, stack, all_cycles)
    return all_cycles 


# main
G = {
    ('Node0', 'Node1'): {'label': 'p != 0'},
    ('Node1', 'Node2'): {'label': 'n >= 0'},
    ('Node2', 'Nodeerr'): {'label': 'p == 0'},
    ('Node2', 'Node3'): {'label': 'n == 0'},
    ('Node2', 'Node4'): {'label': 'n != 0'},
    ('Node3', 'Node4'): {'label': 'p = 0'},
    ('Node4', 'Node1'): {'label': 'n = n - 1'},
}

complete = False  # 紀錄 trace 皆已取完了嗎
edge_mapping = {
    'p != 0': '0',
    'n >= 0': '1',
    'p == 0': '2',
    'n == 0': '3',
    'n != 0': '4',
    'p = 0': '5',
    'n = n - 1': '6'
}
edges =['p != 0', 'n >= 0', 'p == 0', 'n == 0', 'n != 0', 'p = 0', 'n = n - 1']

# 做 DFA
total_dfa = DFA(
    states={'Node0', 'Node1', 'Node2', 'Node3', 'Node4', 'Nodeerr'},
    input_symbols={'0', '1', '2', '3', '4', '5', '6'},
    transitions={
        'Node0': {'0': 'Node1', '1': 'Node0', '2': 'Node0', '3': 'Node0', '4': 'Node0', '5': 'Node0', '6': 'Node0'},
        'Node1': {'1': 'Node2', '2': 'Node1', '0': 'Node1', '3': 'Node1', '4': 'Node1', '5': 'Node1', '6': 'Node1'},
        'Node2': {'4': 'Node4', '3': 'Node3', '2': 'Nodeerr', '0': 'Node2', '1': 'Node2', '5': 'Node2', '6': 'Node2'},
        'Node3': {'5': 'Node4', '0': 'Node3', '1': 'Node3', '2': 'Node3', '3': 'Node3', '4': 'Node3', '6': 'Node3'},
        'Node4': {'6': 'Node1', '0': 'Node4', '1': 'Node4', '2': 'Node4', '3': 'Node4', '4': 'Node4', '5': 'Node4'},
        'Nodeerr': {'0': 'Nodeerr', '1': 'Nodeerr', '2': 'Nodeerr', '3': 'Nodeerr', '4': 'Nodeerr', '5': 'Nodeerr', '6': 'Nodeerr'}
    },
    initial_state='Node0',
    final_states={'Nodeerr'}
)
# cfw(G) # 製作 control flow graph
G = draw_dfa(total_dfa, edge_mapping)

# 找出第一條 trace
trace, dfa1 = find_trace(G, 'Nodeerr', edge_mapping, 'Node0', edges)

# 找出其他 trace
while complete == False:
    diff = total_dfa.difference(dfa1)
    G = draw_dfa(diff, edge_mapping) # 畫出差集後的圖
    if(diff.isempty() != True): # 若差集完非空，則繼續找 trace
        trace, dfa2 = find_trace(G, forzenset_mapping(diff), edge_mapping, diff.initial_state, edges)
        total_dfa = diff
        dfa1 = dfa2
    else:
        complete = True
        print("complete")