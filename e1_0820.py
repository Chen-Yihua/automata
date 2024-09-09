from z3 import *
from graphviz import Digraph
from automata.fa.dfa import DFA
import heapq
import re

# 畫出 Control flow graph
def cfw(G):
    dot = Digraph()  # 創建圖
    for (i, j), label in G.items():  # 畫點與邊
        dot.edge(i, j, label=label['label'])
    dot.render('cfg', format='png', view=True)  # render 圖片
    return G

# 畫出 dfa
def draw_dfa(dfa, edge_mapping):
    G = {}
    dot = Digraph()
    states = dfa.states
    transitions = dfa.transitions

    def get_key_from_value(mapping, value):  # 將邊由編號改成文字
        for key, val in mapping.items():
            if val == value:
                return key
        return None

    for state in states:  # 加入節點
        dot.node(str(state))
    for from_state, edges in transitions.items():  # 加入邊
        for symbol, to_state in edges.items():
            value = get_key_from_value(edge_mapping, symbol)
            dot.edge(str(from_state), str(to_state), label=value)
            G[(from_state, to_state)] = {'label': value}

    dot.render('dfa', format='png', view=True)
    return G

# 找出 trace 最短路徑，並建構證明
def find_trace(G, error_location, edge_mapping, start):
    finded = False
    while finded == False:
        path, error_location = dijkstra(G, error_location, start)  # 找出走到 error location 的最短 trace
        expr1 = weakest_precondition(True, False, path)  # 計算其 annotation 判斷要加進去嗎
        # 找最短路徑、算ano、若為unsat 做dfa、否則找別條最短路徑
        if expr1 == True:
            print("shortest_error_path :", path)
            dfa = build_dfa(G, path, edge_mapping, start, error_location)  # 製作 dfa
            finded = True
            draw_dfa(dfa, edge_mapping)  # 畫出 p 之 dfa

    cycles = find_all_cycles(start)  # 找出程式中的 loop
    for cycle in cycles: # 實際程式走不到就加進去
        new_path = update_path(path, cycle)  # 將 loop 加入 path
        expr2 = weakest_precondition( True, False, new_path)  # 計算加入 loop 後的 annotation
        if expr2 == True:
            dfa = build_dfa(G, new_path, edge_mapping, start, error_location)  # 更新 dfa
            print("add cycle")
            path = new_path
    # wp = weakest_precondition(True, False, path)  # 計算 notation
    # print("annotation : ", wp)
    draw_dfa(dfa, edge_mapping)  # 畫出 p 之 dfa
    return path, dfa

# 找出最短路徑
def dijkstra(G, end, start):
    paths = []
    for error_node in end:
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
            if current_node == error_node:
                break
            # 更新鄰居節點的距離
            for (u, v), attrs in G.items():
                if u == current_node:
                    weight = 1
                    distance = current_distance + weight
                    new_distance = current_distance + distance
                    if new_distance < distances[v]:
                        distances[v] = new_distance
                        previous_nodes[v] = current_node
                        heapq.heappush(priority_queue, (new_distance, v))

        # 輸出路徑
        path = []
        node = error_node
        while node is not None:
            path.append(node)
            node = previous_nodes[node]
        path.reverse()
        paths.append(path)
    
    # 針對每個 error node，判斷哪一條路徑最短
    for i in range(len(paths)):
        if len(paths[0]) < len(paths[i]):
            swap = paths[0]
            paths[i] = swap
            paths[0] = paths[i]

    return paths[0], paths[0][len(paths)-1]


def set_(v, e):
    return lambda post: substitute(post, (v, e))


def verify_fun(pre, post, body): # check unsat
    return prove(Implies(pre, body(post)))


def begin(*args):
    def res(post):
        wp = post
        for s in reversed(args):  # 假設 s 是函數
            if callable(s):
                wp = s(wp)
            else:
                wp = Implies(s, wp)  # 若 s 是 Z3 的 BoolRef 對象，使用 Implies
        return wp
    return res

# 利用 weakest precondition，算出 annotation，Construct proof
def weakest_precondition(pre, post, path):
    label = []
    p, n = Ints("p n")
    for i in range(len(path)-1, 0, -1):
        edge = G[path[i-1], path[i]]  # 取出 trace 中的邊
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
            label.append(set_(left_side, right_side))
        else:
            label.append(eval(edge['label']))  # 取得邊的內容，並轉成 z3 可讀的形式
    prog = begin(
        *label
    )
    a = verify_fun(True, False, prog)  # 查看是否可從起始位置走到 error location
    if str(a) == "unsat":
        return True
    else: return False

# 做 DFA
def build_dfa(G, path, mapping, start, end):
    states = set()
    input_symbols = set()

    # 製作 input_symbols
    for edge, properties in G.items():
        input_symbols.add(mapping[properties['label']])
    # 製作 state
    for i in range(len(path)):
        states.add(f'{path[i]}')

    # 製作 transitions
    transitions = {state: {value: state for key, value in mapping.items()}
                   for state in states}  # 初始化 transition
    for i in range(len(path)):  # 對於 path 中每個點
        for edge, properties in G.items():
            if path[i] in edge[0] and edge[1] in path:  # 找出與此點相連的邊
                transitions[path[i]][mapping.get(
                    properties['label'])] = edge[1]  # 更改連接的邊

    dfa = DFA(
        states = states,
        input_symbols = input_symbols,
        transitions = transitions,
        initial_state = start,
        final_states = {end}
    )
    # 測試 DFA
    # test_strings = ['015','01234127']
    # for string in test_strings:
    #     if dfa.accepts_input(string):
    #         print(f"The string '{string}' is not accepted by the DFA.")
    #     else:
    #         print(f"The string '{string}' is accepted by the DFA.")
    # dfa, initial_state, final_states = forzenset_mapping(dfa)

    return dfa

# 做 dfa 的補集
def complement_dfa(dfa):
    new_final_states = set()
    for state in dfa.states:
        if state not in dfa.final_states:
            new_final_states.add(state)
    complement = DFA(
        states=dfa.states,
        input_symbols=dfa.input_symbols,
        transitions=dfa.transitions,
        initial_state=dfa.initial_state,
        final_states=new_final_states
    )
    return complement

# 做 dfa 的差集
def intersection_dfa(dfa1, dfa2):
    new_states = set()
    new_transitions = {}
    new_final_states = set()

    for state1 in dfa1.states:
        for state2 in dfa2.states:
            new_state = f'{state1}_{state2}'
            new_states.add(new_state)

            new_transitions[new_state] = {}
            for symbol in dfa1.input_symbols:
                next_state1 = dfa1.transitions[state1][symbol]
                next_state2 = dfa2.transitions[state2][symbol]
                new_transitions[new_state][symbol] = f'{next_state1}_{next_state2}'

            # 對於 new_state，如果兩個 DFA 都可接受，則新 DFA 也可接受
            if state1 in dfa1.final_states and state2 in dfa2.final_states:
                new_final_states.add(new_state)

    new_initial_state = f'{dfa1.initial_state}_{dfa2.initial_state}'

    intersection = DFA(
        states = new_states,
        input_symbols = dfa1.input_symbols,
        transitions = new_transitions,
        initial_state = new_initial_state,
        final_states = new_final_states
    )
    return intersection, new_final_states, new_initial_state

def difference_dfa(dfa1, dfa2, mapping):
    # 對 DFA1 和 DFA2 的補集進行交集運算
    dfa2_complement = complement_dfa(dfa2)
    diff, final_states, initial_state = intersection_dfa(dfa1, dfa2_complement)

    return diff, final_states, initial_state

# 製作 forzenset_mapping
# def forzenset_mapping(dfa):
#     new_states = set()
#     new_transitions = {}
#     final_states = set()
#     forzenset_mapping = {}
#     # num = 0 
#     for node in dfa.states:
#         forzenset_mapping[node] = str(node)
#         # num += 1

#     # 處理 forzenset 的值，以便能做 dijkstra
#     for state, transitions in dfa.transitions.items():
#         new_state = forzenset_mapping[state]
#         new_states.add(new_state)
#         new_transitions[new_state] = {
#             symbol: forzenset_mapping.get(next_state)
#             for symbol, next_state in transitions.items()
#         }
        
#     initial_state = forzenset_mapping[dfa.initial_state]
#     for state in dfa.final_states:
#         final_states.add(forzenset_mapping[state])
    
#     # 建立差集後的 DFA
#     new_dfa = DFA(
#         states = new_states,
#         input_symbols = dfa.input_symbols,
#         transitions = new_transitions,
#         initial_state = initial_state,
#         final_states = final_states
#     )

#     return new_dfa, initial_state, final_states


def update_path(path, cycle):
    new_paths = path.copy()
    is_connect = False
    for node in cycle:  # 判斷 loop 與 最短路徑相連嗎
        if node in path:
            loop_start = path.index(node) + 1
            is_connect = True

    if is_connect == True:  # 若相連，則將 loop 加入 path
        for node in cycle[1:]:  # 從第二個元素開始加
            new_paths.insert(loop_start, node)
            loop_start = loop_start + 1

    return new_paths

# 尋找圖中的 loop***
def find_all_cycles(start):
    visited = []
    stack = []
    all_cycles = []

    def dfs(v, visited, stack, all_cycles):  # 尋找迴圈
        stack.append(v)
        visited.append(v)

        for key, value in G.items():  # 找出 neighbor
            if v == key[0]:
                neighbor = key[1]
                if neighbor not in visited:
                    dfs(neighbor, visited, stack, all_cycles)
                elif neighbor in stack:
                    # 在 stack 找 neighbor 的位置
                    cycle_start = stack.index(neighbor)
                    cycle = stack[cycle_start:] + [neighbor]
                    if cycle not in all_cycles:  # 若此 loop 沒被找過，則加入 loop 集合
                        all_cycles.append(tuple(cycle))
        stack.pop()
        visited.remove(v)

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

taken = False  # 紀錄取過 trace 了嗎
complete = False  # 紀錄 trace 皆已取完了嗎
# nodes = []  # 記錄所有節點
mapping = {}  # 紀錄所有邊，並對邊做 mapping
i = 0
edge_mapping = {
    'p != 0': '0',
    'n >= 0': '1',
    'p == 0': '2',
    'n == 0': '3',
    'n != 0': '4',
    'p = 0': '5',
    'n = n - 1': '6'
}

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

# for edge, properties in G.items():
#     mapping[properties['label']] = f'{i}'
#     i = i + 1
#     if edge[0] not in nodes:
#         nodes.append(edge[0])
#     if edge[1] not in nodes:
#         nodes.append(edge[1])

cfw(G) # 製作 control flow graph

# 找出第一條 trace
trace, dfa1 = find_trace(G, {'Nodeerr'}, edge_mapping, 'Node0')
print("trace : ", trace)

# 找出其他 trace
# while complete == False:
diff, final_state, initial_state = difference_dfa(total_dfa, dfa1, edge_mapping)
G = draw_dfa(diff, edge_mapping) # 畫出差集後的圖
trace, dfa2 = find_trace(G, final_state, edge_mapping, initial_state)
print("trace : ", trace)

# 將所有 dfa 做聯集
# dfa_union = dfa.union(dfa2)

# # 將 dfa_all 和 dfa_union 做差集
# dfa_diff = total_dfa.difference(dfa_union)

# # 檢查 dfa_diff 是否為空
# if not dfa_diff.final_states:
#     print("dfa_all 包含於 dfa 聯集")
#     complete = True
#     break
# else:
#     print("dfa_all 不包含於 dfa 聯集")
#     dfa = dfa_union
