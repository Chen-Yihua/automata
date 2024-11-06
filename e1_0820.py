from asyncio.windows_events import NULL
from z3 import *
from automata.fa.dfa import DFA
import heapq
import re
import get_interpolant
import dfa_operations
import unsat_core_operations
import infeasible_proof

"""找出 trace 最短路徑，並建構證明"""
def find_trace(G, error_location, edge_mapping, start, edges):
    found_path = False
    path, dfa = None, None

    while found_path == False:
        path = dijkstra(G, error_location, start)  # 找出走到 error location 的最短 path
        proof_result, solver = infeasible_proof.proof(G, path, edges)  # 判斷不可行性           
        # 若 path 為 unsat，找出 unsat_core，並做dfa
        if proof_result == "unsat":
            unsat_var, unsat_core = unsat_core_operations.find_unsat_core(solver, edges) # 找出 unsat var, unsat core
            unsat_condition = unsat_core_operations.find_unsat_condition(G, unsat_var) # 找出 unsat condition
            dfa = dfa_operations.build_dfa(G, path, edge_mapping, start, error_location, unsat_condition)  # 製作 dfa
            dfa_operations.draw_dfa(dfa, edge_mapping)
            found_path = True # 找到最短路徑

    for cycle in find_all_cycles(start): # 找出程式中的 loop
        new_path, modified = update_path(path, cycle, unsat_condition, unsat_core)  # 將 loop 加入 path
        if modified == False:
             # 若實際程式走不到且 unsat core 一樣，以此新的 path 更新 dfa
            dfa = dfa_operations.build_dfa(G, new_path, edge_mapping, start, error_location, unsat_condition)
            dfa_operations.draw_dfa(dfa, edge_mapping)  # 畫出 p 之 dfa
            path = new_path
    return path, dfa

"""找出最短路徑"""
def dijkstra(G, end, start):
    # 初始化 (每個節點的初始距離為無限大、起始節點的為0)
    distances = {node: float('inf') for node in set(x for edge in G.keys() for x in edge)}
    distances[start] = 0
    priority_queue = [(0, start)] 
    heapq.heapify(priority_queue) # 做 min heap，以選擇最短距離的節點
    previous_nodes = {node: None for node in distances} # 記錄前一個節點(從哪個點走來的)

    while priority_queue:
        current_distance, current_node = heapq.heappop(priority_queue) # 取當前距離最小的節點與距離
        if current_node == end: # 結束設定
            break
        # 更新鄰居節點的距離
        for (u, v), attrs in G.items():
            if u == current_node:
                distance = current_distance + 1
                if distance < distances[v]:
                    distances[v] = distance
                    previous_nodes[v] = current_node
                    heapq.heappush(priority_queue, (distance, v))

    # 輸出路徑
    path = []
    current = end
    while current is not None:
        path.append(current)
        current = previous_nodes[current]
    path.reverse()
    return path

"""製作 forzenset_mapping"""
def forzenset_mapping(dfa):
    forzenset_mapping = {}
    for node in dfa.final_states:
        forzenset_mapping[node] = node
    state = forzenset_mapping[node]
    return state

"""判斷 loop 有無更改衝突變數，若無則可加入 path"""
def update_path(path, cycle, unsat_condition, unsat_core):
    new_path = path.copy()
    new_unsat_core = unsat_core.copy()
    # is_connect = False
    is_connected = any(node in path for node in cycle)  # 檢查 loop 是否與 path 相連
    modified = False

    # 判斷 loop 與 最短路徑相連嗎
    for node in cycle: 
        if node in path:
            loop_start = path.index(node) + 1
            is_connected = True
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
    if is_connected == True and modified == False: 
        # 將 cycle 加入 path
        for node in cycle[1:]:  # 從第二個元素開始加
            new_path.insert(loop_start, node)
            loop_start = loop_start + 1
        return new_path, modified
    else :
        return path, modified

"""尋找 loop 方法"""
def dfs(v, visited, stack, all_cycles):  
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

""" 尋找圖中所有的 loop"""
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
G = dfa_operations.draw_dfa(total_dfa, edge_mapping)

# 找出第一條 trace
trace, dfa1 = find_trace(G, 'Nodeerr', edge_mapping, 'Node0', edges)

# 找出其他 trace
while complete == False:
    diff = total_dfa.difference(dfa1)
    G = dfa_operations.draw_dfa(diff, edge_mapping) # 畫出差集後的圖
    if(diff.isempty() != True): # 若差集完非空，則繼續找 trace
        trace, dfa2 = find_trace(G, forzenset_mapping(diff), edge_mapping, diff.initial_state, edges)
        total_dfa = diff
        dfa1 = dfa2
    else:
        complete = True
        print("complete")