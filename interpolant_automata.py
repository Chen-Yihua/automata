from asyncio.windows_events import NULL
from z3 import *
from automata.fa.dfa import DFA
import heapq
import get_interpolant
import dfa_operations
import unsat_core_operations
import infeasible_proof
import path_operations

"""找出 trace 最短路徑，並建構證明"""
def find_trace(G, error_location, edge_mapping, start, edges):
    found_path = False
    path, dfa, reject_start = None, None, None

    while found_path == False:
        path = path_operations.dijkstra(G, str(error_location), str(start))  # 找出走到 error location 的最短 path
        assertions = infeasible_proof.weakest_precondition(G, path) # 將條件式做 imply
        conditions = unsat_core_operations.get_path_conditions(assertions) # 分解 imply，並更新變量
        interpolant = get_interpolant.creat_interpolant(conditions)
        found_path = True # 找到最短路徑

    for cycle in path_operations.find_all_cycles(G, start): # 找出程式中的 loop
        path_copy = path.copy()
        new_path = update_path(path_copy, cycle)  # 將 loop 加入 path
        new_assertions = infeasible_proof.weakest_precondition(G, path) # 將條件式做 imply
        new_conditions = unsat_core_operations.get_path_conditions(new_assertions)
        new_interpolant = get_interpolant.creat_interpolant(new_conditions)
        if interpolant == new_interpolant:
            # 若實際程式走不到且 unsat core 一樣，以此新的 path 更新 dfa
            path = new_path
        else : 
            for i in range(len(cycle)):
                if cycle[i] not in path:
                    reject_start = cycle[i]
                    break
    dfa = dfa_operations.build_dfa(G, new_path, edge_mapping, start, error_location, reject_start)
    dfa_operations.draw_dfa(dfa)  # 畫出 p 之 dfa
    dfa.show_diagram()
    return path, dfa

"""製作 forzenset_mapping"""
def forzenset_mapping(dfa):
    forzenset_mapping = {}
    for node in dfa.final_states:
        forzenset_mapping[node] = node
    state = forzenset_mapping[node]
    return state

"""判斷 loop 有無更改衝突變數，若無則可加入 path"""
def update_path(path, cycle):
    new_path = path.copy()
    # # 判斷 loop 與 最短路徑相連嗎
    for node in cycle: 
        if node in path:
            loop_start = path.index(node) + 1
            is_connected = True
            break
    
     # 若相連，且變量未被修改，則將 loop 加入 path  
    if is_connected == True: 
        # 將 cycle 加入 path
        for node in cycle[1:]:  # 從第二個元素開始加
            new_path.insert(loop_start, node)
            loop_start = loop_start + 1
        return new_path

# main
complete = False  # 紀錄 trace 皆已取完了嗎
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
G = total_dfa.show_diagram()

# 找出第一條 trace
trace, dfa1 = find_trace(G, 'Nodeerr', dfa_operations.edge_mapping, 'Node0', edges)

# 找出其他 trace
while complete == False:
    diff = total_dfa.difference(dfa1)
    G = dfa_operations.draw_dfa(diff) # 畫出差集後的圖
    G = diff.show_diagram()
    if(diff.isempty() != True): # 若差集完非空，則繼續找 trace
        trace, dfa2 = find_trace(G, forzenset_mapping(diff), dfa_operations.edge_mapping, diff.initial_state, edges)
        total_dfa = diff
        dfa1 = dfa2
    else:
        complete = True
        print("complete")