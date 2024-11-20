from asyncio.windows_events import NULL
from z3 import *
from automata.fa.dfa import DFA
import dfa_operations
import unsat_core_operations
import infeasible_proof
import path_operations
import get_interpolant


"""找出 trace 最短路徑，並建構證明"""
def find_trace(G, error_location, edge_mapping, start, edges, method="unsat_core"):
    found_path = False
    path, dfa, reject_start = None, None, None

    while not found_path:
        path = path_operations.dijkstra(G, str(error_location), str(start))  # 找到最短路径
        if method == "interpolant":
            assertions = infeasible_proof.weakest_precondition(G, path)
            conditions = path_operations.get_path_conditions(assertions)
            interpolant = get_interpolant.creat_interpolant(conditions)
        elif method == "unsat_core":
            proof_result, solver = infeasible_proof.proof(G, path)
            if proof_result == "unsat":
                unsat_var, unsat_core = unsat_core_operations.find_unsat_core(solver, edges)
                unsat_condition = unsat_core_operations.find_unsat_condition(G, unsat_var)
        else:
            raise ValueError("Unsupported method. Use 'interpolant' or 'unsat_core'.")
        found_path = True

    for cycle in path_operations.find_all_cycles(G, start):
        path_copy = path.copy()
        loop_start, new_path = path_operations.add_cycle(path_copy, cycle)
        if method == "interpolant":
            new_assertions = infeasible_proof.weakest_precondition(G, path)
            new_conditions = path_operations.get_path_conditions(new_assertions)
            new_interpolant = get_interpolant.creat_interpolant(new_conditions)
            if get_interpolant.check_interpolant_equality(interpolant, new_interpolant):
                path = new_path
            else:
                for node in cycle:
                    if node not in path:
                        reject_start = node
                        break
        elif method == "unsat_core":
            modified = check_changed_var(path, cycle, unsat_condition, unsat_core, loop_start)
            if not modified:
                path = new_path

    dfa = dfa_operations.build_dfa(G, path, edge_mapping, start, error_location, reject_start)
    dfa_operations.draw_dfa(dfa)
    dfa.show_diagram()
    return path, dfa

""" 判斷 loop 有無更改衝突變數，若無則可加入 path """
def check_changed_var(path, cycle, unsat_condition, unsat_core, loop_start):
    modified = False
    core_index = path_operations.find_core_index(G, unsat_core, path)

    # 檢查 unsat_condition 是否在它們之間，且變量有無被修改
    for i in range(len(core_index)-1):
        if core_index[i] < loop_start and core_index[i+1] >= loop_start:
            for j in range(len(cycle)-1):
                edge = dfa_operations.find_edge(G, cycle[j] , cycle[j+1])
                if edge == unsat_condition:
                    modified = True
                    break

    return modified

# main
complete = False  # 紀錄 trace 皆已取完了嗎
edges =['p != 0', 'n >= 0', 'p == 0', 'n == 0', 'n != 0', 'p = 0', 'n = n - 1']
start = 'Node0'
end = 'Nodeerr'

# 做初始 DFA
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
dfa_operations.draw_dfa(total_dfa)
G = total_dfa.show_diagram()

# 找出所有的 trace
while complete == False:
    trace, dfa = find_trace(G, end, dfa_operations.edge_mapping, start, edges)
    diff = total_dfa.difference(dfa)
    G = dfa_operations.draw_dfa(diff) # 畫出差集後的圖
    G = diff.show_diagram()
    if(diff.isempty() != True): # 若差集完非空，則繼續找 trace
        start = diff.initial_state
        end = dfa_operations.forzenset_mapping(diff.final_states)
        total_dfa = diff
    else:
        complete = True
        print("complete")