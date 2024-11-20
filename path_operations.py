import heapq
import dfa_operations
from z3 import *
import unsat_core_operations


""" 找出圖中指定起點與終點的最短路徑 """
def dijkstra(G, end, start):
    # 初始化 (每個節點的初始距離為無限大、起始節點的為0)
    vertices = G.nodes()
    edges = G.edges()
    distances = {node: float('inf') for node in vertices}
    distances[start] = 0
    priority_queue = [(0, start)] 
    heapq.heapify(priority_queue) # 做 min heap，以選擇最短距離的節點
    previous_nodes = {node: None for node in distances} # 記錄前一個節點(從哪個點走來的)

    while priority_queue:
        current_distance, current_node = heapq.heappop(priority_queue) # 取當前距離最小的節點與距離
        if current_node == end: # 結束設定
            break
        # 更新鄰居節點的距離
        for u, v in edges:
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

# 尋找 loop 方法
def dfs(G, v, visited, stack, all_cycles):  
    stack.append(v) # 用來記錄從起點到當前節點的整個搜尋路徑，以判斷 loop 的位置
    visited.append(v) # 記錄已經拜訪過的節點
    # 找出 neighbor
    total_edges = G.edges()
    for start, end in total_edges:
        if v == start:
            neighbor = end
            if neighbor == v: # 如果 neighbor 等於 v，則跳過自我迴圈的檢查
                continue 
            if neighbor not in visited:
                dfs(G, neighbor, visited, stack, all_cycles)
            elif neighbor in stack: # 在 stack 找 neighbor 的位置
                cycle_start = stack.index(neighbor)
                cycle = stack[cycle_start:] + [neighbor]
                if cycle not in all_cycles:  # 若此 loop 沒被找過，則加入 loop 集合
                    all_cycles.append(tuple(cycle))
    stack.pop()
    visited.remove(v)

""" 尋找圖中所有的 loop path """
def find_all_cycles(G, start): 
    visited = []
    stack = []
    all_cycles = []

    dfs(G, str(start), visited, stack, all_cycles)
    return all_cycles

""" 找 unsat_core 在 path 中的位置"""
def find_core_index(G, core, path):
    core_index = []
    index = 0 # 紀錄查看到 path 的哪個位置
    for i in range(len(core)):
        for j in range(len(path)-1):
            edge = dfa_operations.find_edge(G, path[j] , path[j+1])
            if edge == str(core[i]) and j >= index:
                core_index.append(j)
                index = j
    return core_index

"""將 loop 加入 path """
def add_cycle(path, cycle):
    new_path = path.copy()
    # 判斷 loop 與 最短路徑相連嗎
    for node in cycle: 
        if node in path:
            loop_start = path.index(node) + 1
            initial_loop_start = loop_start
            is_connected = True
            break
    
     # 若相連，則將 loop 加入 path  
    if is_connected == True: 
        # 將 cycle 加入 path
        for node in cycle[1:]:  # 從第二個元素開始加
            new_path.insert(loop_start, node)
            loop_start = loop_start + 1
        return initial_loop_start, new_path

"""取得一條 path 的條件式"""
def get_path_conditions(assertions):
    tracked_conditions = {} # 用來追蹤此 infeasible path 經過哪些 statement
    path_conditions = [] # 存放更改變量後的條件式
    s = Solver()
    unsat_core_operations.tracked_wp(assertions, s, tracked_conditions, 0)
    
    for cond in tracked_conditions:
        path_conditions.append(str(tracked_conditions[cond]))
    return path_conditions

"""找出 path 用到的變量"""
def find_path_variable():
    return



