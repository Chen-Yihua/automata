from z3 import *
from graphviz import Digraph
from automata.fa.dfa import DFA
import heapq

# 畫出 Control flow graph (圖要用程式判斷有幾個節點和邊，還是照圖畫)
def cfw(G):
    dot = Digraph() # 創建圖

    for (i, j), label in G.items(): # 畫點與邊
        dot.edge(i, j, label = label['label'])
        # if i not in all_nodes: all_nodes.append(i)
        # if j not in all_nodes: all_nodes.append(j)
   
    # dot.render('cfg', format='png', view=True)  # render 圖片
    
    return G

# 找出 trace 最短路徑，並建構證明
def trace(G,error_location,shortest_error_path):
    if taken == False: # 取第一條 error trace
        taken == True
    # else: # 做差集
    shortest_error_path = dijkstra(G, error_location) # 找 trace
    print("shortest_error_path :", shortest_error_path)
    weakest_precondition(True, False, shortest_error_path) # 計算 notation
    build_dfa(G,shortest_error_path)
    return shortest_error_path

# 找出最短路徑
def dijkstra(G, end):
    nodes = set() # 存放節點與邊
    for edge in G:
        u, v = edge
        nodes.add(u)
        nodes.add(v)

    # 初始化 (每個節點的初始距離為無限大、起始節點的為0)
    distances = {node: float('inf') for node in set(x for edge in G.keys() for x in edge)}
    distances['Node0'] = 0

    # 做 min heap，以選擇最短距離的節點
    priority_queue = [(0, 'Node0')]
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
                new_distance = current_distance + distance
                if new_distance < distances[v]:
                    distances[v] = new_distance
                    previous_nodes[v] = current_node
                    heapq.heappush(priority_queue, (new_distance, v))

    # 輸出路徑
    path = []
    node = end
    while node is not None:
        path.append(node)
        node = previous_nodes[node]
    path.reverse()

    return path

def if_(cond, t, e):
    return lambda post: Or(Implies(cond, t(post)) , And(Not(cond), e(post)))

def assert_(prop):
    return lambda post: And(post, prop)

def set_(v, e): # 將後置條件 post 中的 v 替換為 e，不會用到
    return lambda post: substitute(post,(v, e))   

def assume_(prop):
    return lambda post: Implies(prop, post)

def verify_fun(pre, post, body):
    s = Solver()
    s.add(pre)
    
    wp_expr = Implies(pre, body(post))
    s.add(Not(wp_expr))
    
    if s.check() == unsat:
        print("Correct")
    else:
        print("Counterexample found:")
        print(s.model())

def begin(*args):
    def res(post):
        wp = post
        for s in reversed(args):
            wp = s(wp)
        return wp
    return res

skip = lambda post: post

# 利用precondition+z3，算出annotation，Construct proof
def weakest_precondition(pre, post, path):
    # for i in range(len(path)-1, 0, -1):
    #     edge = G[path[i-1], path[i]] # 取出 trace 中的邊
    #     label = edge['label'] # 取得邊的內容
    #     # eval(label) # 將邊轉成 z3 可讀的形式
    #     # print(label)
    #     prog1 = begin(
    #     label
    #     )
    #     verify_fun(pre, p==0, prog1)
        
    p, n = Ints("p n")
    prog1 = begin(
        assume_(p!=0),
        if_(n>=0,assert_(p!=0),skip),  
        set_(n,n-1)
    )  
    
    verify_fun(pre, p==0, prog1)

    # s = Solver()
    # for i in range(len(path)-1, 0, -1):
    #     edge = G[path[i-1], path[i]] # 取出 trace 中的邊
    #     label = edge['label'] # 取得邊的內容
    #     wp = eval(label) # 將邊轉成 z3 可讀的形式
    #     pre = And(wp, pre) # 將前置條件與 transitions 做 and 操作
    #     post = Implies(pre, post)
    #     print(post)
    #     s.add(pre)
    
    # s.add(Not(post))
    # if s.check() == sat:
    #     print("True")
    # else:
    #     print("False")

# 做 DFA
def build_dfa(G,path):
    states = set()
    input_symbols = set()
    mapping = {}

    # 製作 statement 與其編號之  mapping
    for i in range(len(path)-1):
        for edge,properties in G.items():
            if edge[0] == path[i] and edge[1] == path[i+1]:
                mapping[properties['label']] = f'{i}'
                break
        input_symbols.add(f'{i}') # 製作 input_symbols

    for i in range(len(path)): # 製作 state
        states.add(f'{path[i]}')
        
    transitions = {state: {value: state for key, value in mapping.items()} for state in states} # 初始化 transition
    for i in range(len(path)): # 對於 path 中每個點
        for edge,properties in G.items(): 
            if path[i] in edge[0]: # 找出與此點相連的邊
                transitions[path[i]][mapping.get(properties['label'])] = edge[1] # 更改連接的邊
                break

    dfa = DFA(
        states = states,
        input_symbols = input_symbols,
        transitions = transitions, 
        initial_state = 'Node0',
        final_states = {'Nodeerr'}
    )

    # 測試 DFA
    test_strings = ['01','000']

    for string in test_strings:
        if dfa.accepts_input(string):
            print(f"The string '{string}' is accepted by the DFA.")
        else:
            print(f"The string '{string}' is not accepted by the DFA.")

    return dfa


# main
G = {
        ('Node0', 'Node1'): {'label': 'p != 0'},
        ('Node1', 'Node2'): {'label': 'n >= 0'},
        ('Node1', 'Node5'): {'label': 'n <= 0'},
        ('Node2', 'Nodeerr'): {'label': 'p == 0'},
        ('Node2', 'Node3'): {'label': 'n == 0'},
        ('Node2', 'Node4'): {'label': 'n != 0'},
        ('Node3', 'Node4'): {'label': 'p := 0'},
        ('Node4', 'Node1'): {'label': 'n--'},
    }

shortest_error_path = ""
taken = False # 紀錄取過 trace 了嗎
complete = False # 紀錄 trace 皆已取完了嗎
all_nodes = [] # 收集點，做 dfa 用

cfw(G)
# 找出trace1路徑(錯誤位置要怎麼判斷，用Z3一個一個節點判斷嗎，但若節點很多怎麼辦)
# while complete == False:
trace(G,'Nodeerr',shortest_error_path)
# trace(G,'Node2',shortest_error_path)

# 做 DFA
dfa1 = DFA(
    states={'q0', 'q1', 'q2', 'q3', 'q4', 'q5', 'qerr'},
    input_symbols={'0', '1', '2', '3', '4', '5', '6', '7'},
    transitions={
        'q0': {'0': 'q1','1':'q0', '2':'q0', '3':'q0', '4':'q0', '5':'q0', '6':'q0', '7':'q0'},
        'q1': {'1': 'q2','2': 'q5','0':'q1', '3':'q1', '4':'q1', '5':'q1', '6':'q1', '7':'q1'},
        'q2': {'3': 'q4', '4': 'q3','5': 'qerr','0':'q2', '1':'q2', '2':'q2', '6':'q2', '7':'q2'},
        'q3': {'6': 'q4','0':'q3','1':'q3', '2':'q3', '3':'q3', '4':'q3', '5':'q3','7':'q3'},
        'q4': {'7': 'q1','0': 'q4','1':'q4', '2':'q4', '3':'q4', '4':'q4', '5':'q4', '6':'q4'},
        'q5':{'0': 'q5','1':'q5', '2':'q5', '3':'q5', '4':'q5', '5':'q5', '6':'q5', '7':'q5'},
        'qerr': {'0': 'qerr','1':'qerr', '2':'qerr', '3':'qerr', '4':'qerr', '5':'qerr', '6':'qerr', '7':'qerr'}
    },
    initial_state='q0',
    final_states={'qerr'}
)

mapping = {
    'p!=0': '0',
    'n>=0': '1',
    'n<0': '2',
    'n!=0': '3',
    'n==0': '4',
    'p==0': '5',
    'p:=0': '6',
    'n--':'7'
}

def map_string(s):
    return mapping.get(s, 'Unknown')

if dfa1.accepts_input(map_string('p!=0')+map_string('n>=0')+map_string('p==0')):
        print("accept")

# 測試 DFA
test_strings = ['010', '110', '015', '013715']

for string in test_strings:
    if dfa1.accepts_input(string):
        print(f"The string '{string}' is accepted by the DFA.")
    else:
        print(f"The string '{string}' is not accepted by the DFA.")
