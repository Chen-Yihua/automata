from graphviz import Digraph
from automata.fa.dfa import DFA

edge_mapping = {
    'p != 0': '0',
    'n >= 0': '1',
    'p == 0': '2',
    'n == 0': '3',
    'n != 0': '4',
    'p = 0': '5',
    'n = n - 1': '6'
}

# 將邊由文字改成編號
def get_key_from_value(mapping, value): 
    for key, val in mapping.items():
        if val == value:
            return key
    return None


# 從 symbol，取得表達式
def symbol_to_value(symbol):
    return get_key_from_value(edge_mapping, symbol)

# """畫出 dfa"""
def draw_dfa(dfa):
    G = {}
    dot = Digraph()
    states = dfa.states
    transitions = dfa.transitions
    final_states = dfa.final_states

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

"""從兩點找邊 symbol"""
def get_symbol(G, start , end):
    for edge in G.edges():
        if start == edge[0] and end == edge[1]:
            return edge.attr["label"]

"""從兩點找表達式"""
def find_edge(G, start , end):
    label = get_symbol(G, start , end)
    value = symbol_to_value(label)
    return value
    

"""製作 DFA"""
def build_dfa(G, path, mapping, initial_node, error_node, unsat_condition):
    states = set()
    input_symbols = set()
    unsat_node = []

    # 製作 input_symbols、states
    total_edges = G.edges()
    for start, end in total_edges:
        if initial_node != end:
            symbol = get_symbol(G, start, end)
            label = str(symbol_to_value(symbol))
            if start != end and symbol != '':
                input_symbols.add(symbol)
            if label == unsat_condition and start != end: # 找出 unsat node
                unsat_node.append(start)
            states.add(str(start))
    # 添加 reject state
    if unsat_condition != 0:
        states.add('reject_node')
    # 製作 transitions
    transitions = {state: {value: state for key, value in mapping.items()}
                   for state in states}  # 初始化 transition
    # 對於 path 中每個點，找出與此點相連的邊，並調整其 transition，將點相連
    for i in range(len(path)-1):
        for start, end in total_edges:
            symbol = get_symbol(G, start, end)
            if start == path[i] and end == path[i+1]:  
                transitions[str(path[i])][symbol] = str(end) 
            
    # 將 unsat node 連至 reject_node
    for node in unsat_node:
        if node not in path:
            transitions[str(node)][mapping.get(unsat_condition)] = 'reject_node'
            # 若 unsat_node 不在 path 裡，更改走進 unsat node 的邊
            for edge in G.edges():
                if edge[0] != edge[1]:
                    label = get_symbol(G, edge[0], edge[1])
                    if edge[1] == node:
                        transitions[str(edge[0])][label] = str(node)

    dfa = DFA(
        states = states,
        input_symbols = input_symbols,
        transitions = transitions,
        initial_state = str(initial_node),
        final_states = {str(error_node)}
    )
    return dfa