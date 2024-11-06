from graphviz import Digraph
from automata.fa.dfa import DFA

# 將邊由編號改成文字
def get_key_from_value(mapping, value): 
        for key, val in mapping.items():
            if val == value:
                return key
        return None

"""畫出 dfa"""
def draw_dfa(dfa, edge_mapping):
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

"""製作 DFA"""
def build_dfa(G, path, mapping, start, end, unsat_condition):
    states = set()
    input_symbols = set()
    unsat_node = []

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