import sys
from collections import defaultdict

class Graph:
    def __init__(self):
        self.graph = defaultdict(list)
        self.node_to_index = {}
        self.index_to_node = {}
        self.time = 0
        self.current_index = 0

    def add_edge(self, u, v):
        """辺を追加する（文字列ノード対応）"""
        if u not in self.node_to_index:
            self.node_to_index[u] = self.current_index
            self.index_to_node[self.current_index] = u
            self.current_index += 1
        if v not in self.node_to_index:
            self.node_to_index[v] = self.current_index
            self.index_to_node[self.current_index] = v
            self.current_index += 1
        self.graph[self.node_to_index[u]].append(self.node_to_index[v])

    def tarjan_scc(self):
        """Tarjanのアルゴリズムで強連結成分を見つける"""
        vertices = self.current_index
        disc = [-1] * vertices
        low = [-1] * vertices
        stack_member = [False] * vertices
        stack = []
        sccs = []

        def scc_util(u):
            """Tarjanの補助関数"""
            nonlocal sccs
            disc[u] = low[u] = self.time
            self.time += 1
            stack.append(u)
            stack_member[u] = True

            for v in self.graph[u]:
                if disc[v] == -1:  # 未訪問
                    scc_util(v)
                    low[u] = min(low[u], low[v])
                elif stack_member[v]:  # スタックにある
                    low[u] = min(low[u], disc[v])

            if low[u] == disc[u]:
                scc = []
                while True:
                    w = stack.pop()
                    stack_member[w] = False
                    scc.append(self.index_to_node[w])  # インデックスを元のノード名に戻す
                    if w == u:
                        break
                sccs.append(scc)

        for i in range(vertices):
            if disc[i] == -1:
                scc_util(i)

        return sccs

def get_sccs(lines):
    g = Graph()
    for line in lines:
        terms = line.split()
        pred_parent = terms[0]
        if pred_parent == "%HES" or pred_parent == "Sentry":
            continue
        for term in terms[1:]:
            if term[0].isupper():
                pred = term
                g.add_edge(pred_parent, pred)
    sccs = g.tarjan_scc()
    sccs_dict = {}
    for i, scc in enumerate(sccs):
        for pred in scc:
            sccs_dict[pred] = i
    return sccs_dict

def reform(lines):
    contents = ' '.join(line.strip() for line in lines)
    quantifier_stack = []
    new_lines = []
    new_line = ""
    for c in contents:
        new_line += c
        if c == '∀':
            quantifier_stack.append(c)
        if c == '.':
            if len(quantifier_stack) == 0:
                if new_line.startswith("%HES"):
                    new_lines.append("%HES")
                    new_lines.append(' '.join(new_line.split()[1:]))
                else:
                    new_lines.append(new_line)
                new_line = ""
            else:
                quantifier_stack.pop()
    for i in range(len(new_lines)):
        line = new_lines[i]
        new_lines[i] = line.replace("=u", "=v").replace(".", " .").strip()
    return new_lines


def get_arg_map(lines):
    arg_map = {}
    for line in lines:
        if line.startswith("%HES") or line.startswith("Sentry"):
            continue
        terms = line.split()
        pred = terms[0]
        arg_map[pred] = []
        for term in terms:
            if term == "=v":
                break
            else:
                if term != pred:
                    arg_map[pred].append(term)
    return arg_map


def create_wf_rf(pred, arg_map, wf_idx):
    args = arg_map[pred]
    args_p = ["p"+s for s in args]
    args_str = " ".join(args)
    args_p_str = " ".join(args_p)
    wf = f"WF_{pred}_{wf_idx} {args_p_str} {args_str} =v ∀r1. ∀r2. RF_{pred}_{wf_idx} {args_p_str} r1 \/ RF_{pred}_{wf_idx} {args_str} r2 \/ (r1 >= 0 /\ r1 > r2)."
    rf = f"RF_{pred}_{wf_idx} {args_str} r =v r <> 1."
    return wf, rf

def create_d_line(arg_map, n_call_map):
    d_lines = []
    for pred in arg_map.keys():
        if len(arg_map[pred]) == 0:
            continue
        args = arg_map[pred]
        args_p = [f"p{arg}" for arg in args]
        args_str = " ".join(args)
        args_p_str = " ".join(args_p)
        d_line = f"D_{pred} isDummy {args_p_str} {args_str} =v isDummy = 1 " +  \
            " ".join([f"\/ WF_{pred}_{i} {args_p_str} {args_str}" for i in range(1, n_call_map[pred]+1)]) + "."
        d_lines.append(d_line)
    return d_lines

def add_ranking_function(lines, arg_map, sccs):
    pred_list = list(arg_map.keys())
    arg_map_with_pred = {pred: [f"{arg}_{pred.lower()}" for arg in args] for pred, args in arg_map.items()}
    print(arg_map_with_pred)
    args_full = []
    for args in arg_map_with_pred.values():
        args_full += args
    new_lines = []
    wf_list = []
    rf_list = []
    n_call_map = {}
    for line in lines:
        if line.startswith("%HES"):
            new_lines.append(line)
            continue
        new_line = []
        terms = line.split()
        paren = []
        pred = ""
        pred_parent = ""
        args_called = []
        is_left = True
        is_Sentry = False
        for term in terms:
            if term == "Sentry":
                is_Sentry = True
                continue
            if is_left:
                if term[0].isupper():
                    pred_parent = term
                    continue
                if term == "=v":
                    is_left = False
                    if is_Sentry:
                        new_line.append("Sentry =v")
                    else:
                        new_line.append(pred_parent)
                        new_args = [f"isDummy_{pred.lower()}" for pred in pred_list] + [f"p{arg}" for arg in args_full] + args_full
                        new_line = new_line + new_args + ["=v"]
                        if len(arg_map[pred_parent]) != 0:
                            new_line = new_line + [f"D_{pred_parent} isDummy_{pred_parent.lower()}"] + ["p"+arg for arg in arg_map_with_pred[pred_parent]] + arg_map_with_pred[pred_parent] + ["/\\ ("]
                        else:
                            new_line.append("(")
                        n_call_map[pred_parent] = 0
                        continue
            else:
                if is_Sentry == False:
                    for variable in arg_map[pred_parent]:
                        term = term.replace(variable, f"{variable}_{pred_parent.lower()}")
                if term[0].isupper():
                    pred = term
                    if len(arg_map[pred]) == 0:
                        new_line += [f"{pred}"] + [f"isDummy_{pred.lower()}" for pred in pred_list] + [f"p{arg}" for arg in args_full] + args_full
                        pred = ""
                    continue
                if pred != "":
                    if term == "(":
                        paren.append("(")
                    elif term == ")":
                        paren.append(")")
                        args_called.append(" ".join(paren))
                        paren = []
                    else:
                        if len(paren) == 0:
                            args_called.append(term)
                        else:
                            paren.append(term)
                    if (len(arg_map_with_pred[pred]) == len(args_called)):
                        if is_Sentry:
                            args_entry = ["0" for i in range(len(args_full))]
                            for p in arg_map.keys():
                                if p == pred:
                                    args_entry += args_called
                                else:
                                    args_entry += ["0" for i in range(len(arg_map[p]))]
                            new_line = new_line + [f"{pred}"] + ["1" for i in range(len(pred_list))] + args_entry
                        else:
                            is_dummy_values = []
                            next_args = []
                            for p in arg_map_with_pred.keys():
                                if p == pred:
                                    next_args += args_called
                                else:
                                    next_args += arg_map_with_pred[p]      
                            for p in pred_list:
                                if p == pred_parent and sccs[pred_parent] == sccs[pred]:
                                    is_dummy_values.append("0")                       
                                else:
                                    is_dummy_values.append(f"isDummy_{p.lower()}")
                            new_line = new_line + \
                                [f"( {pred}"] + [f"isDummy_{p.lower()}" for p in pred_list] + ["p"+arg for arg in args_full] + next_args + ["/\\"] + \
                                [f"{pred}"] + is_dummy_values + args_full + next_args + [")"]
                            n_call_map[pred_parent] += 1
                            wf, rf = create_wf_rf(pred_parent, arg_map_with_pred, n_call_map[pred_parent])
                            wf_list.append(wf)
                            rf_list.append(rf)
                        pred = ""
                        args_called = []
                else:
                    new_line.append(term)
        new_line = ' '.join(new_line)
        if is_Sentry == False:
            new_line = new_line[:-1] + ")."
        new_lines.append(new_line)
    # args = arg_map[list(arg_map.keys())[0]] # そのうち直す、ほんとは共通の引数を取るべき
    d_lines = create_d_line(arg_map_with_pred, n_call_map)
    new_lines = new_lines + d_lines
    new_lines += wf_list
    new_lines += rf_list
    return new_lines


def main():
    filename = sys.argv[1]
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    lines = reform(lines)
    arg_map = get_arg_map(lines)
    sccs = get_sccs(lines)
    lines = add_ranking_function(lines, arg_map, sccs)
    content = "\n".join(lines)
    output_file = "/".join(filename.split("/")[:-1])+"/disjunctive_wf.in"
    with open(output_file, 'w') as file:
        file.write(content)


if __name__ == "__main__":
    main()
