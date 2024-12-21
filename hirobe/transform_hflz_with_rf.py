import sys
import argparse
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
        if pred_parent == "%HES":
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
    # 改行を述語ごとに行う
    for c in contents:
        new_line += c
        if c == '∀' or c == '∃':
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
    # スペースを適切に入れる
    for i, line in enumerate(new_lines):
        line = line.replace("∀", " ∀ ").replace("∃", " ∃ ").replace(".", " . ").replace("(", " ( ").replace(")", " ) ").replace("=u", "=v").replace("  ", " ")
        new_lines[i] = line
    return new_lines

def substitute(arg_map, pred_expr_map, pred_parent, pred_delete):
    parent_exp = pred_expr_map[pred_parent]
    delete_exp = pred_expr_map[pred_delete]
    n_delete_exp_arg = len(delete_exp.split("=v")[0].split()) - 1
    delete_exp = delete_exp.split("=v")[1].rstrip(".")
    new_exp = []
    terms = parent_exp.split()
    is_target = False
    is_first_call = True
    target_args = []
    for term in terms:
        if term == pred_delete:
            is_target = True
            new_exp.append("(")
            continue
        if is_target == False:
            new_exp.append(term)
        else:
            target_args.append(term)
            if len(target_args) == n_delete_exp_arg:
                is_target = False
                if is_first_call:
                    for i, arg in enumerate(target_args):
                        delete_exp = delete_exp.replace(arg_map[pred_delete][i], arg)
                    del arg_map[pred_delete]
                new_exp.append(delete_exp)
                new_exp.append(")")
    new_exp = ' '.join(new_exp)
    pred_expr_map[pred_parent] = new_exp
    del pred_expr_map[pred_delete]
    return pred_expr_map

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


def create_wf_rf(pred, args, n_rf = 2):
    args1 = [s+"1" for s in args]
    args2 = [s+"2" for s in args]
    args_str = " ".join(args)
    args1_str = " ".join(args1)
    args2_str = " ".join(args2)
    if n_rf == 2:
        wf = f"WF_{pred} " + " ".join([f"rf{idx}" for idx in range(1, 3)]) + f" {args1_str} {args2_str}"
        wf_line = f"{wf} =v ∀ r1. ∀ r2. ∀ r3. ∀ r4. ( rf1 {args1_str} r1 \/ ( rf1 {args2_str} r2 \/ ( rf2 {args1_str} r3 \/ ( rf2 {args2_str} r4 \/ ( ( r1 >= 0  ) /\ ( r1 > r2 \/ ( r1 = r2 /\ ( r3 > r4 /\ r3 >= 0 ) ) ) ) ) ) ) )."
        rf_line = f"{args_str} r =v r <> 1."
        rf_lines = [f"RF_{pred}_{idx} " + rf_line for idx in range(1, 3)]
    else:
        wf = f"WF_{pred} " + " ".join([f"rf{idx}" for idx in range(1, len(args)+1)]) + f" {args1_str} {args2_str}"
        forall_r = "".join([f"∀ r{idx}. " for idx in range(1, len(args)*2+1)])
        r_disjunction = "".join([f"( rf{rf_idx} {args1_str} r{rf_idx*2-1} \/ ( rf{rf_idx} {args2_str} r{rf_idx*2} \/ " for rf_idx in range(1, len(args)+1)])
        r_positive = " /\ ".join([f"r{idx*2-1} >= 0" for idx in range(1, len(args)+1)])
        lexicographic = ["( r1 > r2 "] + [f"\/ ( r{idx*2-1} = r{idx*2} /\ ( r{idx*2+1} > r{idx*2+2} " for idx in range(1, len(args))] + [") " for idx in range(1, len(args)*2)]
        lexicographic = "".join(lexicographic)
        wf_line = wf + " =v " + forall_r + r_disjunction + "( ( " + r_positive + " ) /\\ " + lexicographic + ") "*len(args)*2 + ")."
        rf_line = f"{args_str} r =v r <> 1."
        rf_lines = [f"RF_{pred}_{idx} " + rf_line for idx in range(1, len(args)+1)]
    return wf_line, rf_lines


def add_ranking_function(lines, arg_map, sccs):
    p_arg_map = {}
    for key, value in arg_map.items():
        p_arg_map[key] = [f"p{arg}_{key.lower()}" for arg in value]
    new_lines = []
    wf_list = []
    rf_list = []
    has_wf = []
    for line in lines:
        line = line.replace(".", " .")
        if line.startswith("%HES"):
            new_lines.append(line)
            continue
        new_line = []
        terms = line.split()
        pred_parent = ""
        pred = ""
        args_called = []
        paren = []
        is_left = True
        # 各述語の1つ前の値を格納する変数
        p_args = [p_arg for sublist in p_arg_map.values() for p_arg in sublist]
        # isFirstのフラグを格納する変数
        is_first_args = [f"is_first_{pred_name.lower()}" for pred_name in arg_map.keys()]
        for term in terms:
            if is_left:
                if term == "=v":
                    if pred_parent == "Sentry":
                        new_line = [f"{pred_parent} =v"]
                    else:
                        new_line = [pred_parent] + is_first_args + p_args + args_called + ["=v"]
                    is_left = False
                    args_called = []
                    continue
                if term[0].isupper():
                    pred_parent = term
                else:
                    args_called.append(term)
            else:
                if term[0].isupper():
                    pred = term
                    continue
                if pred != "":
                    # 述語が引数をとらない場合
                    if (len(arg_map[pred]) == 0):
                        new_line = new_line + [pred] + is_first_args + p_args + [term]
                        pred = ""
                        continue
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
                    # 述語の呼び出しに対して、WFを追加
                    if (len(arg_map[pred]) == len(args_called)):
                        # previous変数に代入する値
                        p_args_substituted = []
                        for key in p_arg_map.keys():
                            if key == pred:
                                p_args_substituted = p_args_substituted + args_called
                            elif key == pred_parent:
                                p_args_substituted = p_args_substituted + arg_map[pred_parent]
                            else:
                                p_args_substituted = p_args_substituted + p_arg_map[key]
                        # is_firstに代入する値
                        is_first_values = []
                        for p in arg_map.keys():
                            if p ==pred_parent and sccs[pred_parent] == sccs[pred]:
                                is_first_values.append("0")
                            elif p != pred_parent and sccs[pred_parent] != sccs[pred]:
                                is_first_values.append("1")
                            else:
                                is_first_values.append(f"is_first_{p.lower()}")
                        if pred_parent == "Sentry":
                            new_line = new_line + [f"{pred}"] + is_first_values +  ["0" for _ in range(len(p_args))] + args_called
                        else:
                            new_line = new_line + [f"( {pred}"] + is_first_values + p_args_substituted + args_called + \
                                [f"/\ ( is_first_{pred.lower()} = 1 \/ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, 3)] + \
                                p_arg_map[pred] + args_called + [") )"]
                        if pred not in has_wf:
                            wf, rfs = create_wf_rf(pred, arg_map[pred])
                            wf_list.append(wf)
                            rf_list = rf_list + rfs
                            has_wf.append(pred)
                        pred = ""
                        args_called = []
                    continue
                new_line.append(term)
        new_line = ' '.join(new_line)
        new_lines.append(new_line)
    new_lines += wf_list
    new_lines += rf_list
    return new_lines


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("hflz_filename", help="Input file name")
    args = parser.parse_args()
    try:
        with open(args.hflz_filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{args.hflz_filename}' not found.")
        sys.exit(1)
    lines = reform(lines)
    arg_map = get_arg_map(lines)
    sccs = get_sccs(lines)
    lines = add_ranking_function(lines, arg_map, sccs)
    content = "\n".join(lines)
    if args.hflz_filename.endswith("negated_opt.in"):
        output_file = "/".join(args.hflz_filename.split("/")[:-1])+"/rf_lexico_disprover.in"
    else:
        output_file = "/".join(args.hflz_filename.split("/")[:-1])+"/rf_lexico_prover.in"
    with open(output_file, 'w') as file:
        file.write(content)
    print(output_file)

if __name__ == "__main__":
    main()
