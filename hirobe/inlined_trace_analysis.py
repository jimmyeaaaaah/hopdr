import re
import sys
import json

pred_expressions = {}
pred_args = {}

class TreeNode:
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def __repr__(self):
        return f"TreeNode({self.value})"
    
def print_tree(root, level=0, prefix="Root: "):
    if root is not None:
        print(" " * (level * 4) + prefix + str(root.value))
        if root.left is not None or root.right is not None:
            if root.left:
                print_tree(root.left, level + 1, "L--- ")
            else:
                print(" " * ((level + 1) * 4) + "L--- None")
            if root.right:
                print_tree(root.right, level + 1, "R--- ")
            else:
                print(" " * ((level + 1) * 4) + "R--- None")

# 述語ごとに改行された形にする
def format_nuhfl(content):
    content = content.replace(".", " . ").replace("∀", " ∀ ").replace("∃", " ∃ ")
    terms = content.split()
    new_lines = []
    new_line = []
    quantifier = 0
    for term in terms:
        if term == "%HES":
            new_lines.append(term)
            continue
        if term == ".":
            if quantifier == 0:
                new_lines.append(" ".join(new_line))
                new_line = []
                continue
            else:
                quantifier -= 1
        if term == "∀" or term == "∃":
            quantifier += 1
        new_line.append(term)
    return new_lines

def get_pred_info(lines):
    global pred_expressions
    global pred_args
    for line in lines:
        is_left = True
        args = []
        expression = []
        terms = line.split()
        pred = terms[0]
        if pred.startswith("WF") or pred.startswith("RF"):
            continue
        for term in terms:
            if is_left:
                if term == "=v":
                    is_left = False
                    continue
                if term[0].islower():
                    args.append(term)
            else:
                expression.append(term)
        pred_expressions[pred] = expression
        pred_args[pred] = args

def build_tree(tokens):
    if len(tokens) == 0: 
        return None
    elif len(tokens) == 1:    # tokens = "1"
        return TreeNode(tokens[0])
    elif len(tokens) == 2:    # tokens = ["(", ")"]
        return None
    elif len(tokens) == 3:    # tokens = ["(" , "1", ")"]
        return TreeNode(tokens[1])
    tokens = tokens[1:-1]
    root_token = tokens.pop(0)
    if root_token == "app":
        pred = tokens.pop(0)
        root_token = root_token + " " + pred
    node = TreeNode(root_token)

    paren = 0
    left_tokens = []
    right_tokens = []
    is_left = True
    for token in tokens:
        if token == "(":
            paren += 1
        elif token == ")":
            paren -= 1
        if is_left:
            left_tokens.append(token)
            if paren == 0:
                is_left = False
        else:
            right_tokens.append(token)
    if root_token.startswith("app"):
        node.left = TreeNode(" ".join(left_tokens[1:-1]))
    else:
        node.left = build_tree(left_tokens)
    node.right = build_tree(right_tokens)
    return node

def remove_outer_paren(exp_terms):
    paren_idx_pair = []
    paren_start_idx_queue = []
    for i in range(len(exp_terms)):
        term = exp_terms[i]
        if term == "(":
            paren_start_idx_queue.append(i)
        elif term == ")":
            start_idx = paren_start_idx_queue.pop()
            paren_idx_pair.append([start_idx, i])
    n_outer_paren = 0
    paren_idx_pair = sorted(paren_idx_pair)
    paren_idx = 0
    for pair in paren_idx_pair:
        if pair[0] == paren_idx and (pair[0] + pair[1]) == len(exp_terms)-1:
            n_outer_paren += 1
            paren_idx += 1
        else:
            break
    if n_outer_paren != 0:
        exp_terms = exp_terms[n_outer_paren: -n_outer_paren]
    return exp_terms

def get_wf_from_trace_tree(exp_terms, root, assigned_values):
    # 外側についている括弧 "( x < 0 /\ y > 0 )"を取り除く
    exp_terms = remove_outer_paren(exp_terms)
    # print(" ".join(exp_terms))
    # print(root)
    if root is None:
        return [None, None, None]
    if exp_terms[0].startswith("WF"):
        return [exp_terms, assigned_values]
    if root.value == "univ":
        paren = 0
        for i in range(len(exp_terms)):
            term = exp_terms[i]
            if term == "∀":
                assigned_values[exp_terms[i+1]] = root.left.value
            if term == ".":
                exp_terms = exp_terms[i+1:]
                break
        return get_wf_from_trace_tree(exp_terms, root.right, assigned_values)
    elif root.value == "disj":
        left = []
        right = []
        is_left = True
        paren = 0
        for term in exp_terms:
            if term == "(":
                paren += 1
            elif term == ")":
                paren -= 1
            elif is_left and term == "\\/":
                if paren == 0:
                    is_left = False
                    continue
            if is_left:
                left.append(term)
            else:
                right.append(term)

        right_result = get_wf_from_trace_tree(right, root.right, assigned_values)
        left_result = get_wf_from_trace_tree(left, root.left, assigned_values)
        return right_result if left_result[0] is None else left_result
    elif root.value == "conj":
        select_left = root.left.value == "0"
        left = []
        right = []
        is_left = True
        paren = 0
        for term in exp_terms:
            if term == "(":
                paren += 1
            elif term == ")":
                paren -= 1
            elif term == "/\\":
                if paren == 0:
                    is_left = False
                    continue
            if is_left:
                left.append(term)
            else:
                right.append(term)
        if select_left:
            return get_wf_from_trace_tree(left, root.right, assigned_values)
        else:
            return get_wf_from_trace_tree(right, root.right, assigned_values)
    else:
        value = root.value
        token = value.split()[0]
        pred = value.split()[1]
        assigned_values = {}
        for i, arg in enumerate(pred_args[pred]):
            assigned_values[arg] = root.left.value.split()[i]
        if token == "app":
            return get_wf_from_trace_tree(pred_expressions[pred], root.right, assigned_values)
        else:
            raise ValueError("trace tree is invalud format")
def get_wf_args(wf):
    wf_args = []
    arg = []
    paren = 0
    for term in wf:
        if term[0].isupper():
            continue
        if term == "(":
            paren+=1
        elif term == ")":
            paren-=1
        arg.append(term)
        if paren == 0:
            wf_args.append(arg)
            arg = []
    if len(arg) != 0:
        wf_args.append(arg)
    return wf_args

def assign_value(wf_args, assigned_values):
    wf_assigned_values = []
    current_value = ""
    for arg in wf_args:
        for term in arg:
            if term in assigned_values.keys():
                current_value += assigned_values[term]
            else:
                current_value += term
        wf_assigned_values.append(eval(current_value))
        current_value = ""
    return wf_assigned_values

def analyze_trace(trace, lines):
    tokens = trace.replace("(", " ( ").replace(")", " ) ").split()
    root = build_tree(tokens)
    # print_tree(root)
    assigned_values = {}
    wf, assigned_values = get_wf_from_trace_tree(pred_expressions["Sentry"], root, assigned_values)
    wf_name = wf[0]
    wf_args = get_wf_args(wf)
    # print(wf, wf_args,  assigned_values)
    wf_assigned_values = assign_value(wf_args, assigned_values)
    # print(wf_assigned_values)
    return {"wf_name": wf_name, "assigned_values": wf_assigned_values}

def main():
    # inlining前のnuHFLファイル
    original_nuhfl_file = sys.argv[1]
    # inlining後のnuHFLのトレース
    trace_file = sys.argv[2]
    try:
        with open(original_nuhfl_file, 'r') as file:
            content = file.read()
    except FileNotFoundError:
        print(f"Error: File '{original_nuhfl_file}' not found.")
        sys.exit(1)
    try:
        with open(trace_file, 'r') as file:
            trace = file.read().strip()
    except FileNotFoundError:
        print(f"Error: File '{trace_file}' not found.")
        sys.exit(1)
    lines = format_nuhfl(content)
    get_pred_info(lines)
    # {"name": "WF1", "assigned_values": [1,0,1,2]}
    wf_info = analyze_trace(trace, lines)
    # print(wf_info)
    sys.stdout.write(json.dumps(wf_info) + "\n")

if __name__ == "__main__":
    main()
