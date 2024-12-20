import re
import sys
import json


class TreeNode:
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def __repr__(self):
        return f"TreeNode({self.value})"


class CounterExample:
    def __init__(self, pred_name, pred_args, s_exp, tree=None):
        self.pred_name = pred_name
        self.pred_args = pred_args
        self.s_exp = s_exp
        self.tree = tree

    def __repr__(self):
        return f"CounterExample( \n pred_name = {self.pred_name} \n pred_args = {self.pred_args} \n s_exp = {self.s_exp}\n)"


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
                new_line.append(".")
                new_lines.append(" ".join(new_line))
                new_line = []
                continue
            else:
                quantifier -= 1
        if term == "∀" or term == "∃":
            quantifier += 1
        new_line.append(term)
    return new_lines


# 最後に呼び出されている述語(失敗したWFが呼び出されている述語)のみ抜き出す
def extract_and_format_trace(trace):
    tokens = trace.replace("(", " ( ").replace(")", " ) ").split()
    formatted_trace = ""
    parens = []
    end_app = 0
    start_app_idx = 0
    for i in range(len(tokens)):
        token = tokens[i]
        if token == "(":
            parens.append("(")
        elif token == ")":
            if len(parens) == end_app:
                formatted_trace = " ".join(tokens[start_app_idx:i])
                break
            parens.pop()
        elif token == "app":
            start_app_idx = i
            end_app = len(parens)
    # 得られたtraceについて、述語の名前、引数、右側の式を抽出
    tokens = formatted_trace.split()
    if tokens[0] != "app":
        raise ValueError("formatted trace is invalid")
    pred_name = ""
    is_args = True
    pred_args = []
    pred_exp = []
    for token in tokens:
        if token == "app":
            continue
        if token[0].isupper():
            pred_name = token
            continue
        if is_args:
            if token != "(" and token != ")":
                pred_args.append(token)
            if token == ")":
                is_args = False
        else:
            if re.fullmatch(r'^[0-9-]+$', token):
                pred_exp.append("(")
                pred_exp.append(token)
                pred_exp.append(")")
            else:
                pred_exp.append(token)
    pred_exp = " ".join(pred_exp)
    counter_example = CounterExample(pred_name, pred_args, pred_exp)
    return counter_example

def s_exp_to_binary_tree(s_expr):
    tokens = s_expr.replace("(", " ( ").replace(")", " ) ").split()
    return build_tree(tokens)

def build_tree(tokens):
    if len(tokens) == 2:    # tokens = ["(", ")"]
        return None
    if len(tokens) == 3:    # tokens = ["(" , "1", ")"]
        return TreeNode(tokens[1])
    tokens = tokens[1:-1]
    root_token = tokens.pop(0)
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
    node.left = build_tree(left_tokens)
    node.right = build_tree(right_tokens)
    return node

# trace treeを辿って、inline前のnuHFLにおける失敗したWFを取得する
def get_wf_info_from_trace_tree(formatted_trace, original_nuhfl_file):
    pred = ""
    for line in original_nuhfl_file:
        if line.split()[0] == formatted_trace.pred_name:
            pred = line
            break
    # 述語の引数と、それに代入された値のmap
    assigned_values = {}
    pred_left = pred.split("=v")[0]
    args = pred_left.split()[1:]     # 述語名を除いた引数のみ
    for i in range(len(args)):
        assigned_values[args[i]] = formatted_trace.pred_args[i]

    exp_str = pred.split("=v")[1]
    # conjunctionを優先するように括弧をつける？
    # exp_strを、formatted_trace.treeに従って走査していく
    assigned_values_forall = {}
    exp_terms = exp_str.replace("(", " ( ").replace(")", " ) ").split()
    # ピリオドを取り除く
    exp_terms = exp_terms[:-1] if exp_terms[-1] == "." else exp_terms

    # WFを取得
    wf, wf_trace, assigned_values_forall = get_wf_from_trace_tree(
        exp_terms, formatted_trace.tree, assigned_values_forall)
    print(wf, wf_trace, assigned_values_forall)
    assigned_values.update(assigned_values_forall)
    wf_name = wf[0]

    # # WFの中に含まれる算術式を取得
    # wf_str = "( r1 >= 0 /\ r3 >= 0 ) /\ ( r1 > r2 \/ ( r1 = r2 /\ ( r3 > r4 ) ) )"
    # wf_terms = wf_str.split()
    # arith = get_arith_in_wf_from_trace_tree(wf_terms, wf_trace)
    # arith = " ".join(arith)

    # WFの引数に、失敗パスで呼び出した値を代入
    wf_args = " ".join(wf[3:]).replace("+", " + ").replace("-", " - ").split()
    print(wf_args, assigned_values)
    wf_assigned_values = assign_value(wf_args, assigned_values)
    return {"wf_name": wf_name, "assigned_values": wf_assigned_values}

def assign_value(wf_args, assigned_values):
    wf_assigned_values = []
    paren = 0
    current_value = ""
    for term in wf_args:
        if term == "(":
            paren += 1
        elif term == ")":
            paren -= 1
        else:
            if re.fullmatch(r"[-+*]?[\d]*", term):      # termが変数でない
                current_value += term
            else:
                current_value += assigned_values[term]
        if paren == 0:
            wf_assigned_values.append(eval(current_value))
            current_value = ""
    return wf_assigned_values

def is_arithmetic(exp_terms):
    res = False
    for term in exp_terms:
        if term == "\\/" or term == "/\\" or term == "∀":
            return False
        if term == "<" or term == "<=" or term == ">" or term == ">=" or term == "=" or term == "==":
            res = True
    return res

# WFを探す
def get_wf_from_trace_tree(exp_terms, root, assigned_values_forall):
    # 外側についている括弧 "( x < 0 /\ y > 0 )"を取り除く
    exp_terms = remove_outer_paren(exp_terms)
    print(" ".join(exp_terms))
    print(root)
    if root is not None:
        print(root.left, root.right)
    if len(exp_terms) == 0 or root is None:
        return [None, None, None]
    if exp_terms[0].startswith("WF"):
        return [exp_terms, root, assigned_values_forall]
    if is_arithmetic(exp_terms):
        return [None, None]
    if root.value == "univ":
        paren = 0
        for i in range(len(exp_terms)):
            term = exp_terms[i]
            if term == "∀":
                assigned_values_forall[exp_terms[i+1]] = root.left.value
            if term == ".":
                exp_terms = exp_terms[i+1:]
                break
        return get_wf_from_trace_tree(exp_terms, root.right, assigned_values_forall)
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

        right_result = get_wf_from_trace_tree(
            right, root.right, assigned_values_forall)
        left_result = get_wf_from_trace_tree(
            left, root.left, assigned_values_forall)
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
            return get_wf_from_trace_tree(left, root.right, assigned_values_forall)
        else:
            return get_wf_from_trace_tree(right, root.right, assigned_values_forall)
    else:
        raise ValueError("trace tree is invalud format")

# WFの中に含まれる算術式を取得
def get_arith_in_wf_from_trace_tree(exp_terms, root):
    # 外側についている括弧 "( ( x < 0 /\ y > 0 ) )"を取り除く
    exp_terms = remove_outer_paren(exp_terms)
    if is_arithmetic(exp_terms):
        return exp_terms
    if len(exp_terms) == 0 or root is None:
        return None
    if root.value == "univ":
        paren = 0
        for i in range(len(exp_terms)):
            term = exp_terms[i]
            if term == ".":
                exp_terms = exp_terms[i+1:]
                break
        return get_arith_in_wf_from_trace_tree(exp_terms, root.right)
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
            elif term == "\\/":
                if paren == 0:
                    is_left = False
                    continue
            if is_left:
                left.append(term)
            else:
                right.append(term)
        right_result = get_arith_in_wf_from_trace_tree(right, root.right)
        left_result = get_arith_in_wf_from_trace_tree(left, root.left)
        return left_result if right_result[0] is None else right_result
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
            return get_arith_in_wf_from_trace_tree(left, root.right)
        else:
            return get_arith_in_wf_from_trace_tree(right, root.right)
    else:
        raise ValueError("trace tree is invalud format")

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


def analyze_trace(trace, lines):
    formatted_trace = extract_and_format_trace(trace)
    trace_tree = s_exp_to_binary_tree(formatted_trace.s_exp)
    formatted_trace.tree = trace_tree
    wf_info = get_wf_info_from_trace_tree(formatted_trace, lines)
    return wf_info  # {"name": "WF1", "assigned_values": [1,0,1,2]}


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
    # {"name": "WF1", "assigned_values": [1,0,1,2], "failed_arith": "r3 < r4"}
    wf_info = analyze_trace(trace, lines)
    print(wf_info)
    sys.stdout.write(json.dumps(wf_info) + "\n")


if __name__ == "__main__":
    main()
