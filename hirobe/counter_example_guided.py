import argparse
import numpy as np
import sympy as sp
from z3 import *
import os
import re
import sys
import multiprocessing
import subprocess
import time
import json
import signal
import psutil

n_constraints = 0
n_iter = 1
n_rf = 0


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

# nuhflファイルを読み込み、述語(="."で区切られた各行)をリストに格納


def format_nuhfl_by_pred(filename):
    try:
        with open(filename, 'r') as file:
            content = file.read()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    content = content.replace(".", " . ")
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


def get_rf_names(filename):
    rf_names = []
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    for line in lines:
        if line.startswith("RF"):
            rf_names.append(line.split()[0])
    return rf_names


def apply_new_ranking_function(filename, ranking_functions, rf_args, is_first=False):
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    # RFの引数の変数のリストを取得し、argsに格納
    # さらに、ranking_functionsにrf_argsの引数を適当に追加
    if is_first:
        for line in lines:
            if line.startswith("RF"):
                terms = line.split()
                rf_name = ""
                for term in terms:
                    if term.startswith("RF"):
                        rf_name = term
                        continue
                    if term == "r":
                        break
                    rf_args[rf_name].append(term)
        # for key, value in rf_args.items():
        #     ranking_functions[key] = str(value[0])

    print(f"ranking function for iter {n_iter} : {ranking_functions}")
    newlines = []
    for line in lines:
        if line.startswith("RF"):
            left = line.split("<>")[0]
            rf_name = line.split()[0]
            line = f"{left}<> {ranking_functions[rf_name]}.\n"
        newlines.append(line)
    with open(filename, 'w') as file:
        file.writelines(newlines)

def check_cpu_load(threshold=90, wait_time=1):
    while psutil.cpu_percent(interval=0.1) > threshold:
        print(f"High CPU load detected. Waiting for {wait_time} seconds...")
        time.sleep(wait_time)

def check_process_count(max_processes=5, wait_time=1):
    while len(multiprocessing.active_children()) > max_processes:
        print(f"Too many multiprocessing processes running ({len(multiprocessing.active_children())}). Waiting for {wait_time} seconds...")
        time.sleep(wait_time)

def run_rethfl(filename, queue):
    os.setsid()
    rethfl_cmd = f"rethfl {filename} --solver=z3"
    try:
        result = subprocess.run(
            rethfl_cmd, capture_output=True, text=True, check=True, shell=True)
        result = result.stdout.splitlines()[-3].strip()
        queue.put(('rethfl', result))
    except subprocess.CalledProcessError as e:
        print("Error running rethfl:")
        print(e.stdout)
        queue.put(('rethfl', 'error'))
    except KeyboardInterrupt:
        queue.put(('rethfl', 'interrupted'))


def run_show_trace(filename, queue):
    os.setsid()
    hopdr_path = "/home/yurikahirobe/hopdr/hopdr"    
    env = os.environ.copy()
    env['PATH'] = f"{hopdr_path}/bin:{env['PATH']}"
    show_trace_cmd = [f'{hopdr_path}/target/release/check',
                      '--trace', '--input', filename]
    try:
        result = subprocess.run(
            show_trace_cmd, capture_output=True, text=True, check=True, env=env)
        queue.put(('show_trace', result.stdout))
    except subprocess.CalledProcessError as e:
        print("Error running show_trace:")
        print(e.stderr)
        queue.put(('show_trace', 'error'))
    except KeyboardInterrupt:
        queue.put(('rethfl', 'interrupted'))


def solve_nuhfl(filename, start_time, nuhfl_inlining):
    queue = multiprocessing.Queue()
    result_queue = multiprocessing.Queue()
    python_dir = "/home/yurikahirobe/hopdr/hirobe"
    if nuhfl_inlining:
        try:
            nuhfl_inlined = subprocess.run(['python3', f'{python_dir}/rf_inlining.py', filename], check=True, capture_output=True, text=True)
            filename = nuhfl_inlined.stdout.strip()
        except subprocess.CalledProcessError as e:
            print(f"Error while nuhfl_inlining nuhfl with rf: {e}")
    process1 = multiprocessing.Process(
        target=run_rethfl, args=[filename, queue])
    process2 = multiprocessing.Process(
        target=run_show_trace, args=[filename, queue])

    process1.start()
    process2.start()
    try:
        while True:
            check_cpu_load()
            check_process_count()
            message = queue.get()
            if message[0] == "rethfl":
                if message[1] == "Invalid":
                    continue
                else:
                    if process1.is_alive():
                        os.killpg(process1.pid, signal.SIGKILL)
                    if process2.is_alive():
                        os.killpg(process2.pid, signal.SIGKILL)
                    if message[1] == "Valid":
                        print("ReTHFL result : Valid")
                        end_time = time.perf_counter_ns()
                        elapsed_time = (end_time - start_time) / 1_000_000_000
                        print(f"\ntotal: {elapsed_time:.6f} sec")
                        result_queue.put("Valid")
                        sys.exit(0)
                    elif message[1] == "interrupted":
                        sys.exit(1)
                    else:
                        print("terminated because of ReTHFL error")
                        sys.exit(1)
            elif message[0] == "show_trace":
                if process1.is_alive():
                    os.killpg(process1.pid, signal.SIGKILL)
                if process2.is_alive():
                    os.killpg(process2.pid, signal.SIGKILL)
                if message[1] == "error":
                    print("terminated because of show_trace error")
                    sys.exit(1)
                elif message[1] == "Fail":
                    print("terminated because show_trace failed")
                    sys.exit(1)
                elif message[1] == "interrupted":
                    sys.exit(1)
                else:
                    return message[1]
    except KeyboardInterrupt:
        print("Keyboard interrupted.")
        if process1.is_alive():
            os.killpg(process1.pid, signal.SIGKILL)
        if process2.is_alive():
            os.killpg(process2.pid, signal.SIGKILL)
        process1.join(timeout=1)
        process2.join(timeout=1)
        sys.exit(1)


# nuhfl_inlining = Trueの場合、filenameはinline前のnuhflファイル
def parse_result(type, filename, result, nuhfl_inlining=False):
    trace = result.split("Trace: ")[-1]
    if nuhfl_inlining:
        if type == "prover":
            trace_file = '/'.join(filename.split('/')[:-1]) + "/trace_prover.txt"
        if type == "disprover":
            trace_file = '/'.join(filename.split('/')[:-1]) + "/trace_disprover.txt"
        python_dir = "/home/yurikahirobe/hopdr/hirobe"
        with open(trace_file, 'w') as file:
            file.write(trace)
        try:
            result = subprocess.run(['python3', f'{python_dir}/counter_example_from_trace.py',
                                    filename, trace_file], capture_output=True, text=True)
            wf_info = json.loads(result.stdout.strip().split('\n')[-1])
            print(wf_info)
        except subprocess.CalledProcessError as e:
            print(f"Error while analyzing trace from inlined nuhfl: {e}")
        wf_name = wf_info["wf_name"]
        wf_values = wf_info["assigned_values"]
        # arith = wf_info["failed_arith"].split()
    else:
        terms = trace.replace("(", " ( ").replace(")", " ) ").split()
        wf_trace = []
        wf_values = []
        wf_name = ""
        is_wf = False
        is_wf_args = False
        paren = 0
        for term in terms:
            if term.startswith("WF"):
                is_wf = True
                is_wf_args = True
                wf_name = term
                continue
            if is_wf and is_wf_args:
                if term == "(":
                    paren += 1
                elif term == ")":
                    paren -= 1
                    if paren == 0:
                        is_wf_args = False
                        continue
                else:
                    wf_values.append(int(term))
                continue
            if is_wf and not is_wf_args:
                if term == "(":
                    paren += 1
                    wf_trace.append("(")
                elif term == ")":
                    paren -= 1
                    wf_trace.append(")")
                    if paren == 0:
                        is_wf = False
                        break
                else:
                    if re.fullmatch(r'^[0-9-]+$', term):
                        wf_trace.append("(")
                        wf_trace.append(term)
                        wf_trace.append(")")
                    else:
                        wf_trace.append(term)
        wf_trace_tree = build_tree(wf_trace)
        lines = format_nuhfl_by_pred(filename)
        # 目的のWFの式の、右辺のみを取得
        wf_line_str = [line for line in lines if line.startswith(wf_name)][0].split("=v")[
            1]
        wf_line_terms = wf_line_str.replace(
            "(", " ( ").replace(")", " ) ").split()
        # ピリオドを取り除く
        wf_line_terms = wf_line_terms[:-
                                      1] if wf_line_terms[-1] == "." else wf_line_terms
        # arith = scan_exp_with_tracetree(wf_line_terms, wf_trace_tree)

    # WFの呼び出し列から、不等式制約の係数を設定
    n_values = len(wf_values)
    wf_values = np.array(wf_values).reshape(2, int(n_values/2))
    # 定数項に対応する係数1を設定
    constant_coe = np.ones((wf_values.shape[0], 1), dtype=int)
    wf_values = np.concatenate((wf_values, constant_coe), axis=1)
    return wf_name, wf_values

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


def is_arithmetic(exp_terms):
    res = False
    for term in exp_terms:
        if term == "\\/" or term == "/\\" or term == "∀":
            return False
        if term == "<" or term == "<=" or term == ">" or term == ">=" or term == "=" or term == "==":
            res = True
    return res


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
    for pair in paren_idx_pair:
        if (pair[0] + pair[1]) == len(exp_terms)-1:
            n_outer_paren += 1
        else:
            break
    if n_outer_paren != 0:
        exp_terms = exp_terms[n_outer_paren: -n_outer_paren]
    return exp_terms


def scan_exp_with_tracetree(exp_terms, root):
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
        return scan_exp_with_tracetree(exp_terms, root.right)
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
        right_result = scan_exp_with_tracetree(right, root.right)
        left_result = scan_exp_with_tracetree(left, root.left)
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
            return scan_exp_with_tracetree(left, root.right)
        else:
            return scan_exp_with_tracetree(right, root.right)
    else:
        raise ValueError("trace tree is invalud format")


def rf_to_z3exp(rf1_variable, rf2_variable, rf1_assigned_values, rf2_assigned_values):
    rf_exp_list = []
    rf_exp_list.append(Sum([rf1_variable[j] * rf1_assigned_values[j] for j in range(len(rf1_variable))]))
    rf_exp_list.append(Sum([rf1_variable[j] * rf2_assigned_values[j] for j in range(len(rf1_variable))]))
    rf_exp_list.append(Sum([rf2_variable[j] * rf1_assigned_values[j] for j in range(len(rf2_variable))]))
    rf_exp_list.append(Sum([rf2_variable[j] * rf2_assigned_values[j] for j in range(len(rf2_variable))]))
    return rf_exp_list

def set_constraints(wf_name, wf_values, problem, variables_dict):
    global n_constraints
    rf1_name = "RF_" + wf_name[3:] + "_1"
    rf2_name = "RF_" + wf_name[3:] + "_2"
    rf1_variable = variables_dict[rf1_name]
    rf2_variable = variables_dict[rf2_name]
    rf1_assigned_values = wf_values[0]
    rf2_assigned_values = wf_values[1]
    rf_exp_list = rf_to_z3exp(rf1_variable, rf2_variable, rf1_assigned_values, rf2_assigned_values)
    constraint = Or( And(rf_exp_list[0] > rf_exp_list[1], rf_exp_list[0] >= 0), 
                    And(rf_exp_list[0] == rf_exp_list[1], rf_exp_list[2] > rf_exp_list[3], rf_exp_list[0] >= 0, rf_exp_list[2] >= 0))
    problem.add(constraint)
    print(constraint)
    n_constraints += 1


def update_ranking_function(problem, opt, rf_args, rf_variables, start_time):
    new_rfs = {key: "" for key in rf_args.keys()}
    opt.add(problem.assertions())
    # 不等式制約を解く
    if opt.check() == sat:
        model = opt.model()
        # for constraint in problem.assertions():
        #     print(constraint)
        for rf_name in rf_args.keys():
            variables = rf_variables[rf_name]
            new_rf = ""
            for i in range(len(variables)):
                new_coe = model[variables[i]]
                if (new_coe == None or new_coe.as_long() == 0):
                    continue
                if (i != len(variables)-1):
                    new_rf += f"({new_coe.as_long()}) * {rf_args[rf_name][i]} + "
                else:
                    new_rf += f"({new_coe.as_long()}) + "
            new_rf = "1" if new_rf == "" else new_rf[:-3]
            new_rfs[rf_name] = str(sp.sympify(new_rf))
    else:
        print("\nResult: No solution found.")
        end_time = time.perf_counter_ns()
        elapsed_time = (end_time - start_time) / 1_000_000_000
        print(f"total: {elapsed_time:.6f} sec")
        sys.exit(0)

    return new_rfs

def iteration_entry(type, filename, start_time, nuhfl_inlining=False):
    global n_rf
    rf_names = get_rf_names(filename)
    rf_list = {key: "1" for key in rf_names}
    problem = Solver()
    opt = Optimize()
    variables_dict = {key: [] for key in rf_names}
    rf_args = {key: [] for key in rf_names}
    while n_iter <= 500:
        rf_list = iteration(type, filename, rf_names, rf_list, rf_args,
                            problem, opt, variables_dict, start_time, nuhfl_inlining)

def iteration(type, filename, rf_names, rf_list, rf_args,
              problem, opt, variables_dict, start_time, nuhfl_inlining):
    global n_iter
    if (n_iter == 1):
        is_first = True
    else:
        is_first = False
    # 更新されたranking functionまたは初期値を設定
    apply_new_ranking_function(filename, rf_list, rf_args, is_first=is_first)

    # rethfl/show_traceを実行して結果のtrace(S式)を取得
    result = solve_nuhfl(filename, start_time, nuhfl_inlining)
    # print(result)

    # show_traceの結果をparseして、失敗している不等式制約を取得
    wf_name, wf_values = parse_result(type, filename, result, nuhfl_inlining)

    if is_first:
        variable_idx = 1
        for key in rf_args.keys():
            n_args = len(rf_args[key]) + 1
            variables = [Int(f'x{i}') for i in range(
                variable_idx, variable_idx + n_args)]
            variable_idx += n_args
            abs_variables = [Int(f'abs_x{i}') for i in range(1, n_args+1)]
            variables_dict[key] = variables
            for i in range(len(variables)):
                problem.add(abs_variables[i] >= variables[i])
                problem.add(abs_variables[i] >= -1 * variables[i])
        opt.minimize(sum(abs_variables))

    # 制約をset
    set_constraints(wf_name, wf_values, problem, variables_dict)

    # 不等式を解いてranking_functionを更新
    new_rfs = update_ranking_function(
        problem, opt, rf_args, variables_dict, start_time)
    print("")
    n_iter += 1
    return new_rfs

def create_negated_hflz(hflz_file):
    negated_hflz_file = hflz_file.replace(".in", "_negated.in")
    command = [
        "/home/sakayori/bin/hfl_preprocessor",
        "--negate",
        "--elim-exist",
    ]
    try:
        with open(hflz_file, 'r') as file:
            input_hflz = file.read()
        result = subprocess.run(command, input=input_hflz, capture_output=True, text=True, check=True)
        with open(negated_hflz_file, 'w') as file:
            file.write(result.stdout)
        return negated_hflz_file
    except subprocess.CalledProcessError as e:
        print(f"Error while creating negated hflz file: {e}")
        sys.exit(1)

def main(hflz_file, hflz_inlining=False, nuhfl_inlining=False):
    start_time = time.perf_counter_ns()
    python_dir = "/home/yurikahirobe/hopdr/hirobe"

    if hflz_inlining:
        hflz_file = subprocess.run(['python3', f'{python_dir}/hflz_inlining.py', hflz_file], capture_output=True, text=True, check=True).stdout.strip()
    
    negated_hflz_file = create_negated_hflz(hflz_file)

    subprocess.run(['python3', f'{python_dir}/optimize_raw_hflz.py', hflz_file], capture_output=True, text=True, check=True)
    subprocess.run(['python3', f'{python_dir}/optimize_raw_hflz.py', negated_hflz_file], capture_output=True, text=True, check=True)
    hflz_file = hflz_file[:-3] + "_opt.in"
    negated_hflz_file = negated_hflz_file[:-3] + "_opt.in"

    nuhfl_file = subprocess.run(['python3', f'{python_dir}/transform_hflz_with_rf.py', hflz_file], capture_output=True, text=True, check=True).stdout.strip()
    negated_nuhfl_file = subprocess.run(['python3', f'{python_dir}/transform_hflz_with_rf.py', negated_hflz_file], capture_output=True, text=True, check=True).stdout.strip()

    # disjunctionやconjunctionを正しく識別できるように括弧を追加。　場所はここでいいのか要検討
    subprocess.run(['python3', f'{python_dir}/add_paren.py', nuhfl_file], capture_output=True, text=True, check=True)
    subprocess.run(['python3', f'{python_dir}/add_paren.py', negated_nuhfl_file], capture_output=True, text=True, check=True)

    # process_prover = multiprocessing.Process(
    #     target=iteration_entry, args=["prover", nuhfl_file, start_time, nuhfl_inlining])
    process_disprover = multiprocessing.Process(
        target=iteration_entry, args=["disprover",negated_nuhfl_file, start_time, nuhfl_inlining])
    
    # process_prover.start()
    process_disprover.start()

    # process_prover.join()
    process_disprover.join()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Process counter-example guided verification.")
    parser.add_argument(
        'hflz_file', type=str, help="The name of the input hflz file with ranking function")
    parser.add_argument('--hflz-inlining', action='store_true',
                        help="Enable inlining of hflz to reduce predicate")
    parser.add_argument('--nuhfl-inlining', action='store_true',
                        help="Enable inlining of ranking function in nuhfl")
    args = parser.parse_args()
    main(hflz_file=args.hflz_file, hflz_inlining=args.hflz_inlining, nuhfl_inlining=args.nuhfl_inlining)