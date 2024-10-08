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
    print(f"ranking function for iter {n_iter} : {ranking_functions}")
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    newlines = []
    for line in lines:
        if line.startswith("RF"):
            left = line.split("<>")[0]
            rf_name = line.split()[0]
            line = f"{left}<> {ranking_functions[rf_name]}.\n"
        newlines.append(line)
    with open(filename, 'w') as file:
        file.writelines(newlines)

    # RFの引数の変数のリストを取得し、argsに格納
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


def run_rethfl(filename, queue):
    rethfl_cmd = f"rethfl {filename}"
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
    hopdr_path = os.path.expanduser("../hopdr")
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


def solve_nuhfl(filename, start_time, inlining):
    queue = multiprocessing.Queue()
    result_queue = multiprocessing.Queue()
    if inlining:
        try:
            result = subprocess.run(
                ['python3', 'rf_inlining.py', filename], check=True, capture_output=True, text=True)
            filename = result.stdout.strip()
        except subprocess.CalledProcessError as e:
            print(f"Error while inlining nuhfl with rf: {e}")

    process1 = multiprocessing.Process(
        target=run_rethfl, args=[filename, queue])
    process2 = multiprocessing.Process(
        target=run_show_trace, args=[filename, queue])

    process1.start()
    process2.start()

    try:
        while True:
            message = queue.get()
            if message[0] == "rethfl":
                if message[1] == "Invalid":
                    continue
                else:
                    process1.terminate()
                    process2.terminate()
                    process1.join()
                    process2.join()
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
                process1.terminate()
                process2.terminate()
                process1.join()
                process2.join()
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
        process1.terminate()
        process2.terminate()
        process1.join()
        process2.join()
        sys.exit(1)


# inlining = Trueの場合、filenameはinline前のnuhflファイル
# d_args = [2, 2, 1, 0]など(isDummyを除く)、failed_arith = ["r1 > r2", "r1 >= 0"]など
def parse_result(filename, result, inlining=False):
    trace = result.split("Trace: ")[-1].replace("(", " ( ").replace(")", " ) ").split()
    rf_name = 0
    if inlining:
        trace_file = '/'.join(filename.split('/')
                              [:-1]) + "/trace.txt"
        with open(trace_file, 'w') as file:
            file.write(trace)
        try:
            result = subprocess.run(['python3', 'counter_example_from_trace.py',
                                    filename, trace_file], capture_output=True, text=True)
            wf_info = json.loads(result.stdout.strip().split('\n')[-1])
            print(wf_info)
        except subprocess.CalledProcessError as e:
            print(f"Error while analyzing trace from inlined nuhfl: {e}")
        # finally:
        #     if os.path.exists(trace_file):
        #         os.remove(trace_file)
        wf_name = wf_info["wf_name"]
        wf_values = wf_info["assigned_values"]
        arith = wf_info["failed_arith"].split()
    else:
        d_trace = []
        failed_arith = []
        paren = 1
        is_d = False
        for term in trace:
            if term == "D":
                is_d = True
                d_trace.append(term)
                continue
            if is_d:
                if term == "(":
                    paren += 1
                elif term == ")":
                    paren -= 1
                if paren == 0:
                    break
                d_trace.append(term)
        for idx, term in enumerate(d_trace):
            if term == "conj":
                flag = d_trace[idx+1]
                if flag == "0":
                    failed_arith.append("r1 >= 0")
                elif flag == "1":
                    failed_arith.append("r1 > r2")
                else:
                    raise ValueError("invalid flag")
        d_trace_str = " ".join(d_trace)
        d_args = re.split(r'[()]', d_trace_str)[1].split()[1:]
        d_args = [int(val) for val in d_args]
        return d_args, failed_arith

def set_constraints(d_args, failed_arith, problem, variables_dict):
    global n_constraints
    d_args = np.array(d_args).reshape(2, -1)
    d_args = np.column_stack((d_args, np.ones(d_args.shape[0])))
    constraints = []
    for i in range(len(failed_arith)): 
        rf_name = f"RF{i+1}"
        rf_variable = variables_dict[rf_name]
        r1 = Sum([rf_variable[j] * d_args[0][j] for j in range(len(rf_variable))])
        r2 = Sum([rf_variable[j] * d_args[1][j] for j in range(len(rf_variable))])
        arith = failed_arith[i]
        if arith == "r1 > r2":
            constraint = r1 > r2
        elif arith == "r1 >= 0":
            constraint = r1 >= 0
        else:
            raise ValueError("invalid arithmetic")
        constraints.append(constraint)
    problem.add(Or(*constraints))
    n_constraints += 1
    print(constraint)


def update_ranking_function(problem, opt, rf_args, rf_variables, start_time):
    new_rfs = {key: "" for key in rf_args.keys()}
    opt.add(problem.assertions())
    # 不等式制約を解く
    if opt.check() == sat:
        model = opt.model()
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


def iteration(filename, rf_names, rf_list, rf_args,
              problem, opt, variables_dict, start_time, inlining):
    global n_iter
    if (n_iter == 1):
        is_first = True
    else:
        is_first = False
    # 更新されたranking functionまたは初期値を設定
    apply_new_ranking_function(filename, rf_list, rf_args, is_first=is_first)

    # rethfl/show_traceを実行して結果のtrace(S式)を取得
    result = solve_nuhfl(filename, start_time, inlining)
    print(result)

    # show_traceの結果をparseして、失敗している不等式制約を取得
    d_args, failed_arith = parse_result(filename, result, inlining)

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
    set_constraints(d_args, failed_arith, problem, variables_dict)

    # 不等式を解いてranking_functionを更新
    new_rfs = update_ranking_function(
        problem, opt, rf_args, variables_dict, start_time)
    print("")
    n_iter += 1
    return new_rfs


def main(filename, inlining=False):
    start_time = time.perf_counter_ns()
    global n_rf
    rf_names = get_rf_names(filename)
    rf_list = {key: "1" for key in rf_names}
    problem = Solver()
    opt = Optimize()
    variables_dict = {key: [] for key in rf_names}
    rf_args = {key: [] for key in rf_names}
    while n_iter <= 500:
        rf_list = iteration(filename, rf_names, rf_list, rf_args,
                            problem, opt, variables_dict, start_time, inlining)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Process counter-example guided verification.")
    parser.add_argument(
        'filename', type=str, help="The name of the input nuhfl file with ranking function")
    parser.add_argument('--inlining', action='store_true',
                        help="Enable inlining of ranking function")
    args = parser.parse_args()
    main(filename=args.filename, inlining=args.inlining)
