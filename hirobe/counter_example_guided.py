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


def get_n_rf(filename):
    n_rf = 0
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    for line in lines:
        if line.startswith("RF"):
            n_rf += 1
    return n_rf


def apply_new_ranking_function(filename, ranking_functions, args, is_first=False):
    print(f"ranking function for iter {n_iter} : {ranking_functions}")
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    n_rf = 0
    newlines = []
    for line in lines:
        if line.startswith("RF"):
            left = line.split("<>")[0]
            line = f"{left}<> {ranking_functions[n_rf]}.\n"
            n_rf += 1
        newlines.append(line)
    with open(filename, 'w') as file:
        file.writelines(newlines)

    # RFの引数の変数のリストを取得する
    if is_first:
        rf_idx = 0
        for line in lines:
            if line.startswith("RF"):
                terms = line.split()
                for term in terms:
                    if term.startswith("RF"):
                        rf_idx = 0 if term[2:] == "" else int(term[2:])-1
                        continue
                    if term == "r":
                        break
                    args[rf_idx].append(term)


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


def parse_result(result, inlining=False, original_nuhfl_file=""):
    trace = result.split("Trace: ")[-1]
    rf_idx = 0
    if inlining:
        trace_file = '/'.join(original_nuhfl_file.split('/')
                              [:-1]) + "/trace.txt"
        with open(trace_file, 'w') as file:
            file.write(trace)
        try:
            result = subprocess.run(['python3', 'counter_example_from_trace.py',
                                    original_nuhfl_file, trace_file], capture_output=True, text=True)
            wf_info = json.loads(result.stdout.strip().split('\n')[-1])
            print(wf_info)
        except subprocess.CalledProcessError as e:
            print(f"Error while analyzing trace from inlined nuhfl: {e}")
        # finally:
        #     if os.path.exists(trace_file):
        #         os.remove(trace_file)
        wf_name = wf_info["wf_name"]
        wf_args = wf_info["assigned_values"]
        rf_idx = wf_name[2:]
        rf_idx = 0 if rf_idx == "" else int(rf_idx) - 1

    else:
        last_wf = re.findall(r"WF[0-9]* \([0-9 -]+\)", trace)[-1]
        print(f"call sequence for WF : {last_wf}")
        wf_args = re.search(r"WF[0-9]* \(([0-9 -]+)\)",
                            last_wf).group(1).split()
        rf_idx = last_wf.split()[0][2:]
        rf_idx = 0 if rf_idx == "" else int(rf_idx) - 1

    # WFの呼び出し列から、不等式制約の係数を設定
    call_sequence = [int(s) for s in wf_args]
    n_args = len(call_sequence)
    call_sequence = np.array(call_sequence).reshape(2, int(n_args/2))
    # 定数項に対応する係数1を設定
    constant_term_coe = np.ones((call_sequence.shape[0], 1), dtype=int)
    call_sequence = np.concatenate((call_sequence, constant_term_coe), axis=1)
    return rf_idx, call_sequence


def set_constraints(coes, problem, variables):
    global n_constraints
    n_term = len(coes[0])
    for i in range(len(coes) - 1):
        coe1 = coes[i]
        coe2 = coes[i+1]
        coe = coe1 - coe2
        problem.add(Sum([coe[j] * variables[j] for j in range(n_term)]) > 0)
        n_constraints += 1
        problem.add(Sum([coe1[j] * variables[j] for j in range(n_term)]) >= 0)
        n_constraints += 1
    # problem.add(Sum([coes[-1][j] * variables[j] for j in range(n_term)]) >= 0)
    n_constraints += 1


def update_ranking_function(problem, opt, variables, args, start_time):
    new_rf = ""
    n_variable = len(variables)
    opt.add(problem.assertions())

    # 不等式制約を解く
    if opt.check() == sat:
        model = opt.model()
        for i in range(n_variable):
            new_coe = model[variables[i]]
            if (new_coe == None or new_coe.as_long() == 0):
                continue
            if (i != n_variable-1):
                new_rf += f"({new_coe.as_long()}) * {args[i]} + "
            else:
                new_rf += f"({new_coe.as_long()}) + "
        new_rf = "1" if new_rf == "" else new_rf[:-3]
        new_rf = str(sp.sympify(new_rf))
    else:
        print("\nResult: No solution found.")
        end_time = time.perf_counter_ns()
        elapsed_time = (end_time - start_time) / 1_000_000_000
        print(f"total: {elapsed_time:.6f} sec")
        sys.exit(0)

    return new_rf


def iteration(filename, rf_list, n_rf, unseen_rf, problems, opts, variables_list, args, start_time, inlining):
    global n_iter
    if (n_iter == 1):
        is_first = True
    else:
        is_first = False
    # 更新されたranking functionまたは初期値を設定
    apply_new_ranking_function(filename, rf_list, args, is_first=is_first)

    # rethfl/show_traceを実行して結果を取得
    result = solve_nuhfl(filename, start_time, inlining)

    # show_traceの結果をparseして、呼び出し列を2次元arrayに変換
    rf_idx, call_sequence = parse_result(result, inlining, filename)

    if unseen_rf[rf_idx]:
        # LpProblemをranking functionの個数分用意
        n_variable = len(call_sequence[0])
        problem = Solver()
        variables = [Int(f'x{i}') for i in range(1, n_variable+1)]
        abs_variables = [Int(f'abs_x{i}') for i in range(1, n_variable+1)]
        for i in range(len(variables)):
            problem.add(abs_variables[i] >= variables[i])
            problem.add(abs_variables[i] >= -1 * variables[i])
        opt = Optimize()
        opt.minimize(sum(abs_variables))    # L1ノルムを最小化
        problems[rf_idx] = problem
        opts[rf_idx] = opt
        variables_list[rf_idx] = variables
        unseen_rf[rf_idx] = False

    # 制約をset
    set_constraints(call_sequence, problems[rf_idx], variables_list[rf_idx])

    # 不等式を解いてranking_functionを更新
    new_rf = update_ranking_function(
        problems[rf_idx], opts[rf_idx], variables_list[rf_idx], args[rf_idx], start_time)
    rf_list[rf_idx] = new_rf
    print("")
    n_iter += 1
    return rf_list


def main(filename, inlining=False):
    start_time = time.perf_counter_ns()

    global n_rf
    n_rf = get_n_rf(filename)
    rf_list = ["1"] * n_rf
    unseen_rf = [True] * n_rf
    problems = [False] * n_rf
    opts = [False] * n_rf
    variables_list = [False] * n_rf
    args = [[] for _ in range(n_rf)]

    while n_iter <= 500:
        rf_list = iteration(filename, rf_list, n_rf, unseen_rf,
                            problems, opts, variables_list, args, start_time, inlining)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Process counter-example guided verification.")
    parser.add_argument(
        'filename', type=str, help="The name of the input nuhfl file with ranking function")
    parser.add_argument('--inlining', action='store_true',
                        help="Enable inlining of ranking function")
    args = parser.parse_args()
    main(filename=args.filename, inlining=args.inlining)
