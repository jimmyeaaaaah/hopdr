import numpy as np
import sympy as sp
from z3 import *
import os
import re
import sys
import multiprocessing
import subprocess
import time

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
    rethfl_cmd = f"rethfl --remove-disjunction {filename}"
    try:
        result = subprocess.run(rethfl_cmd, capture_output=True, text=True, check=True, shell=True)
        result = result.stdout.splitlines()[-3].strip()
        queue.put(('rethfl', result))
    except subprocess.CalledProcessError as e:
        print("Error running rethfl:")
        print(e.stdout)
        queue.put(('rethfl', 'error'))
    except KeyboardInterrupt:
        queue.put(('rethfl', 'interrupted'))

def run_show_trace(filename, queue):
    env = os.environ.copy()
    env['PATH'] = f"{os.getcwd()}/bin:{env['PATH']}"
    show_trace_cmd = ['./target/release/check', '--trace', '--input', filename]
    try:
        result = subprocess.run(show_trace_cmd, capture_output=True, text=True, check=True, env=env)
        queue.put(('show_trace', result.stdout))
    except subprocess.CalledProcessError as e:
        print("Error running show_trace:")
        print(e.stderr)
        queue.put(('show_trace', 'error'))
    except KeyboardInterrupt:
        queue.put(('rethfl', 'interrupted'))

def solve_nuhfl(filename, start_time):
    queue = multiprocessing.Queue()
    result_queue = multiprocessing.Queue()

    process1 = multiprocessing.Process(target=run_rethfl, args=[filename, queue])
    process2 = multiprocessing.Process(target=run_show_trace, args=[filename, queue])

    process1.start()
    process2.start()

    try:
        while True:
            message = queue.get()
            if message[0] == "rethfl":
                if message[1] == "Valid":
                    process1.terminate()
                    process2.terminate()
                    print("ReTHFL result : Valid")
                    end_time = time.perf_counter_ns()
                    elapsed_time = (end_time - start_time)/ 1_000_000_000
                    print(f"\ntotal: {elapsed_time:.6f} sec")
                    result_queue.put("Valid")
                    sys.exit(0)
                elif message[1] == "interrupted":
                    process1.terminate()
                    process2.terminate()
                    sys.exit(1)
                elif message[1] != "Invalid":
                    process1.terminate()
                    process2.terminate()
                    print("terminated because of ReTHFL error")
                    sys.exit(1)
                
            elif message[0] == "show_trace":
                if message[1] == "error":
                    process1.terminate()
                    process2.terminate()
                    sys.exit(1)
                elif message[1] == 'Fail\n':
                    process1.terminate()
                    process2.terminate()
                    print("show_trace failed")
                    sys.exit(1)
                elif message[1] == "interrupted":
                    process1.terminate()
                    process2.terminate()
                    sys.exit(1)
                else:
                    process1.terminate()
                    process2.terminate()
                    return message[1]
    except KeyboardInterrupt:
        print("Keyboard interrupted.")
        process1.terminate()
        process2.terminate()
        sys.exit(1)

    process1.join()
    process2.join()

def parse_result(result):
    trace = result.split("Trace: ")[-1]
    last_wf = re.findall(r"WF[0-9]* \([0-9 -]+\)", trace)[-1]
    print(f"call sequence for WF : {last_wf}")
    args_of_wf = re.search(r"WF[0-9]* \(([0-9 -]+)\)", last_wf).group(1).split()
    rf_idx = last_wf.split()[0][2:]
    rf_idx = 0 if rf_idx == "" else int(rf_idx)-1

    # WFの呼び出し列から、不等式制約の係数を設定
    call_sequence = [int(s) for s in args_of_wf]
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
        problem.add(Sum([coe[j] * variables[j] for j in range(n_term)]) >= 1)
        n_constraints+=1
        problem.add(Sum([coe1[j] * variables[j] for j in range(n_term)]) >= 0)
        n_constraints+=1
    problem.add(Sum([coes[-1][j] * variables[j] for j in range(n_term)]) >= 0)
    n_constraints+=1

def update_ranking_function(problem, variables, args):
    new_rf = ""
    n_variable = len(variables)

    # print(problem)

    # 不等式制約を解く
    if problem.check() == sat:
        model = problem.model()
        for i in range(n_variable):
            new_coe = model[variables[i]]
            if(new_coe == None or new_coe.as_long() == 0):
                continue
            if(i != n_variable-1):
                new_rf += f"({new_coe.as_long()}) * {args[i]} + "
            else:
                new_rf += f"({new_coe.as_long()}) + "
        new_rf = "1" if new_rf == "" else new_rf[:-3]
        new_rf = str(sp.sympify(new_rf))
    else:
        print("\nResult: No solution found.")
        end_time = time.perf_counter_ns()
        elapsed_time = (end_time - start_time)/ 1_000_000_000
        print(f"total: {elapsed_time:.6f} sec")
        sys.exit(0)

    return new_rf

def iteration(filename, rf_list, n_rf, unseen_rf, problems, variables_list, args, start_time):
    global n_iter
    if(n_iter == 1):
        is_first = True
    else:
        is_first = False
    # ranking functionの初期値を設定
    apply_new_ranking_function(filename, rf_list, args, is_first=is_first)

    # rethfl/show_traceを実行して結果を取得
    result = solve_nuhfl(filename, start_time)

    # show_traceの結果をparseして、呼び出し列を2次元arrayに変換
    rf_idx, call_sequence = parse_result(result)

    if unseen_rf[rf_idx]:
        # LpProblemをranking functionの個数分用意
        n_variable = len(call_sequence[0])
        problem_name = f"RF{rf_idx}"
        problem = Solver()
        variables = [Int(f'x{i}') for i in range(1, n_variable+1)]

        problems[rf_idx] = problem
        variables_list[rf_idx] = variables
        unseen_rf[rf_idx] = False

    # 制約をset
    set_constraints(call_sequence, problems[rf_idx], variables_list[rf_idx])
   
    # 不等式を解いてranking_functionを更新
    new_rf = update_ranking_function(problems[rf_idx], variables_list[rf_idx], args[rf_idx])
    rf_list[rf_idx] = new_rf
    print("")
    n_iter+=1
    return rf_list

def main():
    global n_rf
    filename = sys.argv[1]
    start_time = time.perf_counter_ns()

    n_rf = get_n_rf(filename)
    rf_list = ["1"] * n_rf
    unseen_rf = [True] * n_rf
    problems = [False] * n_rf
    variables_list = [False] * n_rf
    args = [[] for _ in range(n_rf)]

    while n_iter <= 100:
        rf_list = iteration(filename, rf_list, n_rf, unseen_rf, problems, variables_list, args, start_time)
        
if __name__ == "__main__":
    main()