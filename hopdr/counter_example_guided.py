import numpy as np
import sympy as sp
import pulp
import os
import re
import sys
import subprocess
import time

n_constraints = 0
args = []
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

def apply_new_ranking_function(filename, ranking_functions, is_first=False):
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
        rf_line_terms = lines[-1].split()
        for term in rf_line_terms:
            if term.startswith("RF"):
                continue
            if term == "=v":
                break
            args.append(term)


def run_rethfl(filename):
    rethfl_cmd = f"rethfl --remove-disjunction {filename}"
    try:
        result = subprocess.run(rethfl_cmd, capture_output=True, text=True, check=True, shell=True)
        result = result.stdout.splitlines()[-3].strip()
        return result
    except subprocess.CalledProcessError as e:
        print("Error running rethfl:")
        print(e.stderr)
        sys.exit(1)

def run_show_trace(filename):
    env = os.environ.copy()
    env['PATH'] = f"{os.getcwd()}/bin:{env['PATH']}"
    show_trace_cmd = ['./target/release/check', '--trace', '--input', filename]
    try:
        result = subprocess.run(show_trace_cmd, capture_output=True, text=True, check=True, env=env)
        return result.stdout
    except subprocess.CalledProcessError as e:
        print("Error running show_trace:")
        print(e.stderr)
        sys.exit(1)

def solve_nuhfl(filename):
    rethfl_result = run_rethfl(filename)
    if rethfl_result == "Valid":
        print("ReTHFL result : Valid")
        end_time = time.perf_counter_ns()
        elapsed_time = (end_time - start_time)/ 1_000_000_000
        print(f"\ntotal: {elapsed_time:.6f} sec")
        sys.exit(0)
    elif rethfl_result == "Invalid":
        print("ReTHFL result : Invalid")
        print("run show_trace")
        return run_show_trace(filename)
    else:
        print("ReTHFL result : Unknown")
        sys.exit(1)

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
        problem += sum(coe[j] * variables[j] for j in range(n_term)) >= 1, f"Constraint_diff{n_constraints}"
        n_constraints+=1
        problem += sum(coe1[j] * variables[j] for j in range(n_term)) >= 0, f"Constraint_posi{n_constraints}"
        n_constraints+=1
    problem += sum(coes[-1][j] * variables[j] for j in range(n_term)) >= 0, f"Constraint_posi{n_constraints}"
    n_constraints+=1

def update_ranking_function(problem, variables):
    new_rf = ""
    n_variable = len(variables)

    # print(problem)

    # 不等式制約を解く
    solver = pulp.PULP_CBC_CMD(msg=False)   # ログを非表示
    problem.solve(solver)

    if pulp.LpStatus[problem.status] == 'Optimal':
        for i in range(n_variable):
            new_coe = variables[i].varValue
            if(new_coe == None or int(new_coe) == 0):
                continue
            if(i != n_variable-1):
                new_rf += f"({int(new_coe)}) * {args[i]} + "
            else:
                new_rf += f"({int(new_coe)}) + "
        new_rf = "1" if new_rf == "" else new_rf[:-3]
        new_rf = str(sp.sympify(new_rf))
    else:
        print("\nResult: No solution found.")
        sys.exit(0)
    return new_rf

def iteration(filename, rf_list, n_rf, unseen_rf, problems, variables_list):
    global n_iter
    if(n_iter == 1):
        is_first = True
    else:
        is_first = False
    # ranking functionの初期値を設定
    apply_new_ranking_function(filename, rf_list, is_first=is_first)

    # rethfl/show_traceを実行して結果を取得
    result = solve_nuhfl(filename)

    # show_traceの結果をparseして、呼び出し列を2次元arrayに変換
    rf_idx, call_sequence = parse_result(result)

    if unseen_rf[rf_idx]:
        # LpProblemをranking functionの個数分用意
        n_variable = len(call_sequence[0])
        problem_name = f"RF{rf_idx}"
        problem = pulp.LpProblem(problem_name, pulp.LpMaximize)
        variables = [pulp.LpVariable(f'x{i}', lowBound=None, cat='Integer') for i in range(1, n_variable+1)]
        problem += 0, "Objective_Function"      # 目的関数は無し

        problems[rf_idx] = problem
        variables_list[rf_idx] = variables
        unseen_rf[rf_idx] = False

    # 制約をset
    set_constraints(call_sequence, problems[rf_idx], variables_list[rf_idx])
   
    # 不等式を解いてranking_functionを更新
    new_rf = update_ranking_function(problems[rf_idx], variables_list[rf_idx])
    rf_list[rf_idx] = new_rf
    print("")
    n_iter+=1
    return rf_list

def main():
    global n_rf
    filename = sys.argv[1]

    n_rf = get_n_rf(filename)
    rf_list = ["1"] * n_rf
    unseen_rf = [True]*n_rf
    problems = [False]*n_rf
    variables_list = [False]*n_rf

    while n_iter <= 20:
        rf_list = iteration(filename, rf_list, n_rf, unseen_rf, problems, variables_list)
        
if __name__ == "__main__":
    start_time = time.perf_counter_ns()
    main()