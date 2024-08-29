import sys
import re
import numpy as np

def substitute(rf_idx, rf_args, wf_args, rf):
    for i in range(len(rf_args)):
        original_arg = rf_args[i]
        replaced_arg = wf_args[rf_idx][i]
        rf = rf.replace(original_arg, replaced_arg)
    return rf

def wf_to_rf(wf_args, rf_args, rf):
    wf_args = np.array(wf_args)
    wf_args = np.resize(wf_args, (2, len(wf_args) // 2))
    rf1 = substitute(0, rf_args, wf_args, rf)
    rf2 = substitute(1, rf_args, wf_args, rf)
    replaced_rf = "( " + rf1 + " >= 0 /\ " + rf1 + " > " + rf2 + " ) "
    return replaced_rf

def inlining(lines):
    n_rf = lines[-1].split()[0][2:] 
    n_rf = int(n_rf) if n_rf != "" else 1
    rf_args = [[]]*n_rf
    rfs = [""]*n_rf
    # 各RFの引数とrfの中身を取得
    for line in lines:
        if line.startswith("RF"):
            rf_index = 0
            is_args = True
            is_rf = False
            terms = line.split()
            for term in terms:
                if term.startswith("RF"):
                    rf_index = int(term[2:]) - 1 if term[2:] != "" else 0
                    continue
                if term == "=v":
                    is_args = False
                    continue
                if term == "<>":
                    is_rf = True
                    continue
                if is_args:
                    if term != "r":
                        rf_args[rf_index].append(term)
                if is_rf:
                    rfs[rf_index] = rfs[rf_index] + ' ' + term
            rfs[rf_index] = rfs[rf_index].rstrip(".")
    new_lines = []
    for line in lines:
        new_line = []
        if line.startswith("WF"):
            break
        line = line.replace("(", " ( ").replace(")", " ) ")
        terms = line.split()
        is_wf = False
        wf_paren = 0
        wf_args = []
        for term in terms:
            if term.startswith("WF"):
                is_wf = True
                wf_paren = 0
                wf_index = int(term[2:]) - 1 if term[2:] != "" else 0
                continue
            if is_wf:
                if term.startswith("RF"):
                    continue
                if re.fullmatch(r'^[0-9a-z+-]+$', term):
                    if wf_paren == 0:
                        wf_args.append(term)
                    else:
                        wf_args[-1] = wf_args[-1] + term
                else:
                    if term == "(":
                        if wf_paren == 0:
                            wf_args.append(term)
                        else:
                            wf_args[-1] = wf_args[-1] + term
                        wf_paren += 1
                    elif term == ")":
                        if wf_paren == 0:   # WFから抜けている
                            is_wf = False
                            # ここでwf_idxとwf_argsからWFを展開する処理
                            rf = wf_to_rf(wf_args, rf_args[wf_index], rfs[wf_index])
                            wf_args = []
                            new_line.append(rf)
                            new_line.append(term)
                        else:
                            wf_paren -= 1
                            wf_args[-1] = wf_args[-1] + term
                    else:
                        is_wf = False
                        # ここでwf_idxとwf_argsからWFを展開する処理
                        rf = rf = wf_to_rf(wf_args, rf_args[wf_index], rfs[wf_index])
                        wf_args = []
                        new_line.append(rf)
            else:
                new_line.append(term)
        new_line = " ".join(new_line).replace("  ", " ")
        new_lines.append(new_line)
    return new_lines


def main():
    filename = sys.argv[1]
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    lines = inlining(lines)
    content = "\n".join(lines)
    output_file = "/".join(filename.split("/")[:-1]) + "/rf_inlined.in"
    with open(output_file, 'w') as file:
        file.write(content)
    sys.stdout.write(output_file + '\n')

if __name__ == "__main__":
    main()