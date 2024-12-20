import sys
import re
import numpy as np

def substitute(wf_args, rf_args, rf):
    rf = rf.replace("(", " ( ").replace(")", " ) ").replace("-", " - ").replace("+", " + ").replace("*", " * ")
    new_rf = []
    for term in rf.split():
        if term in rf_args:
            arg_idx = rf_args.index(term)
            new_rf.append(wf_args[arg_idx])
        else:
            new_rf.append(term)
    new_rf = " ".join(new_rf)
    return new_rf

# WF RF1 RF2 x ( x + 1 ), RF1 x r =v r <> x + 1, RF2 x r =v r <> 2*x + 3 を 
# ( ( x + 1 >= 0 /\ 2*x + 3 >= 0) /\ ( x + 1 > (x + 1) + 1 \/ ( x + 1 = (x + 1) + 1) /\ ( 2*x + 3 > 2*(x + 1) + 3 ) ) ) に置き換え
def wf_to_rf(wf_name, wf_args, rf_args, rf):
    rf_name1 = wf_name.replace("WF", "RF") + "_1"
    rf_name2 = wf_name.replace("WF", "RF") + "_2"
    wf_args = np.array(wf_args)
    wf_args = np.resize(wf_args, (2, len(wf_args) // 2))
    r1 = substitute(wf_args[0], rf_args[rf_name1], rf[rf_name1])
    r2 = substitute(wf_args[1], rf_args[rf_name1], rf[rf_name1])
    r3 = substitute(wf_args[0], rf_args[rf_name2], rf[rf_name2])
    r4 = substitute(wf_args[1], rf_args[rf_name2], rf[rf_name2])
    replaced_rf = f"( ( {r1} >= 0 ) /\ ( {r1} > {r2} \/ ( {r1} = {r2} /\ ( {r3} > {r4} /\ {r3} >= 0 ) ) ) )"
    return replaced_rf

def inlining(lines):
    rf_args = {}
    rfs = {}
    # 各RFの引数とrfの中身を取得
    for line in lines:
        if line.startswith("RF"):
            rf_name = 0
            is_args = True
            is_rf = False
            terms = line.split()
            for term in terms:
                if term.startswith("RF"):
                    rf_name = term
                    continue
                if term == "=v":
                    is_args = False
                    continue
                if term == "<>":
                    is_rf = True
                    continue
                if is_args:
                    if term != "r":
                        if rf_name not in rf_args.keys():
                            rf_args[rf_name] = []
                        rf_args[rf_name].append(term)
                if is_rf:
                    if rf_name not in rfs.keys():
                        rfs[rf_name] = ""
                    rfs[rf_name] = rfs[rf_name] + ' ' + term
            rfs[rf_name] = rfs[rf_name].rstrip(".")

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
                wf_name = term
                continue
            if is_wf:
                if term.startswith("RF"):
                    continue
                if re.fullmatch(r'^[0-9a-z\+\-\*\_]+$', term):
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
                            rf = wf_to_rf(wf_name, wf_args, rf_args, rfs)
                            wf_args = []
                            new_line.append(rf)
                            new_line.append(term)
                        else:
                            wf_paren -= 1
                            wf_args[-1] = wf_args[-1] + term
                    else:
                        is_wf = False
                        # ここでwf_idxとwf_argsからWFを展開する処理
                        rf = wf_to_rf(wf_name, wf_args, rf_args, rfs)
                        wf_args = []
                        new_line.append(rf)
                        new_line.append(term)
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
    output_file = filename.replace(".in", "_inlined.in")
    with open(output_file, 'w') as file:
        file.write(content)
    sys.stdout.write(output_file + '\n')

if __name__ == "__main__":
    main()