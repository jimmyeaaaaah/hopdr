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
# ( ( isDummy = 1 \/ ( px + 1 >= 1 /\ px + 1 > x + 1) ) \/ ( 2*px + 3 >= 0 /\ 2*px + 3 > 2*x + 3 ) )
def wf_to_rf(wf_name, wf_args, rf_args, rf):
    rf_name1 = wf_name.replace("WF", "RF") + "_1"
    rf_name2 = wf_name.replace("WF", "RF") + "_2"
    wf_args = np.array(wf_args)
    wf_args = np.resize(wf_args, (2, len(wf_args) // 2))
    r1 = substitute(wf_args[0], rf_args[rf_name1], rf[rf_name1])
    r2 = substitute(wf_args[1], rf_args[rf_name1], rf[rf_name1])
    r3 = substitute(wf_args[0], rf_args[rf_name2], rf[rf_name2])
    r4 = substitute(wf_args[1], rf_args[rf_name2], rf[rf_name2])
    replaced_rf = f"( ( {r1} >= 0 /\ {r3} >= 0 ) /\ ( {r1} > {r2} \/ ( {r1} = {r2} /\ ( {r3} > {r4} ) ) ) )"
    return replaced_rf

def d_to_arith(rf_args, rfs):
    d_str = "( isDummy = 1 "
    for i in range(len(rf_args)):
        args = rf_args[i]
        p_args = [f"p{arg}" for arg in args]
        rf1_str = substitute(p_args, rf_args[i], rfs[i])
        rf2_str = substitute(args, rf_args[i], rfs[i])
        d_str += f"\/ ( {rf1_str} >= 0 /\ {rf1_str} >= {rf2_str} ) "
    d_str += " )"
    return d_str

def inlining(lines):
    rf_args = []
    rfs = []
    # 各RFの引数とrfの中身を取得
    rf_idx = -1
    for line in lines:
        if line.startswith("RF"):
            is_args = True
            is_rf = False
            terms = line.split()
            for term in terms:
                if term.startswith("RF"):
                    rf_idx += 1
                    rf_args.append([])
                    rfs.append("")
                    continue
                if term == "=v":
                    is_args = False
                    continue
                if term == "<>":
                    is_rf = True
                    continue
                if is_args:
                    if term != "r":
                        rf_args[rf_idx].append(term)
                if is_rf:
                    rfs[rf_idx] = rfs[rf_idx] + ' ' + term
            rfs[rf_idx] = rfs[rf_idx].rstrip(".")
    new_lines = []
    for line in lines:
        if line.startswith("%HES") or line.startswith("Sentry"):
            new_lines.append(line.strip())
            continue
        if line.startswith("D") or line.startswith("WF") or line.startswith("RF"):
            break
        new_line = []
        terms = line.replace("(", " ( ").replace(")", " ) ").strip().split()
        is_d = False
        for term in terms:
            if term == "D":
                is_d = True
                arith = d_to_arith(rf_args, rfs)
                new_line.append(arith)
            if is_d:
                if term == "/\\":
                    is_d = False
                    new_line.append(term)
                    continue
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
    output_file = "/".join(filename.split("/")[:-1]) + "/disjunctive_wf_inlined.in"
    with open(output_file, 'w') as file:
        file.write(content)
    sys.stdout.write(output_file + '\n')

if __name__ == "__main__":
    main()