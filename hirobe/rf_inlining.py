import sys
import re
import numpy as np

def reform(lines):
    contents = ' '.join(line.strip() for line in lines)
    quantifier_stack = []
    new_lines = []
    new_line = ""
    for c in contents:
        new_line += c
        if c == '∀':
            quantifier_stack.append(c)
        if c == '.':
            if len(quantifier_stack) == 0:
                if new_line.startswith("%HES"):
                    new_lines.append("%HES")
                    new_lines.append(' '.join(new_line.split()[1:]))
                else:
                    new_lines.append(new_line)
                new_line = ""
            else:
                quantifier_stack.pop()
    for i in range(len(new_lines)):
        line = new_lines[i]
        new_lines[i] = line.replace("=u", "=v").replace(".", " .").strip()
    return new_lines

def substitute(substituted_args, rf_args, rf):
    rf = rf.replace("(", " ( ").replace(")", " ) ").replace("-", " - ").replace("+", " + ").replace("*", " * ")
    new_rf = []
    for term in rf.split():
        if term in rf_args:
            arg_idx = rf_args.index(term)
            new_rf.append(substituted_args[arg_idx])
        else:
            new_rf.append(term)
    new_rf = " ".join(new_rf)
    return new_rf


def d_to_arith(pred, rf_args, rfs):
    d_str = f"( isDummy_{pred.lower()} = 1 "
    for i in range(len(rfs)):
        rf = rfs[i]
        p_args = [f"p{arg}" for arg in rf_args]
        rf1_str = substitute(p_args, rf_args, rf)
        rf2_str = substitute(rf_args, rf_args, rf)
        d_str += f"\/ ( {rf1_str} >= 0 /\ {rf1_str} > {rf2_str} ) "
    d_str += " )"
    return d_str

def inlining(lines):
    rf_args = {}
    rfs = {}
    # 各RFの引数とrfの中身を取得
    for line in lines:
        if line.startswith("RF"):
            is_args = True
            is_rf = False
            terms = line.split()
            for term in terms:
                if term.startswith("RF"):
                    pred = ("_").join(term.split("_")[1:-1])
                    rf_args[pred] = []
                    if pred not in rfs.keys():
                        rfs[pred] = []
                    rfs[pred].append("")
                    continue
                if term == "=v":
                    is_args = False
                    continue
                if term == "<>":
                    is_rf = True
                    continue
                if is_args:
                    if term != "r":
                        rf_args[pred].append(term)
                if is_rf:
                    rfs[pred][-1] = rfs[pred][-1] + ' ' + term
            rfs[pred][-1] = rfs[pred][-1].rstrip(".")
    new_lines = []
    for line in lines:
        if line.startswith("%HES") or line.startswith("Sentry"):
            new_lines.append(line.strip())
            continue
        if line.startswith("D") or line.startswith("WF") or line.startswith("RF"):
            break
        new_line = []
        terms = line.replace("(", " ( ").replace(")", " ) ").strip().split()
        pred = terms[0]
        is_d = False
        for term in terms:
            if term.startswith("D"):
                is_d = True
                arith = d_to_arith(pred, rf_args[pred], rfs[pred])
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
    lines = reform(lines)
    lines = inlining(lines)
    content = "\n".join(lines)
    output_file = "/".join(filename.split("/")[:-1]) + "/disjunctive_wf_inlined.in"
    with open(output_file, 'w') as file:
        file.write(content)
    sys.stdout.write(output_file + '\n')

if __name__ == "__main__":
    main()