import sys


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
    for idx_rf in range(len(new_lines)):
        line = new_lines[idx_rf]
        new_lines[idx_rf] = line.replace("=u", "=v")
    return new_lines


def get_arg_map(lines):
    arg_map = {}
    for line in lines:
        if line.startswith("%HES") or line.startswith("Sentry"):
            continue
        terms = line.split()
        pred = terms[0]
        arg_map[pred] = []
        for term in terms:
            if term == "=v":
                break
            else:
                if term != pred:
                    arg_map[pred].append(term)
    return arg_map


def create_wf_rf(pred, args):
    args1 = [s+"1" for s in args]
    args2 = [s+"2" for s in args]
    args_str = " ".join(args)
    args1_str = " ".join(args1)
    args2_str = " ".join(args2)
    wf = f"WF_{pred} " + " ".join([f"rf{idx}" for idx in range(1, len(args)+1)]) + f" {args1_str} {args2_str}"
    forall_r = "".join([f"∀ r{idx}. " for idx in range(1, len(args)*2+1)])
    r_disjunction = "".join([f"rf{rf_idx} {args1_str} r{rf_idx*2-1} \/ rf{rf_idx} {args2_str} r{rf_idx*2} \/ " for rf_idx in range(1, len(args)+1)])
    r_positive = "".join([f"r{idx*2-1} >= 0 /\ " for idx in range(1, len(args)+1)])
    lexicographic = ["( r1 > r2 "] + [f"\/ ( r{idx*2-1} = r{idx*2} /\ ( r{idx*2+1} > r{idx*2+2} " for idx in range(1, len(args))] + [") " for idx in range(1, len(args)*2)]
    lexicographic = "".join(lexicographic)
    wf_line = wf + " =v " + forall_r + r_disjunction + "( " + r_positive + lexicographic + ")."
    rf_line = f"{args_str} r =v r <> 1."
    rf_lines = [f"RF_{pred}_{idx} " + rf_line for idx in range(1, len(args)+1)]
    return wf_line, rf_lines


def add_ranking_function(lines, arg_map):
    print(arg_map)
    new_lines = []
    wf_list = []
    rf_list = []
    has_wf = []
    for line in lines:
        if line.startswith("%HES") or line.startswith("Sentry"):
            new_lines.append(line)
            continue
        new_line = []
        terms = line.split()
        args_called = []
        paren = []
        pred = ""
        is_left = True
        for term in terms:
            new_line.append(term)
            if is_left:
                if term == "=v":
                    is_left = False
                    continue
            else:
                if term[0].isupper():
                    pred = term
                    continue
                if pred != "":
                    if term == "(":
                        paren.append("(")
                    elif term == ")":
                        paren.append(")")
                        args_called.append(" ".join(paren))
                        paren = []
                    else:
                        if len(paren) == 0:
                            args_called.append(term)
                        else:
                            paren.append(term)
                    if (len(arg_map[pred]) == len(args_called)):
                        new_line = new_line + \
                            [f"/\ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, len(arg_map[pred])+1)] + \
                            arg_map[pred] + args_called
                        if pred not in has_wf:
                            wf, rfs = create_wf_rf(pred, arg_map[pred])
                            wf_list.append(wf)
                            rf_list = rf_list + rfs
                            has_wf.append(pred)
                        pred = ""
                        args_called = []
        new_line = ' '.join(new_line)
        new_lines.append(new_line)
    new_lines += wf_list
    new_lines += rf_list
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
    arg_map = get_arg_map(lines)
    lines = add_ranking_function(lines, arg_map)
    content = "\n".join(lines)
    output_file = "/".join(filename.split("/")[:-1])+"/rf_lexico.in"
    with open(output_file, 'w') as file:
        file.write(content)


if __name__ == "__main__":
    main()
