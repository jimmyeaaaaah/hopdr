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
    for i in range(len(new_lines)):
        line = new_lines[i]
        new_lines[i] = line.replace("=u", "=v").replace(".", " .")
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


def create_wf_rf(args, rf_idx):
    args_p = ["p"+s for s in args]
    args_str = " ".join(args)
    args_p_str = " ".join(args_p)
    wf = f"WF{rf_idx} {args_p_str} {args_str} =v ∀r1. ∀r2. RF{rf_idx} {args_p_str} r1 \/ RF{rf_idx} {args_str} r2 \/ (r1 >= 0 /\ r1 > r2)."
    rf = f"RF{rf_idx} {args_str} r =v r <> 1."
    return wf, rf

def create_d_line(args, rf_idx):
    args_p = ["p"+s for s in args]
    args_str = " ".join(args)
    args_p_str = " ".join(args_p)
    d_line = f"D isDummy {args_p_str} {args_str} =v isDummy = 1 " + " ".join([f"\/ WF{i} {args_p_str} {args_str}" for i in range(1, rf_idx)]) + "."
    return d_line

def add_ranking_function(lines, arg_map):
    print(arg_map)
    new_lines = []
    wf_list = []
    rf_list = []
    for line in lines:
        if line.startswith("%HES"):
            new_lines.append(line)
            continue
        new_line = []
        terms = line.split()
        paren = []
        pred = ""
        args_called = []
        is_left = True
        is_Sentry = False
        rf_idx = 1
        for term in terms:
            if term == "Sentry":
                is_Sentry = True
                continue
            if is_left:
                if term[0].isupper():
                    pred = term
                    continue
                if term == "=v":
                    is_left = False
                    if is_Sentry:
                        new_line.append("Sentry =v")
                    else:
                        new_line.append(pred)
                        new_args = ["isDummy"] + ["p"+arg for arg in arg_map[pred]] + arg_map[pred]
                        new_line += new_args
                        new_line = new_line + ["=v D isDummy"] + ["p"+arg for arg in arg_map[pred]] + arg_map[pred] + ["/\\ ("]
                        pred = ""
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
                        if is_Sentry:
                            new_line = new_line + [f"{pred} 1"] + args_called + args_called
                        else:
                            new_line = new_line + \
                                [f"( {pred} isDummy"] + ["p"+arg for arg in arg_map[pred]] + args_called + ["/\\"] + \
                                [f"{pred} 0"] + [arg for arg in arg_map[pred]] + args_called + [")"]
                            wf, rf = create_wf_rf(arg_map[pred], rf_idx)
                            wf_list.append(wf)
                            rf_list.append(rf)
                            rf_idx += 1
                        pred = ""
                        args_called = []
                else:
                    new_line.append(term)
        new_line = ' '.join(new_line)
        if is_Sentry == False:
            new_line = new_line[:-1] + ")."
        new_lines.append(new_line)
    args = arg_map[list(arg_map.keys())[0]] # そのうち直す、ほんとは共通の引数を取るべき
    d_line = create_d_line(args, rf_idx)
    new_lines.append(d_line)
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
    output_file = "/".join(filename.split("/")[:-1])+"/disjunctive_wf.in"
    with open(output_file, 'w') as file:
        file.write(content)


if __name__ == "__main__":
    main()
