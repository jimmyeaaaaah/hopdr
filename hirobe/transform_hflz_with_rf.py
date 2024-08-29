import sys

def reform(lines):
    contents = ' '.join(line.strip() for line in lines)
    quantifier_stack=[]
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

def create_wf_rf(n_counter, idx_rf, args):
    args2 = [ s+"2" for s in args]
    args_str = " ".join(args)
    args2_str = " ".join(args2)
    wf_line = ""
    rf_line = ""
    if n_counter == 1:
        wf_line = "WF "+args_str+" "+args2_str+"  =v ∀ r. ∀ r2. RF "+args_str+" r \/ RF "+args2_str+" r2 \/ r >= 0 /\ r > r2."
        rf_line = "RF "+args_str+" r =v r <> 1."
    else:
        wf_line = f"WF{idx_rf} rf "+args_str+" "+args2_str+"  =v ∀ r. ∀ r2. rf "+args_str+" r \/ rf "+args2_str+" r2 \/ r >= 0 /\ r > r2."
        rf_line = f"RF{idx_rf} "+args_str+" r =v r <> 1."
    return wf_line, rf_line

def add_ranking_function(lines, n_counter, arg_map):
    new_lines = []
    wf_list = []
    rf_list = []
    idx_rf = 1
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
                    if(len(arg_map[pred]) == len(args_called)):
                        if n_counter == 1:
                            new_line = new_line + ["/\ WF"] + arg_map[pred] + args_called
                            wf, rf = create_wf_rf(n_counter, idx_rf, arg_map[pred])
                            if len(wf_list) == 0:
                                wf_list.append(wf)
                                rf_list.append(rf)
                        else:
                            new_line = new_line + [f"/\ WF{idx_rf} RF{idx_rf}"] + arg_map[pred] + args_called
                            wf, rf = create_wf_rf(n_counter, idx_rf, arg_map[pred])
                            wf_list.append(wf)
                            rf_list.append(rf)
                            idx_rf += 1
                        pred = ""
                        args_called = []
        new_line = ' '.join(new_line)
        new_lines.append(new_line)
    new_lines += wf_list
    new_lines += rf_list
    return new_lines

def main():
    filename = sys.argv[1]
    n_counter = int(sys.argv[2])
    try:
        with open(filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    lines = reform(lines)
    arg_map = get_arg_map(lines)
    lines = add_ranking_function(lines, n_counter, arg_map)
    content = "\n".join(lines)
    output_file = "/".join(filename.split("/")[:-1])+"/rf.in"
    with open(output_file, 'w') as file:
        file.write(content)
        
if __name__ == "__main__":
    main()