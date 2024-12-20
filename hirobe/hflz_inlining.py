import sys

def reform(lines):
    contents = ' '.join(line.strip() for line in lines)
    quantifier_stack = []
    new_lines = []
    new_line = ""
    for c in contents:
        new_line += c
        if c == '∀' or c == '∃':
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

def substitute(arg_map, pred_expr_map, pred_parent, pred_delete):
    parent_exp = pred_expr_map[pred_parent]
    delete_exp = pred_expr_map[pred_delete]
    n_delete_exp_arg = len(delete_exp.split("=v")[0].split()) - 1
    delete_exp = delete_exp.split("=v")[1].rstrip(".")
    new_exp = []
    terms = parent_exp.split()
    is_target = False
    is_first_call = True
    target_args = []
    for term in terms:
        if term == pred_delete:
            is_target = True
            new_exp.append("(")
            continue
        if is_target == False:
            new_exp.append(term)
        else:
            target_args.append(term)
            if len(target_args) == n_delete_exp_arg:
                is_target = False
                if is_first_call:
                    for i, arg in enumerate(target_args):
                        delete_exp = delete_exp.replace(arg_map[pred_delete][i], arg)
                    del arg_map[pred_delete]
                new_exp.append(delete_exp)
                new_exp.append(")")
    new_exp = ' '.join(new_exp)
    pred_expr_map[pred_parent] = new_exp
    del pred_expr_map[pred_delete]
    return pred_expr_map

def inlining(lines, arg_map):
    pred_expr_map = {}
    pred_parent_map = {}

    for line in lines:
        terms = line.split()
        pred_parent = terms[0]
        pred_expr_map[pred_parent] = line
        if pred_parent == "%HES" or pred_parent == "Sentry":
            continue
        for term in terms[1:]:
            if term[0].isupper():
                if term not in pred_parent_map.keys():
                    pred_parent_map[term] = []
                if pred_parent not in pred_parent_map[term]:
                    pred_parent_map[term].append(pred_parent)
    for pred_delete in pred_parent_map.keys():
        if len(pred_parent_map[pred_delete]) != 1:
            continue
        pred_expr_map = substitute(arg_map, pred_expr_map, pred_parent_map[pred_delete][0], pred_delete)
    new_lines = []
    for pred in pred_expr_map.keys():
        new_lines.append(pred_expr_map[pred])
    return new_lines

def main():
    filename = sys.argv[1]
    try:
        with open(filename) as f:
            lines = f.readlines()
    except FileNotFoundError:
        print(f"File not found: {filename}")
        sys.exit(1)
    lines = reform(lines)
    arg_map = get_arg_map(lines)
    if len(arg_map) > 1:
        lines = inlining(lines, arg_map)
    content = "\n".join(lines)
    output_file_inlined = filename.replace(".in", "_inlined.in")
    with open(output_file_inlined, 'w') as file:
        file.write(content)
    print(output_file_inlined)

if __name__ == "__main__":
    main()