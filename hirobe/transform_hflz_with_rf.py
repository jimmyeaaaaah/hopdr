import sys
import argparse

max_int = sys.maxsize

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


def create_wf_rf(pred, args, n_rf = 2):
    args1 = [s+"1" for s in args]
    args2 = [s+"2" for s in args]
    args_str = " ".join(args)
    args1_str = " ".join(args1)
    args2_str = " ".join(args2)
    if n_rf == 2:
        wf = f"WF_{pred} " + " ".join([f"rf{idx}" for idx in range(1, 3)]) + f" {args1_str} {args2_str}"
        wf_line = f"{wf} =v ∀ r1. ∀ r2. ∀ r3. ∀ r4. ( rf1 {args1_str} r1 \/ ( rf1 {args2_str} r2 \/ ( rf2 {args1_str} r3 \/ ( rf2 {args2_str} r4 \/ ( ( r1 >= 0  ) /\ ( r1 > r2 \/ ( r1 = r2 /\ ( r3 > r4 /\ r3 >= 0 ) ) ) ) ) ) ) )."
        rf_line = f"{args_str} r =v r <> 1."
        rf_lines = [f"RF_{pred}_{idx} " + rf_line for idx in range(1, 3)]
    else:
        wf = f"WF_{pred} " + " ".join([f"rf{idx}" for idx in range(1, len(args)+1)]) + f" {args1_str} {args2_str}"
        forall_r = "".join([f"∀ r{idx}. " for idx in range(1, len(args)*2+1)])
        r_disjunction = "".join([f"( rf{rf_idx} {args1_str} r{rf_idx*2-1} \/ ( rf{rf_idx} {args2_str} r{rf_idx*2} \/ " for rf_idx in range(1, len(args)+1)])
        r_positive = " /\ ".join([f"r{idx*2-1} >= 0" for idx in range(1, len(args)+1)])
        lexicographic = ["( r1 > r2 "] + [f"\/ ( r{idx*2-1} = r{idx*2} /\ ( r{idx*2+1} > r{idx*2+2} " for idx in range(1, len(args))] + [") " for idx in range(1, len(args)*2)]
        lexicographic = "".join(lexicographic)
        wf_line = wf + " =v " + forall_r + r_disjunction + "( ( " + r_positive + " ) /\\ " + lexicographic + ") "*len(args)*2 + ")."
        rf_line = f"{args_str} r =v r <> 1."
        rf_lines = [f"RF_{pred}_{idx} " + rf_line for idx in range(1, len(args)+1)]
    return wf_line, rf_lines


def add_ranking_function(lines, arg_map):
    p_arg_map = {}
    for key, value in arg_map.items():
        p_arg_map[key] = [f"p{arg}_{key.lower()}" for arg in value]
    entry_pred = []
    new_lines = []
    wf_list = []
    rf_list = []
    has_wf = []
    for line in lines:
        line = line.replace(".", " .")
        if line.startswith("%HES"):
            new_lines.append(line)
            continue
        if line.startswith("Sentry"):
            terms = line.split()
            args_called = []
            pred = ""
            paren = []
            new_line = []
            for term in terms:
                if term[0].isupper() and term != "Sentry":
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
                        args = []
                        for key in arg_map.keys():
                            if pred == key:
                                args = args + args_called
                            else:
                                for value in arg_map[key]:
                                    args.append("0")  # 初期値を0に設定
                        new_line = new_line + [pred] + args + args_called
                        entry_pred.append(pred)
                        pred = ""
                        args_called = []
                else:
                    new_line.append(term)
            terms = ' '.join(new_line).split()
            new_line = []
            for term in terms:
                new_line.append(term)
                if term[0].isupper() and term != "Sentry":
                    is_first_initial_value = ["1" for i in range(len(arg_map) - len(entry_pred))]
                    new_line = new_line + is_first_initial_value
                    continue
            new_lines.append(' '.join(new_line))
            continue
        # Sentry以外の述語
        new_line = []
        terms = line.split()
        pred_parent_map = ""
        pred = ""
        args_called = []
        paren = []
        is_left = True
        # 各述語の1つ前の値を格納する変数
        p_args = [p_arg for sublist in p_arg_map.values() for p_arg in sublist]
        # isFirstのフラグを格納する変数
        is_first_args = [f"is_first_{pred_name.lower()}" for pred_name in arg_map.keys() if pred_name not in entry_pred]
        for term in terms:
            if is_left:
                if term == "=v":
                    # if pred_parent_map in entry_pred:
                    #     new_line = new_line + [pred_parent_map] + ["isFirst"] + p_args + args_called + ["=v"]
                    # else:
                    new_line = new_line + [pred_parent_map] + is_first_args + p_args + args_called + ["=v"]
                    is_left = False
                    args_called = []
                    continue
                if term[0].isupper():
                    pred_parent_map = term
                else:
                    args_called.append(term)
            else:
                if term[0].isupper():
                    pred = term
                    continue
                if pred != "":
                    # 述語が引数をとらない場合
                    if (len(arg_map[pred]) == 0):
                        new_line = new_line + [pred] + is_first_args + p_args + [term]
                        pred = ""
                        continue
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
                    # 述語の呼び出しに対して、WFを追加
                    if (len(arg_map[pred]) == len(args_called)):
                        p_args_substituted = []
                        for key in p_arg_map.keys():
                            if key == pred:
                                p_args_substituted = p_args_substituted + args_called
                            elif key == pred_parent_map:
                                p_args_substituted = p_args_substituted + arg_map[pred_parent_map]
                            else:
                                p_args_substituted = p_args_substituted + p_arg_map[key]
                        # if pred in entry_pred:
                        #     new_line = new_line + [f"( {pred} 0"] + p_args_substituted + args_called + \
                        #         [f"/\ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, 3)] + \
                        #         p_arg_map[pred] + args_called + [")"]
                        # else:
                        #     if pred_parent_map in entry_pred:
                        #         new_line = new_line + [f"( {pred}"] + p_args_substituted + args_called + \
                        #             [f"/\ ( isFirst = 1 \/ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, 3)] + \
                        #             p_arg_map[pred] + args_called + [") )"]
                        #     else:
                        if pred in entry_pred:
                            # isFirstの比較は行わない
                            new_line = new_line + [f"( {pred}"] + is_first_args + p_args_substituted + args_called + \
                                [f"/\ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, 3)] + \
                                p_arg_map[pred] + args_called + [")"]
                        else:
                            # 今呼び出している述語のisFirstは0にする
                            is_first_args_substituted = ["0" if f"is_first_{pred.lower()}" == is_first_arg else is_first_arg for is_first_arg in is_first_args]
                            new_line = new_line + [f"( {pred}"] + is_first_args_substituted + p_args_substituted + args_called + \
                                [f"/\ ( is_first_{pred.lower()} = 1 \/ WF_{pred}"] + [f"RF_{pred}_{idx}" for idx in range(1, 3)] + \
                                p_arg_map[pred] + args_called + [") )"]

                        if pred not in has_wf:
                            wf, rfs = create_wf_rf(pred, arg_map[pred])
                            wf_list.append(wf)
                            rf_list = rf_list + rfs
                            has_wf.append(pred)
                        pred = ""
                        args_called = []
                    continue
                new_line.append(term)
        new_line = ' '.join(new_line)
        new_lines.append(new_line)
    new_lines += wf_list
    new_lines += rf_list
    return new_lines


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", help="Input file name")
    parser.add_argument("--inlining", action="store_true", help="Enable inlining")
    args = parser.parse_args()
    try:
        with open(args.filename, 'r') as file:
            lines = file.readlines()
    except FileNotFoundError:
        print(f"Error: File '{args.filename}' not found.")
        sys.exit(1)
    lines = reform(lines)
    arg_map = get_arg_map(lines)
    if args.inlining:
        lines = inlining(lines, arg_map)
        content = "\n".join(lines)
        output_file_inlined = args.filename.strip(".in") + "_inlined.in"
        with open(output_file_inlined, 'w') as file:
            file.write(content)
    lines = add_ranking_function(lines, arg_map)
    content = "\n".join(lines)
    output_file = "/".join(args.filename.split("/")[:-1])+"/rf_lexico.in"
    with open(output_file, 'w') as file:
        file.write(content)


if __name__ == "__main__":
    main()
