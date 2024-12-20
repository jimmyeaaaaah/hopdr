import sys

def reform(lines):
    contents = ' '.join(line.strip() for line in lines)
    quantifier_stack = []
    new_lines = []
    new_line = ""
    # 改行を述語ごとに行う
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
    # スペースを適切に入れる
    for i, line in enumerate(new_lines):
        line = line.replace("∀", " ∀ ").replace("∃", " ∃ ").replace(".", " . ").replace("(", " ( ").replace(")", " ) ").replace("  ", " ")
        new_lines[i] = line
    return new_lines

def migrate_quantifier(lines):
     new_lines = []
     for line in lines:
          left = []
          right = []
          is_left = True
          is_forall = False
          forall = []
          foralls = []
          terms = line.split()
          for term in terms:
               if is_left:
                    left.append(term)
                    if term == "=u" or term == "=v":
                         is_left = False
               else:
                    if term == "∀":
                         is_forall = True
                    if is_forall:
                         forall.append(term)
                         if term == ".":
                              is_forall = False
                              foralls.append(" ".join(forall))
                    else:
                         right.append(term)
          newline = left + forall + right
          new_lines.append(" ".join(newline))
     return new_lines


def check_is_term(str):
     is_term = True
     terms = str.split(" ")
     for term in terms:
          if term == "/\\" or term == "\\/" :
               is_term = False
               break
     return is_term

def check_is_quantifier(str):
     if str.endswith("."):
          return True
     else:
          return False

def remove_outer_paren(exp_terms):
    paren_idx_pair = []
    paren_start_idx_queue = []
    for i in range(len(exp_terms)):
        term = exp_terms[i]
        if term == "(":
            paren_start_idx_queue.append(i)
        elif term == ")":
            start_idx = paren_start_idx_queue.pop()
            paren_idx_pair.append([start_idx, i])
    n_outer_paren = 0
    paren_idx_pair = sorted(paren_idx_pair)
    paren_idx = 0
    for pair in paren_idx_pair:
        if pair[0] == paren_idx and (pair[0] + pair[1]) == len(exp_terms)-1:
            n_outer_paren += 1
            paren_idx += 1
        else:
            break
    if n_outer_paren != 0:
        exp_terms = exp_terms[n_outer_paren: -n_outer_paren]
    return exp_terms

def add_paren(input_str):
     print(input_str)
     if check_is_term(input_str) or check_is_quantifier(input_str):
          return input_str
     terms = input_str.split(" ")
     terms = remove_outer_paren(terms)
     n_paren = 0
     blocks = []
     block = []
     junctions = []
     quantifiers = []
     for term in terms:
          if term == "(":
               n_paren += 1
               block.append(term)
               continue
          elif term == ")":
               n_paren -= 1
               block.append(term)
               continue
          elif term == ".":
               block.append(term)
               quantifiers.append(" ".join(block))
               block = []
               continue
          elif term == "\\/" or term == "/\\":
               if n_paren != 0:
                    block.append(term)
                    continue
               blocks.append(" ".join(block))
               junctions.append(term)
               block = []
               continue
          block.append(term)
     if len(block) != 0:
          blocks.append(" ".join(block))
     print(blocks)

     for i, block in enumerate(blocks):
          blocks[i] = add_paren(block)
     n_conjunction = 0
     for i, junction in enumerate(junctions):
          if junction == "/\\":
               blocks[i-n_conjunction] = "( " + blocks[i-n_conjunction] + " /\\ " + blocks[i-n_conjunction+1] + " )"
               blocks[i-n_conjunction+1:] = blocks[i-n_conjunction+2:]
               n_conjunction += 1
     res = quantifiers
     for i in range(len(blocks)-1):
          res.append("(" )
     for i, block in enumerate(blocks):
          if i == 0:
               res.append(block)
          else:
               res.append(f"\\/ {block} )")
     res = " ".join(res)
     return res

def main(filename):
     with open(filename, "r") as f:
          lines = f.readlines()
     lines = reform(lines)
     lines = migrate_quantifier(lines)
     newlines = []
     for line in lines:
          if line.startswith("%HES"):
               newlines.append(line)
               continue
          newline = ""
          line = line.strip()
          line = line.rstrip(".")
          left = []
          right = []
          is_right = False
          terms = line.strip().replace("  ", " ").split(" ")
          for term in terms:
               if is_right:
                    right.append(term)
               else:
                    left.append(term)
               if term == "=v" or term == "=u":
                    is_right = True
                    left = " ".join(left)
                    newline = left
          right = " ".join(right)
          newline = newline + " " + add_paren(right) + "."
          newlines.append(newline)
     content = "\n".join(newlines)
     with open(filename, "w") as f:
          f.write(content)

if __name__ == "__main__":
    filename = sys.argv[1]
    main(filename)

    