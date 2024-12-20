# muHFLファイルをきれいにする(変数名、冗長な述語の整理、改行)
import re
import os
import sys
import argparse

# 文字列が整数(負の数を含む)かどうかを判定する
def is_integer(s):
    try:
        int(s)
        return True
    except ValueError:
        return False

# 一旦ピリオドごとに行を区切る
def pre_processing(lines):
    for i, line in enumerate(lines):
        lines[i] = line.rstrip()
    content = " ".join(lines)

    # 指定の文字をスペースで分離
    content = content.replace("∀", " ∀ ")
    content = content.replace(".", " . ")
    content = content.replace("(", " ( ")
    content = content.replace(")", " ) ")
    pattern = re.compile(r'\s{2,}')
    content = re.sub(pattern, ' ', content)

    lines = content.split(".")
    lines = [s for s in lines if s != ""]

    new_lines = []
    concat = False
    for line in lines:
        if line.startswith("%HES"):
            line = line[5:]
        words = line.split()
        if concat and len(new_lines) > 0:
            new_lines[-1] = new_lines[-1] + '.' + line
        else:
            new_lines.append(line)
        if len(words)>1 and words[-2] == '∀':
            concat = True
        else:
            concat = False

    lines = new_lines
    new_lines = ["%HES\n"]
    for line in lines:
        if line == ' ' or line == '':
            continue
        line = re.sub(r"\+\s*-", "-", line)
        line = line + " .\n"
        pattern = re.compile(r'\s{2,}')
        line = re.sub(pattern, ' ', line)
        new_lines.append(line)
    return new_lines

# Sentryを合体
def concat_sentry(lines):
    newlines = []
    if(lines[1].strip() != "Sentry =v State_main_entry ."):
        return lines
    else:
        for line in lines:
            words = line.split()
            if(len(words) > 1 and words[0] == "State_main_entry" and words[1] == "=v"):
                new_sentry = "Sentry =v "+' '.join(words[2:]) + '\n'
                if(len(newlines)>2): 
                    newlines[1] = new_sentry
            else:
                newlines.append(line)
    return newlines

# 改行をする
def line_break(lines):
    for i, line in enumerate(lines):
        pattern = re.compile(r'(.* =[uv])')
        newline = pattern.sub(r'\1\n', line)
        lines[i] = newline
    
    for i, line in enumerate(lines):
        def start_newline(index):
            start = (index >= 3 and (line[index-3:index+1] == "\/ (" or line[index-3:index+1] == "/\ (")) or (index >= 2 and (line[index-2:index+1] == ". ("))
            return start

        n_newline = 0
        bracket_stack = []
        newline = line
        for index, w  in enumerate(line):
            if w == '(':
                if start_newline(index):
                    newline = newline[:index + 1 + n_newline] + '\n' + newline[index + 1 + n_newline:]
                    n_newline += 1
                    bracket_stack.append("Y")
                else:
                    bracket_stack.append("N")
            elif w == ')':
                if len(bracket_stack) > 0:
                    if bracket_stack[-1] == "Y":
                        newline = newline[:index + n_newline] + '\n' + newline[index + n_newline:]
                        n_newline += 1
                        bracket_stack.pop()
                    else:
                        bracket_stack.pop()
        lines[i] = newline

    contents = ''.join(lines)
    lines = contents.split('\n')

    # タブを入れる
    n_tabs = 0
    newlines = []
    for i, line in enumerate(lines):
        def tab(i, line):
            increase_tab = (len(line) > 0 and line[-1] == '(') or (len(line) > 1 and ( line[-2:] == '=v' or line[-2:] == '=u'))
            return increase_tab
        newlines.append(' ' * 4 * n_tabs + line + '\n')
        if tab(i, line):
            n_tabs += 1
        else:
            if i != 0:
                n_tabs -= 1
    return newlines

# 変数名を整理
def rename_variables(lines):
    # (),∀,.の前後にスペースを入れる
    newlines = []
    for line in lines:
        line = line.replace("(", " ( ")
        line = line.replace(")", " ) ")
        line = line.replace("∀", " ∀ ")
        line = line.replace(".", " . ")
        line = line.replace("  ", " ")
        newlines.append(line)
    lines = newlines
    reserved_words = ["","Sentry", "%HES","=v", "=u", "∀", 
                      "\/", "/\\", '+', '-', '*', '/', '.', 
                      "<", ">", "<=", ">=", "=", "!=", "<>", "(", ")", "true", "false"]
    
    newlines = []
    variable_map = {}   # 変数名のマップ (小文字)
    predicate_map = {}       # 述語変数名のマップ (大文字)
    def next_variable_name(n, capitalize):
        if capitalize:
            return chr(ord('P') + n)
        else:
            return chr(ord('a') + n)
        
    for line in lines:
        line = line.rstrip().replace("  ", " ")
        words = line.split(" ")
        new_words = []
        for word in words:
            if word == "!=" or word == "/=":
                word = "<>"
            # if word.startswith("-") and len(word) > 1:
            #     word = f"( {word} )"
            #     new_words.append(word)
            #     continue
            if not (word in reserved_words or is_integer(word)):
                if word in variable_map:
                    new_words.append(variable_map[word])
                elif word in predicate_map:
                    new_words.append(predicate_map[word])
                else:
                    if len(word) > 0 and word[0].isupper():
                        new_name = next_variable_name(len(predicate_map), True)
                        predicate_map[word] = new_name
                        new_words.append(new_name)
                    else:
                        new_name = next_variable_name(len(variable_map), False)
                        variable_map[word] = new_name
                        new_words.append(new_name)
            else:
                new_words.append(word)
        line = ' '.join(new_words) + '\n'
        newlines.append(line)
    return newlines


def process_file(file_path):
    with open(file_path, 'r') as file:
        lines = file.readlines()
    lines = pre_processing(lines)
    lines = concat_sentry(lines)
    lines = rename_variables(lines) 
    lines = line_break(lines)  
    
    content = "".join(lines)
    return content

def main():
    filename = sys.argv[1]
    output_file = ""
    if filename[-3:] != ".in":
        raise ValueError("Invalid filename")
    else:
        output_file = filename[:-3] + "_opt.in"
    parser = argparse.ArgumentParser(description="Process input and output files")
    parser.add_argument("input_file", help="Input file path")
    parser.add_argument("output_file", help="Output file path")
    contents = process_file(filename)
    with open(output_file, 'w') as outfile:
        outfile.write(contents)
                
if __name__ == "__main__":
    main()

