#!/bin/bash

if [[ "$#" -lt 2 || "$#" -gt 3 ]]; then
    echo "Usage: $0 <filename> <number> [--inlining]"
    exit 1
fi

# ディレクトリを引数1から取得
filename="$1"
dir=$(dirname "$filename")
rf_file="$dir/rf.in"

# counterの数も引数2から取得
n_counter="$2"

# --inliningのオプション
inlining=""
if [[ "$#" -eq 3 && "$3" == "--inlining" ]]; then
    inlining="--inlining"
fi

# hflzをranking function のnuhflに変換
python3 transform_hflz_with_rf.py "$filename" "$n_counter"

# 変換したファイルを使ってpythonを実行
python3 counter_example_guided.py "$rf_file" $inlining
