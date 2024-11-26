#!/bin/bash

# ディレクトリを引数1から取得
filename="$1"
dir=$(dirname "$filename")
rf_file="$dir/rf_lexico.in"

# --inliningのオプション
inlining=""
if [[ "$#" -eq 2 && "$2" == "--inlining" ]]; then
    inlining="--inlining"
fi

# hflzをranking function のnuhflに変換
python3 transform_hflz_with_rf.py "$filename" --inlining

# 変換したファイルを使ってpythonを実行
python3 counter_example_guided.py "$rf_file" $inlining
