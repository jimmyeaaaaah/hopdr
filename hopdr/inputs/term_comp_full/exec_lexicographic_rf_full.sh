#!/bin/bash

# fileを1つずつ走査
find ./in -type f -name "hflz.in" | while read hflz_file; do
    echo "Processing $hflz_file"
    dirname=$(dirname "$hflz_file")
    benchmark_name=$(basename "$dirname")
    hflz_opt_file=$(echo "$hflz_file" | sed 's/\.in$/_opt.in/')
    # nuhfl_file="$dirname/rf_lexico.in"
    out_filename="out/$benchmark_name.txt"

    # # HFLZのoptimizationを実行。　"hflz_opt.in"が出力される
    # python3 ../../../hirobe/optimize_raw_hflz.py "$hflz_file"

    # counter example guided refinementを実行
    timeout_duration=300
    if ! timeout $timeout_duration python3 ../../../hirobe/counter_example_guided.py "$hflz_opt_file" --hflz-inlining --nuhfl-inlining > "$out_filename" 2>&1; then
        echo "timeout" > "$out_filename"
    fi
done

