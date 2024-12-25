#!/bin/bash

# fileを1つずつ走査
find ./in -type f -name "hflz.in" | while read hflz_file; do
    echo "Processing $hflz_file"
    dirname=$(dirname "$hflz_file")
    benchmark_name=$(basename "$dirname")

    out_filename="out/$benchmark_name.txt"

    timeout_duration=300
    if ! timeout $timeout_duration python3 -u ../../../hirobe/counter_example_guided.py "$hflz_file" --hflz-inlining --nuhfl-inlining > "$out_filename" 2>&1; then
        if [ $? -eq 124 ]; then
            echo "timeout" >> "$out_filename"
        fi
    fi
done

