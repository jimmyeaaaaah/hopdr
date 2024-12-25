#!/bin/bash

hflz_file=$1

cleanup() {
    echo "Keyboard interrupt detected. Cleaning up..."
    exit 1
}

# trapを使ってSIGINTをキャッチ
trap cleanup SIGINT

echo "Processing $hflz_file"
dirname=$(dirname "$hflz_file")
benchmark_name=$(basename "$dirname")
out_filename="out/$benchmark_name.txt"

# counter example guided refinementを実行
echo $hflz_opt_file
timeout_duration=300
if ! timeout $timeout_duration python3 -u ../../../hirobe/counter_example_guided.py "$hflz_file" --hflz-inlining --nuhfl-inlining > "$out_filename" 2>&1; then
    if [ $? -eq 124 ]; then
        echo "timeout" >> "$out_filename"
    fi
fi

