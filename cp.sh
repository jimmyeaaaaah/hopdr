#!/bin/bash

container_id="28be954cb3a6"
base_dir="/Users/hirobeyurika/Desktop/研究/hopdr/hopdr/inputs/bote_timeouted"

while IFS= read -r dir_name; do
    mkdir -p "${base_dir}/${dir_name}"
    docker cp "${container_id}:/home/opam/timeouted_both/${dir_name}/hflz_opt.in" "${base_dir}/${dir_name}/hflz_opt.in"
done < dirs_bote_timeouted.txt