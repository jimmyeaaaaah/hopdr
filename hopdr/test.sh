#!/bin/sh

set -eu

cargo build 
CMD="target/debug/hopdr"
OPTIONS=--no-preprocess

VALID=inputs/valid
INVALID=inputs/invalid

for f in `find $VALID | grep "\\.in$"`
do
   echo $f
   r=`timeout 15 $CMD $OPTIONS --input $f` 
   if [ $r != "Valid" ]; then
     exit -1
   fi
done

for f in `find $INVALID | grep "\\.in$"`
do
   echo $f
   r=`timeout 15 $CMD $OPTIONS --input $f` 
   if [ $r != "Invalid" ]; then
     echo -e "\e[31mFAIL\e[m"
     exit -1
   fi
done

echo "OK"
