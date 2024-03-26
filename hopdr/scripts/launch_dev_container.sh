#!/bin/bash

root=`dirname "${BASH_SOURCE[0]}"`/../

cd $root/../
docker rm -f vscoder-hopdr
docker run -w "/work" -v "$PWD:/work" --name=vscode-hopdr moratorium08/hopdr true
