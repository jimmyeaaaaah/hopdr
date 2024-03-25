#!/bin/bash

root=`dirname "${BASH_SOURCE[0]}"`/../
cd $root/docker
docker build --platform linux/amd64 . -t moratorium08/hopdr

