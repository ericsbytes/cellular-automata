#!/bin/bash

echo "$1" | 
tr -d '()' | 
xargs -n2 | 
awk '{printf "%s(0->%s)", sep, $2; sep=" + "} END{print ""}'
