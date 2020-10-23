#!/bin/bash

file_type=$(file "$2")
arch=$(echo "$file_type" | cut -d ',' -f 2 | cut -d ' ' -f 2)
endian=$(echo "$file_type" | cut -d ',' -f 1 | cut -d ' ' -f 4)

TVHEADLESS=1 "$1" -B -o"$3" "$2" > /dev/null
