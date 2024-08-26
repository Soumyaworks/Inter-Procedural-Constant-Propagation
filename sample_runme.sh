#!/bin/bash

# Define input directory path
input_directory="/path/to/input_directory containing ll files"

# Check if the input directory exists
if [ ! -d "$input_directory" ]; then
  echo "Input directory does not exist: $input_directory"
  exit 1
fi

# Iterate over all .ll files in the input directory
for ll_file in "$input_directory"/*.ll; do
  if [ -f "$ll_file" ]; then
    
    filename=$(basename "$ll_file" .ll)
    
    # Run the command with the current .ll file
    /path/to/llvm-project/build/bin/opt -load /path/to/llvm-project/build/lib/constfolding.so -constfolding -enable-new-pm=0 "$ll_file" > "${filename}_output.ll"
    
  fi
done