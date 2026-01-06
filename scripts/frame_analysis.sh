#!/bin/bash
# Usage Check
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <log_file> <elf_binary>"
    echo "Example: $0 crash.log ./kernel.elf"
    exit 1
fi
# --- Color Definitions ---
# We use $(tput) if available for maximum compatibility, otherwise fallback to raw codes
if command -v tput &> /dev/null; then
    RED=$(tput setaf 1)
    GREEN=$(tput setaf 2)
    YELLOW=$(tput setaf 3)
    CYAN=$(tput setaf 6)
    GRAY=$(tput setaf 8 2>/dev/null || tput setaf 7) # Fallback to white if gray not supported
    RESET=$(tput sgr0)
else
    RED='\033[0;31m'
    GREEN='\033[1;32m'
    YELLOW='\033[1;33m'
    CYAN='\033[0;36m'
    GRAY='\033[0;90m'
    RESET='\033[0m'
fi

LOG_FILE="$1"
ELF_BINARY="$2"

# Check if addr2line exists, prefer llvm-addr2line for Rust/Clang builds if available
if command -v llvm-addr2line &> /dev/null; then
    ADDR2LINE="llvm-addr2line"
elif command -v addr2line &> /dev/null; then
    ADDR2LINE="addr2line"
else
    echo "Error: Neither 'addr2line' nor 'llvm-addr2line' found."
    exit 1
fi
echo "=== Resolving Stack Trace ==="
echo "Binary: $ELF_BINARY"
echo "----------------------------------------------"

# 1. sed: Slice the log
# 2. grep: Extract addresses
# 3. tr: Clean brackets
sed -n '/---BACKTRACE---:/,/---END---/p' "$LOG_FILE" | \
grep -o '\[[0-9a-fA-F]\+\]' | \
tr -d '[]' | \
while read -r addr; do
    
    # Resolve address
    # -p: Pretty prints "Function at File:Line"
    raw_result=$($ADDR2LINE -e "$ELF_BINARY" -f -C -i -p "$addr")
    
    # Use awk to inject colors safely. 
    # We substitute the first occurrence of " at " with the colored version.
    echo "$raw_result" | awk -v addr="$addr" \
                             -v y="$YELLOW" \
                             -v g="$GREEN" \
                             -v c="$CYAN" \
                             -v gr="$GRAY" \
                             -v r="$RESET" \
        '{ 
           # Replace " at " with " <GRAY>at<RESET> <CYAN>"
           sub(/ at /, " " gr "at" r " " c); 
           
           # Print: [YELLOW addr RESET] GREEN line RESET
           printf "[%s%s%s] %s%s%s\n", y, addr, r, g, $0, r
        }'
done

echo "----------------------------------------------"
