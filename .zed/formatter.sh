#!/bin/bash
tmpfile=$(mktemp)
echo $2 > "$tmpfile"
verusfmt "$tmpfile" >/dev/null 2>&1
cat "$tmpfile"
rm "$tmpfile"
