#!/usr/bin/env bash
# rebase latex files to the current directory, copy zariski-style files from given path
# also rebase main.tex

if [ "$#" -lt 1 ]; then
  echo "Usage: $0 path-to-zariski-style-files"
  exit 1
fi


for file in literature.bib zariski.cls zariski.sty zariski-base.cls zariski-small.cls; do
    if [ -f "$@$file" ]; then
	cp "$@$file" "$file"
	# Use sed to replace ../util/SOMETHING with SOMETHING
	sed -i 's|\.\./util/\([^/]*\)|\1|g' "$file"
	echo "Processed file: $file"
    else
	echo "File not found: $file"
    fi
done

sed -i 's|\.\./util/\([^/]*\)|\1|g' main.tex
echo "Processed file: main.tex"


