#!/usr/bin/env python3
"""List the Lean files under a source root, relative to it and sorted, one per line.

  list-files.py SRC_ROOT [SAMPLE]

With SAMPLE greater than zero, prints that many files, evenly spaced through the sorted list.
"""
import os
import sys

src = sys.argv[1]
sample = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] else 0
files = []
for root, _dirs, names in os.walk(src):
    for name in names:
        if name.endswith(".lean"):
            files.append(os.path.relpath(os.path.join(root, name), src).replace(os.sep, "/"))
files.sort()
if 0 < sample < len(files):
    files = [files[i * len(files) // sample] for i in range(sample)]
sys.stdout.write("".join(f + "\n" for f in files))
