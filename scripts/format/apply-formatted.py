#!/usr/bin/env python3
"""Copy the formatted text of the selected files over a checkout.

  apply-formatted.py PASS_LIST FORMATTED_ROOT SRC_ROOT

PASS_LIST holds paths relative to both roots. A path that is not already a file under SRC_ROOT,
or whose formatted text is missing or empty, stops the script.
"""
import os
import sys

pass_list, fmt_root, src_root = sys.argv[1:4]
n = 0
for rel in [l.strip() for l in open(pass_list, encoding="utf-8") if l.strip()]:
    src = os.path.join(fmt_root, rel)
    dst = os.path.join(src_root, rel)
    if os.path.isabs(rel) or ".." in rel.split("/") or not rel.endswith(".lean"):
        sys.exit("unexpected path: " + rel)
    if not os.path.isfile(dst) or os.path.islink(dst):
        sys.exit("not a file in the checkout: " + rel)
    data = open(src, "rb").read()
    if not data:
        sys.exit("empty formatted file: " + rel)
    with open(dst, "wb") as f:
        f.write(data)
    n += 1
print("copied", n)
