#!/usr/bin/env python3
"""Collect the tokens that the project's own notation and syntax declarations introduce.

  project-tokens.py SRC_ROOT OUT

Reads every string literal on a line that starts a `notation`, `infix`, `prefix`, `postfix`,
`macro`, `syntax`, `elab` or `binder_predicate` declaration. This over-collects on purpose: the
result is only used as part of the superset of tokens that split-check.py protects.
"""
import os
import re
import sys

src, out = sys.argv[1:3]
decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:scoped|local|private)\s+)*"
                  r"(?:notation3?|infixl?|infixr?|prefix|postfix|macro|syntax|elab|binder_predicate)\b")
lit = re.compile(r'"((?:[^"\\]|\\.)*)"')
tokens = set()
for root, _dirs, names in os.walk(src):
    for name in names:
        if not name.endswith(".lean"):
            continue
        for line in open(os.path.join(root, name), encoding="utf-8", errors="replace"):
            if decl.match(line):
                for m in lit.finditer(line):
                    t = m.group(1).strip()
                    if t:
                        tokens.add(t)
with open(out, "w", encoding="utf-8") as f:
    f.write("".join(t + "\n" for t in sorted(tokens)))
print("%d tokens" % len(tokens))
