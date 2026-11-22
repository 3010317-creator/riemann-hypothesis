#!/usr/bin/env python3
"""Text-level safety check of formatter output, independent of any Lean environment.

  split-check.py LIST ORIG_ROOT FMT_ROOT OUT_TSV TOKEN_FILE...

A formatter may only change whitespace, apart from dropping the separators `;` and `,` in favour
of a line break. That is safe only if no whitespace lands inside a token and no two tokens are
run together. Which character sequences are tokens depends on the notation in scope, so the check
uses a superset: every token of the given files (one per line), whatever its scope.

For each file it aligns the non-whitespace characters of original and formatted text and reports

  UNALIGNED  a non-whitespace change other than a dropped `;` or `,`
  SPLIT      whitespace inserted between two characters that were adjacent, inside a known token
  MERGED     whitespace removed so that a known token, or one longer word, now spans the junction
  OK         none of the above

OUT_TSV gets `STATUS  path  detail  dropped-semicolons  dropped-commas`.
"""
import os
import sys
import unicodedata
from multiprocessing import Pool

list_path, orig_root, fmt_root, out_path = sys.argv[1:5]
token_files = sys.argv[5:]

TOKENS = set()
for path in token_files:
    for line in open(path, encoding="utf-8"):
        t = line.strip()
        if len(t) >= 2:
            TOKENS.add(t)
LENGTHS = sorted({len(t) for t in TOKENS})


def spanning_token(text, pos):
    """A known token that covers both text[pos-1] and text[pos], or None."""
    for length in LENGTHS:
        for d in range(1, length):
            start = pos - d
            if start < 0:
                break
            if text[start:start + length] in TOKENS:
                return text[start:start + length]
    return None


def is_word_char(c):
    if c in "_'!?":
        return True
    cat = unicodedata.category(c)
    return cat[0] in "LN" or cat in ("Mn", "Mc")


def check(rel):
    try:
        orig = open(os.path.join(orig_root, rel), encoding="utf-8").read()
        fmt = open(os.path.join(fmt_root, rel), encoding="utf-8").read()
    except OSError as e:
        return ("IO_ERROR", rel, str(e)[:120], 0, 0)
    oi = [i for i, c in enumerate(orig) if not c.isspace()]
    fi = [i for i, c in enumerate(fmt) if not c.isspace()]
    pairs = []  # (index into orig, index into fmt) of matched characters
    i = j = 0
    semis = commas = 0
    n, m = len(oi), len(fi)
    while i < n and j < m:
        a, b = orig[oi[i]], fmt[fi[j]]
        if a == b:
            pairs.append((oi[i], fi[j]))
            i += 1
            j += 1
        elif a == ";":
            semis += 1
            pairs.append(None)  # a separator was here: not a junction between two tokens
            i += 1
        elif a == ",":
            commas += 1
            pairs.append(None)
            i += 1
        else:
            ctx = orig[max(0, oi[i] - 30):oi[i] + 30].replace("\n", " ").replace("\t", " ")
            return ("UNALIGNED", rel, "near: " + ctx, semis, commas)
    while i < n and orig[oi[i]] in ";,":
        semis += orig[oi[i]] == ";"
        commas += orig[oi[i]] == ","
        i += 1
    if i < n or j < m:
        return ("UNALIGNED", rel, "trailing text differs", semis, commas)
    for k in range(1, len(pairs)):
        p, q = pairs[k - 1], pairs[k]
        if p is None or q is None:
            continue
        adj_orig = q[0] == p[0] + 1
        adj_fmt = q[1] == p[1] + 1
        if adj_orig and not adj_fmt:
            t = spanning_token(orig, q[0])
            if t is not None:
                ctx = orig[max(0, q[0] - 25):q[0] + 25].replace("\n", " ")
                return ("SPLIT", rel, "token %r in: %s" % (t, ctx), semis, commas)
        elif adj_fmt and not adj_orig:
            t = spanning_token(fmt, q[1])
            if t is None and is_word_char(fmt[p[1]]) and is_word_char(fmt[q[1]]):
                t = "two words joined"
            if t is not None:
                ctx = fmt[max(0, q[1] - 25):q[1] + 25].replace("\n", " ")
                return ("MERGED", rel, "%r in: %s" % (t, ctx), semis, commas)
    return ("OK", rel, "", semis, commas)


if __name__ == "__main__":
    files = [l.strip() for l in open(list_path, encoding="utf-8") if l.strip()]
    with Pool(int(os.environ.get("CHECK_JOBS", "4"))) as pool, open(out_path, "w", encoding="utf-8") as out:
        for row in pool.imap(check, files, chunksize=200):
            out.write("\t".join(str(x) for x in row) + "\n")
