#!/usr/bin/env python3
"""Move Lean modules to new paths and rewrite every reference to their names.

The mapping file has one move per line: the old module name and the new one, separated by a
tab.  Blank lines and lines starting with `#` are skipped.  The script

* moves `src/<old>.lean` to `src/<new>.lean` and stages the move;
* in every tracked text file that mentions an old name, replaces each whole occurrence of it
  with the new name.  That covers import lines, the module names that scripts/clump.py writes
  into comments, and the lists in scripts/*-exclude.txt.

A name counts as whole when the characters on either side cannot extend it: a letter, digit,
`_`, `'`, `!` or `?` after it, or any of those or `.` before it.  So `Old.Module.foo`, a
declaration in a namespace that happens to match the module name, is left alone.  Imports keep
their order and their `public`/`private`/`meta`/`all` modifiers.  Declaration names do not
change, because they come from namespaces, not from file paths.

With --rewrite-only nothing is moved.  Use it on a branch made before a move, to point the
branch's imports at the new names before merging main.

Usage: move_modules.py ROOT MAPPING [--rewrite-only]
"""

import argparse
import os
import re
import subprocess
import sys

IDENT = r"[\w'!?]"
COMPONENT = re.compile(r"[^\W\d][\w']*")
TOKEN = re.compile(rf"(?<![\w'!?.]){IDENT}+(?:\.{IDENT}+)*")


def read_mapping(path):
    moves = {}
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.rstrip("\n")
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            sys.exit(f"{path}:{n}: expected `old<TAB>new`")
        old, new = parts[0].strip(), parts[1].strip()
        for name in (old, new):
            if not all(COMPONENT.fullmatch(c) for c in name.split(".")):
                sys.exit(f"{path}:{n}: {name!r} is not a plain module name (guillemets are not supported)")
        if old == new:
            continue
        if old in moves:
            sys.exit(f"{path}:{n}: {old} is moved twice")
        moves[old] = new
    targets = list(moves.values())
    if len(set(targets)) != len(targets):
        sys.exit("two modules are moved to the same name")
    if set(targets) & set(moves):
        sys.exit("a module is moved to the old name of another; split the mapping into two runs")
    return moves


def git(root, *args, data=None):
    return subprocess.run(["git", "-C", root, *args], input=data, capture_output=True, check=True).stdout


def src_path(root, module):
    return os.path.join(root, "src", *module.split(".")) + ".lean"


def move_files(root, moves):
    for old, new in moves.items():
        if not os.path.exists(src_path(root, old)):
            sys.exit(f"src/{old.replace('.', '/')}.lean does not exist")
        if os.path.exists(src_path(root, new)):
            sys.exit(f"src/{new.replace('.', '/')}.lean already exists")
    paths = []
    for old, new in sorted(moves.items()):
        a, b = src_path(root, old), src_path(root, new)
        os.makedirs(os.path.dirname(b), exist_ok=True)
        os.rename(a, b)
        paths += [os.path.relpath(a, root), os.path.relpath(b, root)]
    git(root, "add", "-A", "--pathspec-from-file=-", "--pathspec-file-nul",
        data="\0".join(paths).encode())
    for old in moves:  # drop directories the move emptied
        d = os.path.dirname(src_path(root, old))
        while d != os.path.join(root, "src") and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)


def rewrite(root, moves):
    prefixes = sorted({old.rsplit(".", 1)[0] + "." for old in moves})
    args = ["grep", "-I", "-l", "-z", "-F"]
    for p in prefixes:
        args += ["-e", p]
    try:
        files = [f for f in git(root, *args).decode().split("\0") if f]
    except subprocess.CalledProcessError as e:
        if e.returncode == 1:  # no file mentions any old name
            return 0, 0
        raise
    changed, count = [], 0
    for rel in files:
        path = os.path.join(root, rel)
        with open(path, encoding="utf-8", newline="") as f:  # keep CRLF line endings as they are
            text = f.read()
        n = 0

        def sub(m):
            nonlocal n
            new = moves.get(m.group(0))
            if new is None:
                return m.group(0)
            n += 1
            return new

        out = TOKEN.sub(sub, text)
        if n:
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(out)
            changed.append(rel)
            count += n
    if changed:
        git(root, "add", "--pathspec-from-file=-", "--pathspec-file-nul", data="\0".join(changed).encode())
    return len(changed), count


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("root")
    ap.add_argument("mapping")
    ap.add_argument("--rewrite-only", action="store_true", help="rewrite references without moving files")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    moves = read_mapping(a.mapping)
    if not a.rewrite_only:
        move_files(root, moves)
        print(f"moved {len(moves)} files")
    nfiles, count = rewrite(root, moves)
    print(f"rewrote {count} references in {nfiles} files")


if __name__ == "__main__":
    main()
