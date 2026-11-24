#!/usr/bin/env python3
"""Delete thin wrapper modules and point their callers at the wrapped declaration.

A wrapper is a module whose only declaration is a theorem `N` proved by naming another
declaration `X`, as in

    theorem N : T := by
      first | exact @X | exact X | (intros; apply X <;> assumption)

or `theorem N : T := X`.  For each wrapper this script

* resolves `X` (in the wrapper's namespace / `open` context) to a project declaration,
  following chains of wrappers;
* in every module importing the wrapper, rewrites references to `N` as `_root_.X'` (keeping a
  leading `@`), where `X'` is the final target;
* replaces the importer's `import W` by W's own imports plus the module declaring `X'`
  (all reachable from the importer before, so no cycle can appear), with the same modifier,
  at the same place in the header;
* deletes the wrapper file.

Wrappers are kept when `N` and `X` do not take the same sequence of explicit, implicit,
strict-implicit and instance arguments (parsed from their source by lean_signature.py; anything
it cannot parse counts as a mismatch), when the wrapper file has any column-0 line other than the
theorem and scaffolding (`open`, `namespace`, `section`, `set_option`, `attribute [local instance]`
and the like), when the wrapper file declares `variable`s, when `X` does
not resolve to exactly one project declaration, when a module that does not import the wrapper
directly names `N` (only direct importers are rewritten), when a caller
mentions `N` in a way that might not be a reference (field notation such as `N.f`, a local declaration of
the same short name, a possible string literal), when the wrapper is imported by a protected module, or when they are
listed in `scripts/collapse-wrappers-exclude.txt` (e.g. because a caller failed to compile).
This is not reversible by a script.

Usage: collapse_wrappers.py ROOT [--dry-run]
"""

import argparse
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import clump  # noqa: E402
from lean_signature import signature, telescope  # noqa: E402

FIRST_RE = re.compile(r"\bfirst\s*\|\s*exact\s+@?([^\s|()\[\]{},]+)")
TERM_RE = re.compile(r":=\s*(?:by\s+exact\s+)?@?([^\s|()\[\]{},]+)\s*$")
OPEN_RE = re.compile(r"^open\s+(?:scoped\s+)?(.*?)(?:\s+in)?\s*(?:--.*)?$")
# Lean 4.37.0-rc1: Init/Meta/Defs.lean, isLetterLike/isIdFirst/isIdRest.
# In particular, tuple brackets and λ/Π/Σ are not identifier characters.
ID_LETTERS = (
    r"A-Za-z_\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
    r"\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03b1-\u03ba\u03bc-\u03fb\u1f00-\u1ffe\u2100-\u214f"
    r"\U0001d49c-\U0001d59f"
)
ID_REST = ID_LETTERS + r"0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
# Keep escaped components atomic: «N.foo» is not the qualified name N.foo.
ID_COMPONENT = rf"(?:«[^»]*»|[{ID_LETTERS}][{ID_REST}]*)"
IDENT_RE = re.compile(rf"(@?)({ID_COMPONENT}(?:\.{ID_COMPONENT})*)")
PROTECTED = {"Main", "Statements", "Challenge"}
# Column-0 lines a wrapper file may have besides its theorem. A local instance only affects how
# the wrapper's own statement elaborates; callers never see it.
ALLOWED_OTHER = re.compile(
    r"^(?:open\b|namespace\b|end\b|section\b|noncomputable\s+section|@\[expose\]|public\s+section|set_option\b|universe\b|variable\b|--|/-|-/"
    r"|attribute\s+\[local\s+instance(?:\s+\d+)?\]\s)")


def contexts(body):
    """Yield (line, namespace list, opens list) for each column-0 command line."""
    stack, opens_stack, opens = [], [], []
    for l in body.split("\n"):
        if not l or l[0] in " \t":
            continue
        m = clump.SECTION_RE.match(l)
        if m:
            stack.append(("section", m.group(1))); opens_stack.append(list(opens)); continue
        m = clump.NAMESPACE_RE.match(l)
        if m:
            stack.append(("namespace", m.group(1))); opens_stack.append(list(opens)); continue
        m = clump.END_RE.match(l)
        if m and stack:
            stack.pop(); opens = opens_stack.pop(); continue
        m = OPEN_RE.match(l)
        if m and not l.rstrip().endswith(" in"):
            for tok in m.group(1).split():
                if tok in ("hiding", "renaming") or tok.startswith("("):
                    break
                opens.append(tok)
            continue
        yield l, [n for k, n in stack if k == "namespace"], opens


def find_wrapper(mod):
    lines = [l for l in mod.body.split("\n") if l.strip()]
    decl_lines = [l for l in lines if clump.DECL_RE.match(l)]
    if len(decl_lines) != 1 or not re.search(r"\b(theorem|lemma)\b", decl_lines[0].split(":")[0]):
        return None
    if len(mod.decls) != 1:
        return None
    # everything at column 0 other than the declaration must be scaffolding
    for l in lines:
        if l[0] in " \t" or l is decl_lines[0] or clump.DECL_RE.match(l):
            continue
        if not ALLOWED_OTHER.match(l):
            return None
    body = mod.body
    m = FIRST_RE.search(body) or TERM_RE.search(body.strip())
    if not m:
        return None
    target = m.group(1)
    ns, opens = [], []
    for l, n, o in contexts(body):
        if clump.DECL_RE.match(l):
            ns, opens = n, o
            break
    return next(iter(mod.decls)), target, ns, opens


def resolve(tok, ns, opens, index):
    if tok.startswith("_root_."):
        tok = tok[len("_root_."):]
        return tok if tok in index else None
    full_ns = ".".join(ns).split(".") if ns else []
    for i in range(len(full_ns), 0, -1):
        c = ".".join(full_ns[:i]) + "." + tok
        if c in index:
            return c
    hits = set()
    for o in opens:
        for i in range(len(full_ns), -1, -1):
            c = ".".join(full_ns[:i] + [o, tok]) if i else o + "." + tok
            if c in index:
                hits.add(c)
                break
    if tok in index:
        hits.add(tok)
    return hits.pop() if len(hits) == 1 else None


def written_names(full):
    """The ways a declaration named `full` may be written at its declaration site."""
    parts = full.split(".")
    return {".".join(parts[i:]) for i in range(len(parts))} | {"_root_." + full}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    root = args.root
    mods = clump.load(root)
    exclude = clump.read_exclude(os.path.join(os.path.dirname(__file__), "collapse-wrappers-exclude.txt"))

    index = {}
    dup = set()
    for m, mod in mods.items():
        for d in mod.decls:
            if d in index:
                dup.add(d)
            index[d] = m
    by_last = collections.defaultdict(set)
    for d in index:
        by_last[d.rsplit(".", 1)[-1]].add(d)

    rev = collections.defaultdict(list)
    for m, mod in mods.items():
        for x, _ in mod.imports:
            if x in mods:
                rev[x].append(m)

    wrappers = {}  # module -> (N, X)
    stats = collections.Counter()
    for m, mod in mods.items():
        if m in exclude or clump.lib_of(m) in ("Main", "Challenge") or mod.exotic:
            continue
        w = find_wrapper(mod)
        if not w:
            continue
        stats["candidates"] += 1
        n, tok, ns, opens = w
        x = resolve(tok, ns, opens, index)
        if x is None or x == n or n in dup or x in dup:
            stats["unresolved"] += 1
            continue
        if any(i in PROTECTED for i in rev[m]):
            stats["protected"] += 1
            continue
        if re.search(r"^variable\b", mod.body, re.M):
            stats["variables"] += 1
            continue
        # Callers apply N exactly as they would apply X only if both take the same
        # sequence of explicit / implicit / instance arguments.
        tn = telescope(signature(mod.body, written_names(n)) or "")
        tx = telescope(signature(mods[index[x]].body, written_names(x)) or "")
        if tn is None or tx is None or tn != tx:
            stats["signature-mismatch-or-unparsed"] += 1
            continue
        wrappers[m] = (n, x)
    name_to_mod = {n: m for m, (n, _) in wrappers.items()}

    def final(x, seen=()):
        while x in name_to_mod and x not in seen:
            seen = seen + (x,)
            x = wrappers[name_to_mod[x]][1]
        return x

    # Only direct importers are rewritten below, but a module that imports a wrapper through
    # another module can name `N` too (also as `N.f`). Keep every wrapper named outside its
    # direct importers.
    wrapper_of_last = collections.defaultdict(list)
    for m, (n, _) in wrappers.items():
        wrapper_of_last[n.rsplit(".", 1)[-1]].append(m)
    direct = {m: set(rev[m]) for m in wrappers}
    indirect = set()
    for c, mod in mods.items():
        for mt in IDENT_RE.finditer(mod.body):
            t = mt.group(2)
            parts = (t[len("_root_."):] if t.startswith("_root_.") else t).split(".")
            for i in range(1, len(parts) + 1):
                p = ".".join(parts[:i])
                for m in wrapper_of_last.get(parts[i - 1], ()):
                    n = wrappers[m][0]
                    if c != m and c not in direct[m] and (n == p or n.endswith("." + p)):
                        indirect.add(m)

    # Check every caller; drop wrappers with any doubtful use.
    plan = {}
    for m, (n, x) in wrappers.items():
        if m in indirect:
            stats["indirect-caller"] += 1
            continue
        last = n.rsplit(".", 1)[-1]
        ok = True
        for c in rev[m]:
            body = mods[c].body
            if last not in body:
                continue
            # Every string literal lies between the first and last double quote.
            # Keep doubtful uses, including raw/interpolated strings, rather than
            # rewrite their contents. This may also retain a use between strings.
            # The JSON in clump.py's `-- clump-header:` comments is not a string
            # literal, and would otherwise put almost all of a clump between quotes.
            code = "\n".join(l for l in body.split("\n") if not l.startswith(clump.HEADER_TAG))
            if '"' in code and last in code[code.index('"'):code.rindex('"') + 1]:
                ok = False
                break
            if any(d.rsplit(".", 1)[-1] == last for d in mods[c].decls):
                ok = False
                break
            for mt in IDENT_RE.finditer(body):
                t = mt.group(2)
                if "«" in t and last in t:
                    ok = False  # the source name index does not resolve escaped components
                    break
                if last in t.split(".")[:-1]:
                    ok = False  # `N.f` (field notation on N): the rewrite below only replaces whole names
                    break
                if t.rsplit(".", 1)[-1] != last:
                    continue
                if not (n == t or n.endswith("." + t)):
                    ok = False  # field notation or a different declaration with this name
                    break
                cands = [d for d in by_last[last] if d == t or d.endswith("." + t)]
                if len(cands) != 1:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            plan[m] = (n, x)
        else:
            stats["doubtful-caller"] += 1
    # A wrapper whose target is a dropped wrapper still works: final() only chases planned ones.
    name_to_mod = {n: m for m, (n, _) in plan.items()}
    wrappers = plan
    stats["collapsed"] = len(plan)
    print(dict(stats), file=sys.stderr)
    if args.dry_run:
        return

    # Rewrite callers. A caller may import several wrappers; handle all at once.
    edits = collections.defaultdict(list)
    for m in plan:
        for c in rev[m]:
            edits[c].append(m)

    def replacement_imports(w, seen):
        """Modules standing in for wrapper w: what w re-exported (its public imports, expanding
        planned wrappers) plus the module declaring its final target."""
        out = []
        for x, pub in mods[w].imports:
            if not pub:
                continue
            if x in plan:
                if x not in seen:
                    out += replacement_imports(x, seen | {x})
            else:
                out.append(x)
        out.append(index[final(plan[w][1])])
        return out

    for c, ws in edits.items():
        if c in plan:
            continue  # a wrapper importing a wrapper is itself deleted
        mod = mods[c]
        targets = {}
        for w in ws:
            n, x = plan[w]
            targets[n.rsplit(".", 1)[-1]] = (n, final(x))
        def sub(mt):
            at, t = mt.group(1), mt.group(2)
            last = t.rsplit(".", 1)[-1]
            if last in targets:
                n, x = targets[last]
                if n == t or n.endswith("." + t):
                    return at + "_root_." + x
            return mt.group(0)
        body = IDENT_RE.sub(sub, mod.body)
        # imports
        old = [(x, pub) for x, pub in mod.imports]
        keep = collections.OrderedDict()
        for x, pub in old:
            if x in plan:
                # same modifier as the caller's import of the wrapper
                for y in replacement_imports(x, {x}):
                    if y != c and y not in plan:
                        keep[y] = keep.get(y, False) or pub
            else:
                keep[x] = keep.get(x, False) or pub
        # Keep the caller's import order: Lean tries instances of equal priority in an order that
        # depends on it, and a reordered header can make instance search time out.
        header = ["module", ""] + [("public import " if p else "import ") + x for x, p in keep.items()]
        text = "\n".join(header) + "\n\n" + body
        with open(os.path.join(root, mod.path), "w", encoding="utf-8") as f:
            f.write(text)
    for m in plan:
        os.remove(os.path.join(root, mods[m].path))


if __name__ == "__main__":
    main()
