#!/usr/bin/env python3
"""Remove a definition from ImportGraph that the formatter's Lean now has in core.

  patch-import-graph.py PATH/TO/ImportGraph/Lean/Syntax.lean

The formatter adds `Lean.SourceInfo.getLeading?` to `Lean.Fmt.Util.Basic`. ImportGraph, which
Mathlib imports, defines the same name, so Mathlib cannot be imported next to the formatter until
one of the two is gone. This drops ImportGraph's copy and imports the core one in its place.
Fails if the file does not look as expected.
"""
import sys

path = sys.argv[1]
src = open(path, encoding="utf-8").read()
old_def = '''/-- Gets the leading whitespace of `.original` `SourceInfo`, or `none` if not `.original`. -/
def SourceInfo.getLeading? : SourceInfo → Option Substring.Raw
  | .original (leading := leading) .. => leading
  | _ => none

'''
if src.count(old_def) != 1:
    sys.exit("patch-import-graph: the definition of SourceInfo.getLeading? was not found exactly once")
src = src.replace(old_def, "")
old_import = "public import Lean.Syntax\n"
if src.count(old_import) != 1:
    sys.exit("patch-import-graph: the import of Lean.Syntax was not found exactly once")
src = src.replace(old_import, old_import + "public import Lean.Fmt.Util.Basic\n")
open(path, "w", encoding="utf-8").write(src)
