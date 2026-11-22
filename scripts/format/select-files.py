#!/usr/bin/env python3
"""Decide which formatted files may be proposed, and summarize the run.

A file is taken only if the formatter changed it (`OK`), the text check passed (`OK` in the
split-check table) and the syntax comparison on the project's toolchain says `SAME`. The paths
given with --keep are never taken.

Writes into OUT_DIR:
  pass.txt       the files taken, relative to src/
  excluded.tsv   every other file the formatter did not leave alone, with the reason
  summary.json   the counts
  summary.md     the same, readable

Exits with an error if a listed file has no formatter result, or a changed file has no check
result: that means the run is incomplete, not that a file is unsuitable.
"""
import argparse
import collections
import glob
import json
import os
import sys

FORMAT_TERMINAL = ("OK", "SAME", "REFUSED", "ERROR", "TIMEOUT", "CRASH")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--list", required=True, help="the files the formatter was asked to format")
    p.add_argument("--format-logs", required=True, help="directory with worker-*.tsv")
    p.add_argument("--split", required=True, help="table written by split-check.py")
    p.add_argument("--compare-logs", required=True, help="directory with cmp-*.tsv")
    p.add_argument("--out-dir", required=True)
    p.add_argument("--keep", nargs="*", default=[], help="paths that are never taken")
    args = p.parse_args()
    keep = set(args.keep)

    listed = [l.strip() for l in open(args.list, encoding="utf-8") if l.strip()]

    fmt_status, commands, kept_raw, files_with_raw = {}, 0, 0, 0
    for log in sorted(glob.glob(os.path.join(args.format_logs, "worker-*.tsv"))):
        for line in open(log, encoding="utf-8", errors="replace"):
            q = line.rstrip("\n").split("\t")
            if len(q) >= 5 and q[0] in FORMAT_TERMINAL:
                fmt_status[q[4]] = (q[0], q[5] if len(q) > 5 else "")
                if q[0] in ("OK", "SAME"):
                    commands += int(q[2])
                    kept_raw += int(q[3])
                    files_with_raw += int(q[3]) > 0

    split = {}
    if os.path.exists(args.split):
        for line in open(args.split, encoding="utf-8"):
            q = line.rstrip("\n").split("\t")
            split[q[1]] = (q[0], q[2], int(q[3]), int(q[4]))

    cmp = {}
    for log in sorted(glob.glob(os.path.join(args.compare_logs, "cmp-*.tsv"))):
        for line in open(log, encoding="utf-8", errors="replace"):
            q = line.rstrip("\n").split("\t")
            if q[0] != "IMPORTED" and len(q) >= 2:
                cmp[q[1]] = (q[0], q[2] if len(q) > 2 else "")

    passed, excluded = [], []
    reasons = collections.Counter()
    incomplete = []
    semis = commas = 0
    for path in listed:
        if path not in fmt_status:
            incomplete.append(path + ": no formatter result")
            continue
        status, detail = fmt_status[path]
        if status == "SAME":
            continue
        if status != "OK":
            excluded.append((path, "formatter: " + status + " " + detail))
            reasons["formatter " + status] += 1
            continue
        if path in keep:
            excluded.append((path, "kept untouched on purpose"))
            reasons["kept untouched on purpose"] += 1
            continue
        s = split.get(path)
        c = cmp.get(path)
        if s is None or c is None:
            incomplete.append(path + ": no " + ("text check" if s is None else "syntax comparison") + " result")
            continue
        if s[0] == "OK" and c[0] == "SAME":
            passed.append(path)
            semis += s[2]
            commas += s[3]
            continue
        why = []
        if s[0] != "OK":
            why.append("text check: " + s[0] + " " + s[1])
            reasons["text check " + s[0]] += 1
        if c[0] != "SAME":
            why.append("syntax comparison: " + c[0] + " " + c[1])
            reasons["syntax comparison " + c[0]] += 1
        excluded.append((path, "; ".join(why)))

    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "pass.txt"), "w", encoding="utf-8") as f:
        f.write("".join(path + "\n" for path in passed))
    with open(os.path.join(args.out_dir, "excluded.tsv"), "w", encoding="utf-8") as f:
        for path, why in excluded:
            f.write(path + "\t" + why.replace("\t", " ") + "\n")

    statuses = collections.Counter(fmt_status[path][0] for path in listed if path in fmt_status)
    summary = {
        "files_listed": len(listed),
        "formatter_status": dict(statuses),
        "commands": commands,
        "commands_kept_as_written": kept_raw,
        "files_with_a_command_kept_as_written": files_with_raw,
        "taken": len(passed),
        "excluded": len(excluded),
        "excluded_reasons": dict(reasons),
        "dropped_semicolons": semis,
        "dropped_commas": commas,
        "incomplete": len(incomplete),
    }
    with open(os.path.join(args.out_dir, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
        f.write("\n")

    md = []
    md.append("| | Files |")
    md.append("|---|---:|")
    md.append("| Under `src/` in this run | %s |" % format(len(listed), ","))
    md.append("| Reformatted and passed both checks | %s |" % format(len(passed), ","))
    md.append("| Already formatted | %s |" % format(statuses.get("SAME", 0), ","))
    md.append("| Left as they were | %s |" % format(len(excluded), ","))
    md.append("")
    if reasons:
        md.append("Why files were left as they were (a file can fail both checks):")
        md.append("")
        for reason, n in sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0])):
            md.append("- %s: %s" % (reason, format(n, ",")))
        md.append("")
    md.append("The formatter kept %s of %s commands as written, in %s files. It replaced %s `;` and %s `,` "
              "separators by line breaks." % (format(kept_raw, ","), format(commands, ","),
                                               format(files_with_raw, ","), format(semis, ","), format(commas, ",")))
    with open(os.path.join(args.out_dir, "summary.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")
    print("\n".join(md))

    if incomplete:
        sys.stderr.write("\n".join(incomplete[:50]) + "\n")
        sys.exit("%d files have no result: the run is incomplete" % len(incomplete))


if __name__ == "__main__":
    main()
