#!/usr/bin/env python3
"""Run ParseCompare.lean over a file list with several resumable workers.

LEAN is the `lean` binary of the toolchain the project is built with. The modules it imports are
found through LEAN_PATH, which is taken from the environment. LIST is split round-robin into
shards. Each worker is one long-lived Lean process that works through its shard in order and logs
one line per file.

If a process exits early, the first file without a log line was the one in flight: it is recorded
as CRASH and the worker restarts after it. A process that makes no progress for ten minutes is
killed, with the same effect. A process that exits without even finishing its import stops the
worker, so that a broken setup cannot mark every file as crashed.
"""
import argparse
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TERMINAL = {"SAME", "DIFF", "ORIG_ERROR", "FMT_ERROR", "IO_ERROR", "CRASH"}
STALL_SECONDS = 600
IMPORT_SECONDS = 2400  # importing Mathlib from a cold disk cache, several processes at once


def read_log(log):
    """Return (set of finished paths, number of completed imports)."""
    finished, imports = set(), 0
    if os.path.exists(log):
        for line in open(log, encoding="utf-8", errors="replace"):
            parts = line.rstrip("\n").split("\t")
            if parts[0] == "IMPORTED":
                imports += 1
            elif parts[0] in TERMINAL and len(parts) >= 2:
                finished.add(parts[1])
    return finished, imports


def work(args, shard, idx, env):
    log = os.path.join(args.run_dir, "cmp-%02d.tsv" % idx)
    err = os.path.join(args.run_dir, "cmp-%02d.err" % idx)
    todo = os.path.join(args.run_dir, "cmp-%02d.todo" % idx)
    while True:
        finished, imports_before = read_log(log)
        remaining = [f for f in shard if f not in finished]
        if not remaining:
            return
        with open(todo, "w", encoding="utf-8") as f:
            f.write("\n".join(remaining) + "\n")
        with open(err, "ab") as fe:
            proc = subprocess.Popen([args.lean, "--tstack=400000", "--run", args.script, todo, args.orig,
                                     args.fmt, log, args.prelude, args.module], stdout=fe, stderr=fe, env=env)
            last_size, last_change = -1, time.time()
            while proc.poll() is None:
                time.sleep(5)
                size = os.path.getsize(log) if os.path.exists(log) else 0
                if size != last_size:
                    last_size, last_change = size, time.time()
                    continue
                imported = read_log(log)[1] > imports_before
                if time.time() - last_change > (STALL_SECONDS if imported else IMPORT_SECONDS):
                    fe.write(b"supervisor: no progress, killing the process\n")
                    proc.kill()
                    proc.wait()
        finished, imports_after = read_log(log)
        remaining = [f for f in shard if f not in finished]
        if not remaining:
            return
        if imports_after == imports_before:
            with open(err, "ab") as fe:
                fe.write(b"supervisor: the process exited before finishing its import, giving up\n")
            return
        with open(log, "a", encoding="utf-8") as f:
            f.write("CRASH\t%s\tthe process exited or stalled while comparing this file\n" % remaining[0])


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--lean", required=True, help="lean binary of the project's toolchain")
    p.add_argument("--list", required=True, help="file with one path per line, relative to both roots")
    p.add_argument("--orig", required=True, help="root of the original files")
    p.add_argument("--fmt", required=True, help="root of the formatted files")
    p.add_argument("--run-dir", required=True, help="directory for the per-worker logs")
    p.add_argument("--workers", type=int, default=os.cpu_count() or 2)
    p.add_argument("--script", default=str(HERE / "ParseCompare.lean"))
    p.add_argument("--prelude", default=str(HERE / "ProjectSyntax.lean"))
    p.add_argument("--module", default="Mathlib", help="module imported once per worker")
    args = p.parse_args()

    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    env.pop("ELAN_TOOLCHAIN", None)

    os.makedirs(args.run_dir, exist_ok=True)
    files = [l.strip() for l in open(args.list, encoding="utf-8") if l.strip()]
    if not files:
        print("nothing to compare")
        return
    workers = max(1, min(args.workers, len(files)))
    shards = [files[i::workers] for i in range(workers)]

    threads = [threading.Thread(target=work, args=(args, shards[i], i, env)) for i in range(workers)]
    for t in threads:
        t.start()
        time.sleep(1)
    for t in threads:
        t.join()
    done = set()
    for i in range(workers):
        done |= read_log(os.path.join(args.run_dir, "cmp-%02d.tsv" % i))[0]
    print("compared %d of %d files" % (len(done & set(files)), len(files)))
    if not set(files) <= done:
        for i in range(workers):
            err = os.path.join(args.run_dir, "cmp-%02d.err" % i)
            if os.path.exists(err) and os.path.getsize(err):
                sys.stderr.write(open(err, encoding="utf-8", errors="replace").read()[-4000:])
        sys.exit("some files have no result")


if __name__ == "__main__":
    main()
