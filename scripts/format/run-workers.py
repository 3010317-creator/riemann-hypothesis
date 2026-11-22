#!/usr/bin/env python3
"""Run the batch formatter driver over a file list with several resumable workers.

LIST holds paths relative to SRC. It is split round-robin into shards, one per worker. Each worker
is one long-lived Lean process (it imports Mathlib once) that is restarted, skipping the files
already logged, whenever it exits early: on a per-file timeout the driver exits by itself, and on
a crash the file that was in flight is recorded as CRASH.

LEAN is the `lean` binary of the build that contains the formatter. The modules it imports are
found through LEAN_PATH, which is taken from the environment.

Everything is resumable: running the same command again continues from the logs in RUN_DIR.
"""
import argparse
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TERMINAL = {"OK", "SAME", "REFUSED", "ERROR", "TIMEOUT", "CRASH"}


def read_log(log):
    """Return (set of finished paths, path that was started last without finishing or None)."""
    finished, in_flight = set(), None
    if os.path.exists(log):
        for line in open(log, encoding="utf-8", errors="replace"):
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 5:
                continue
            if parts[0] == "START":
                in_flight = parts[4]
            elif parts[0] in TERMINAL:
                finished.add(parts[4])
                if in_flight == parts[4]:
                    in_flight = None
    return finished, in_flight


def work(args, shard, idx, env):
    log = os.path.join(args.run_dir, "worker-%02d.tsv" % idx)
    err = os.path.join(args.run_dir, "worker-%02d.err" % idx)
    todo = os.path.join(args.run_dir, "worker-%02d.todo" % idx)
    stalls = 0
    while True:
        finished, in_flight = read_log(log)
        if in_flight is not None:
            # The previous process died while this file was being formatted.
            with open(log, "a", encoding="utf-8") as f:
                f.write("CRASH\t0\t0\t0\t%s\tworker process exited while formatting this file\n" % in_flight)
            finished.add(in_flight)
        remaining = [f for f in shard if f not in finished]
        if not remaining:
            return
        with open(todo, "w", encoding="utf-8") as f:
            f.write("\n".join(remaining) + "\n")
        before = len(remaining)
        with open(err, "ab") as fe:
            subprocess.run([args.lean, "--tstack=400000", "--run", args.driver, todo, args.src, args.out,
                            log, str(args.timeout), args.prelude, args.module], stdout=fe, stderr=fe, env=env)
        finished_now, in_flight_now = read_log(log)
        after = len([f for f in shard if f not in finished_now])
        stalls = stalls + 1 if after >= before and in_flight_now is None else 0
        if stalls >= 3:
            with open(err, "ab") as fe:
                fe.write(b"supervisor: no progress in three consecutive runs, giving up\n")
            return


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--lean", required=True, help="lean binary of the build that contains the formatter")
    p.add_argument("--list", required=True, help="file with one path per line, relative to --src")
    p.add_argument("--src", required=True, help="root of the files to format")
    p.add_argument("--out", required=True, help="root under which changed files are written")
    p.add_argument("--run-dir", required=True, help="directory for the per-worker logs")
    p.add_argument("--workers", type=int, default=os.cpu_count() or 2)
    p.add_argument("--timeout", type=int, default=120, help="seconds allowed per file")
    p.add_argument("--driver", default=str(HERE / "BatchFmt.lean"))
    p.add_argument("--prelude", default=str(HERE / "ProjectSyntax.lean"))
    p.add_argument("--module", default="Mathlib", help="module imported once per worker")
    args = p.parse_args()

    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    env.pop("ELAN_TOOLCHAIN", None)

    os.makedirs(args.run_dir, exist_ok=True)
    os.makedirs(args.out, exist_ok=True)
    files = [l.strip() for l in open(args.list, encoding="utf-8") if l.strip()]
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
        done |= read_log(os.path.join(args.run_dir, "worker-%02d.tsv" % i))[0]
    print("formatter ran on %d of %d files" % (len(done & set(files)), len(files)))
    if not set(files) <= done:
        for i in range(workers):
            err = os.path.join(args.run_dir, "worker-%02d.err" % i)
            if os.path.exists(err) and os.path.getsize(err):
                sys.stderr.write(open(err, encoding="utf-8", errors="replace").read()[-4000:])
        sys.exit("some files have no result")


if __name__ == "__main__":
    main()
