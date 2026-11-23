#!/usr/bin/env python3
"""Assemble queued pull requests into a batch pull request and keep the labels in step.

The batch-queue workflow runs this from its trusted checkout. Everything goes through GitHub's
API: GitHub performs the merges, and nothing from a pull request is checked out or run here.

A batch is a branch `batch/...` in this repository, normally with an open pull request.

- Without the `building` label it is being assembled. Each pull request labelled `batch queue`
  is merged into it, and one that GitHub cannot merge is told so in a comment.
- With the `building` label it is frozen. Nothing more is merged in, and the pull requests it
  contains swap `batch queue` for `building`. Later arrivals start a new batch.
- Once it is merged, the pull requests it contained lose `building`.

No state is stored. Which pull requests a batch contains is read from its commits each time,
so a run can be repeated or skipped, and a maintainer can merge something into a batch by hand.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys

QUEUED, BUILDING = "batch queue", "building"
PREFIX = "batch/"
# Marks the pull request text this script writes, and the comment left on a pull request that
# could not be added. The comment names the batch and commit so the attempt is not repeated.
BODY = "<!-- batch-queue -->"
REFUSAL = "<!-- batch-queue-refused {branch} {sha} -->"
BOT = "github-actions[bot]"


class Refused(Exception):
    """GitHub would not do something this script cannot work around."""


class GitHub:
    """The repository's REST API through `gh`. With `dry_run`, writes are printed, not sent."""

    def __init__(self, repo, dry_run=False):
        self.repo, self.dry_run = repo, dry_run

    def call(self, method, path, payload=None):
        """One request. Returns (HTTP status, decoded body or None)."""
        args = ["gh", "api", "--include", "--method", method, f"repos/{self.repo}/{path}".rstrip("/")]
        data = None
        if payload is not None:
            args += ["--input", "-"]
            data = json.dumps(payload).encode()
        done = subprocess.run(args, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        head, _, body = done.stdout.decode("utf-8", "replace").replace("\r\n", "\n").partition("\n\n")
        try:
            status = int(head.split()[1])
        except (IndexError, ValueError):
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"no answer from GitHub for {method} {path}") from None
        return status, (json.loads(body) if body.strip() else None)

    def get(self, path):
        status, data = self.call("GET", path)
        if status != 200:
            raise RuntimeError(f"GET {path} answered {status}")
        return data

    def pages(self, path):
        """Every item of a paginated list."""
        items, page = [], 1
        while True:
            batch = self.get(f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
            items += batch
            if len(batch) < 100:
                return items
            page += 1

    def write(self, method, path, payload=None):
        if self.dry_run:
            print(f"would {method} {path} {json.dumps(payload) if payload else ''}".rstrip())
            return 0, None
        return self.call(method, path, payload)


def quoted(label):
    return label.replace(" ", "%20")


def pull(gh, number):
    info = gh.get(f"pulls/{number}")
    head = info["head"]
    return {"number": info["number"], "sha": head["sha"], "ref": head["ref"],
            "own": (head.get("repo") or {}).get("full_name") == gh.repo, "base": info["base"]["ref"],
            "labels": {label["name"] for label in info["labels"]},
            "open": info["state"] == "open", "merged": bool(info.get("merged"))}


def is_batch(pr):
    return pr["own"] and pr["ref"].startswith(PREFIX)


def labelled(gh, label, state="open"):
    """Pull requests carrying a label, lowest number first."""
    items = gh.pages(f"issues?labels={quoted(label)}&state={state}")
    return sorted(item["number"] for item in items if "pull_request" in item)


def contains(gh, batch_sha, sha):
    """Whether every commit of `sha` is already in the batch."""
    return gh.get(f"compare/{batch_sha}...{sha}?per_page=1")["ahead_by"] == 0


def relabel(gh, number, add=None, remove=None):
    if add:
        gh.write("POST", f"issues/{number}/labels", {"labels": [add]})
    if remove:
        gh.write("DELETE", f"issues/{number}/labels/{quoted(remove)}")


def open_batches(gh):
    """Batch branches that have not landed, as {ref, sha, number, frozen}. `number` is None for a
    branch whose pull request has not been opened yet."""
    found = []
    for ref in gh.get(f"git/matching-refs/heads/{PREFIX}"):
        name = ref["ref"][len("refs/heads/"):]
        owner = gh.repo.split("/")[0]
        pulls = gh.get(f"pulls?state=all&head={owner}:{name}")
        live = [item for item in pulls if item["state"] == "open"]
        if pulls and not live:
            continue  # merged or closed: finished with
        number = live[0]["number"] if live else None
        frozen = bool(live) and BUILDING in {label["name"] for label in live[0]["labels"]}
        found.append({"ref": name, "sha": ref["object"]["sha"], "number": number, "frozen": frozen,
                      "body": live[0]["body"] if live else None})
    return found


def refused_before(gh, number, branch, sha):
    marker = REFUSAL.format(branch=branch, sha=sha)
    return any(marker in (item.get("body") or "") for item in gh.pages(f"issues/{number}/comments"))


def refuse(gh, pr, batch, reason):
    """Tell the pull request why it was left out, once for this commit and this batch."""
    link = f"#{batch['number']}" if batch["number"] else f"`{batch['ref']}`"
    text = (f"{REFUSAL.format(branch=batch['ref'], sha=pr['sha'])}\n"
            f"This pull request was not added to the batch {link}: {reason}\n\n"
            f"It keeps its `{QUEUED}` label. It is tried again when it gets a new commit, "
            "or when the next batch starts.\n")
    gh.write("POST", f"issues/{pr['number']}/comments", {"body": text})


def describe(batch, members, refused):
    """The text of a batch pull request."""
    lines = [BODY, "The batch-queue workflow assembles this pull request. Commenting `batch` on a "
             "pull request merges it in here."]
    if batch["frozen"]:
        lines.append(f"\nThis batch is frozen at `{batch['sha'][:10]}`. Nothing more is added to it, "
                     "and later `batch` comments start a new batch.")
    else:
        lines.append("\nCommenting `freeze` here, or starting a build of this pull request, freezes it: "
                     f"nothing more is added, and what it contains is relabelled `{BUILDING}`.")
    lines += ["", "In this batch:", ""]
    lines += [f"- #{pr['number']} at `{pr['sha'][:10]}`" for pr in members] or ["- nothing yet"]
    if refused:
        lines += ["", "Left out, because GitHub could not merge them into this branch: "
                  + ", ".join(f"#{pr['number']}" for pr in refused) + "."]
    lines += ["", "Merge this with a merge commit, not a squash, so that GitHub marks the pull "
              "requests above as merged."]
    return "\n".join(lines) + "\n"


def publish(gh, batch, members, refused, main):
    """Open the batch's pull request if it has none, and bring its text up to date."""
    text = describe(batch, members, refused)
    if batch["number"]:
        if text != batch.get("body"):
            gh.write("PATCH", f"pulls/{batch['number']}", {"body": text})
        return
    title = "Batch " + batch["ref"][len(PREFIX):]
    status, data = gh.write("POST", "pulls", {"title": title, "head": batch["ref"], "base": main, "body": text})
    if status == 201:
        batch["number"] = data["number"]
    elif status:
        raise Refused(
            f"GitHub would not let this workflow open a pull request for `{batch['ref']}` "
            f"({status}: {(data or {}).get('message', 'no reason given')}). The branch is ready. Open the pull "
            f"request by hand at https://github.com/{gh.repo}/compare/{main}...{batch['ref']}?expand=1 and it "
            "will be picked up, or allow GitHub Actions to create pull requests in the repository settings.")


def sync(gh, now=None):
    """Bring batches and labels up to date. Returns lines saying what was done."""
    log = []
    main = gh.get("")["default_branch"]
    batches = open_batches(gh)
    queued = [pull(gh, number) for number in labelled(gh, QUEUED)]
    queued = [pr for pr in queued if not is_batch(pr) and pr["base"] == main]
    building = [pull(gh, number) for number in labelled(gh, BUILDING)]
    building = [pr for pr in building if not is_batch(pr)]

    # A frozen batch hands `building` to what it contains.
    for batch in (item for item in batches if item["frozen"]):
        inside = [pr for pr in queued if contains(gh, batch["sha"], pr["sha"])]
        for pr in inside:
            relabel(gh, pr["number"], add=BUILDING, remove=QUEUED)
            log.append(f"#{pr['number']} is in the frozen batch #{batch['number']}: now `{BUILDING}`")
        queued = [pr for pr in queued if pr not in inside]
        members = [pr for pr in building if contains(gh, batch["sha"], pr["sha"])] + inside
        publish(gh, batch, sorted(members, key=lambda pr: pr["number"]), [], main)

    # The batch being assembled takes everything still waiting.
    assembling = sorted((item for item in batches if not item["frozen"]), key=lambda item: item["ref"])
    batch = assembling[-1] if assembling else None
    members, refused, before = [], [], len(log)
    for pr in queued:
        if batch is None:
            stamp = (now or datetime.datetime.now(datetime.timezone.utc)).strftime("%Y-%m-%d-%H%M")
            batch = {"ref": PREFIX + stamp, "sha": gh.get(f"git/ref/heads/{main}")["object"]["sha"],
                     "number": None, "frozen": False}
            gh.write("POST", "git/refs", {"ref": f"refs/heads/{batch['ref']}", "sha": batch["sha"]})
            log.append(f"started `{batch['ref']}` from `{main}`")
        if contains(gh, batch["sha"], pr["sha"]):
            members.append(pr)
            continue
        if refused_before(gh, pr["number"], batch["ref"], pr["sha"]):
            refused.append(pr)
            continue
        # Look again before every merge: the batch may have been frozen a moment ago.
        if batch["number"] and BUILDING in pull(gh, batch["number"])["labels"]:
            log.append(f"batch #{batch['number']} was frozen during this run: stopped adding to it")
            break
        message = f"Add #{pr['number']} to the batch\n\nMerged at {pr['sha']}."
        status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": pr["sha"], "commit_message": message})
        if status == 201:
            batch["sha"] = data["sha"]
        if status in (0, 201, 204):
            members.append(pr)
            log.append(f"{'would add' if gh.dry_run else 'added'} #{pr['number']} to `{batch['ref']}`")
            continue
        reason = ("GitHub could not merge it with what is already there." if status == 409 else
                  f"GitHub refused the merge ({status}: `{(data or {}).get('message', 'no reason given')}`).")
        refuse(gh, pr, batch, reason)
        refused.append(pr)
        log.append(f"left #{pr['number']} out of `{batch['ref']}`: {reason}")
    if batch and (members or batch["number"]):
        publish(gh, batch, members, refused, main)
        if len(log) > before:
            log.append(f"batch pull request #{batch['number']} lists {len(members)} pull request(s)"
                       if batch["number"] else f"`{batch['ref']}` has no pull request yet")
    return log or ["nothing to do"]


def landed(gh, number):
    """A batch was merged: take `building` off what it contained and remove its branch."""
    batch = pull(gh, number)
    if not (is_batch(batch) and batch["merged"]):
        return [f"#{number} is not a merged batch: nothing to do"]
    log = []
    for other in labelled(gh, BUILDING, state="all"):
        if other != number and contains(gh, batch["sha"], pull(gh, other)["sha"]):
            relabel(gh, other, remove=BUILDING)
            log.append(f"#{other} landed with batch #{number}: `{BUILDING}` removed")
    relabel(gh, number, remove=BUILDING)
    gh.write("DELETE", f"git/refs/heads/{batch['ref']}")
    return log + [f"removed the branch `{batch['ref']}`"]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--landed", type=int, help="a batch pull request that was just merged")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        log = landed(gh, args.landed) if args.landed else sync(gh)
    except Refused as error:
        log, failure = [str(error)], 1
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
