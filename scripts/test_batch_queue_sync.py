#!/usr/bin/env python3
"""Batch assembly checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import importlib.util
import io
from pathlib import Path
import re
import unittest

SCRIPT = Path(__file__).with_name("batch-queue-sync.py")
spec = importlib.util.spec_from_file_location("batch_queue_sync", SCRIPT)
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)

REPO = "o/r"
NOW = datetime.datetime(2026, 11, 23, 4, 12, tzinfo=datetime.timezone.utc)
QUEUED, BUILDING = batch.QUEUED, batch.BUILDING


class Fake(batch.GitHub):
    """Just enough of the REST API. Commits are names; `inside` says what each one contains."""

    def __init__(self, dry_run=False):
        super().__init__(REPO, dry_run)
        self.pulls, self.refs, self.comments = {}, {}, {}
        self.inside = {"main0": set()}
        self.conflicting, self.allow_pulls, self.writes, self.after_merge = set(), True, [], None

    # Setting the scene.
    def add_pull(self, number, sha, labels=(), ref=None, own=False, base="main", state="open", merged=False):
        self.inside.setdefault(sha, set())
        self.pulls[number] = {
            "number": number, "state": state, "merged": merged, "labels": [{"name": name} for name in labels],
            "body": "", "title": "",
            "head": {"sha": sha, "ref": ref or f"topic-{number}", "repo": {"full_name": REPO if own else "fork/r"}},
            "base": {"ref": base}}

    def labels(self, number):
        return {label["name"] for label in self.pulls[number]["labels"]}

    # Answering requests.
    def call(self, method, path, payload=None):
        if method != "GET":
            self.writes.append((method, path, payload))
        for pattern, handler in self.routes:
            match = re.fullmatch(pattern, f"{method} {path}")
            if match:
                return handler(self, payload, *match.groups())
        raise AssertionError(f"unexpected request: {method} {path}")

    def _repo(self, _):
        return 200, {"default_branch": "main"}

    def _refs(self, _):
        return 200, [{"ref": f"refs/heads/{name}", "object": {"sha": sha}} for name, sha in sorted(self.refs.items())]

    def _main(self, _):
        return 200, {"object": {"sha": "main0"}}

    def _pulls_for(self, _, name):
        return 200, [pr for pr in self.pulls.values() if pr["head"]["ref"] == name and pr["head"]["repo"]["full_name"] == REPO]

    def _pull(self, _, number):
        return 200, self.pulls[int(number)]

    def _issues(self, _, label, state):
        label = label.replace("%20", " ")
        return 200, [{"number": number, "pull_request": {}} for number, pr in self.pulls.items()
                     if label in self.labels(number) and state in ("all", pr["state"])]

    def _compare(self, _, base, head):
        return 200, {"ahead_by": 0 if head == base or head in self.inside[base] else 1}

    def _comments(self, _, number):
        return 200, self.comments.get(int(number), [])

    def _new_ref(self, payload):
        self.refs[payload["ref"][len("refs/heads/"):]] = payload["sha"]
        return 201, {}

    def _merge(self, payload):
        base, head = self.refs[payload["base"]], payload["head"]
        if head in self.conflicting:
            return 409, {"message": "Merge conflict"}
        if head == base or head in self.inside[base]:
            return 204, None
        merged = f"merge-of-{head}-into-{base}"
        self.inside[merged] = self.inside[base] | self.inside[head] | {base, head}
        self.refs[payload["base"]] = merged
        for pr in self.pulls.values():
            if pr["head"]["ref"] == payload["base"]:
                pr["head"]["sha"] = merged
        if self.after_merge:
            self.after_merge()
        return 201, {"sha": merged}

    def _new_pull(self, payload):
        if not self.allow_pulls:
            return 403, {"message": "GitHub Actions is not permitted to create or approve pull requests."}
        number = max(self.pulls, default=0) + 100
        self.add_pull(number, self.refs[payload["head"]], ref=payload["head"], own=True)
        self.pulls[number].update(body=payload["body"], title=payload["title"])
        return 201, {"number": number}

    def _edit_pull(self, payload, number):
        self.pulls[int(number)].update(payload)
        return 200, {}

    def _add_label(self, payload, number):
        self.pulls[int(number)]["labels"] += [{"name": name} for name in payload["labels"] if name not in self.labels(int(number))]
        return 200, []

    def _drop_label(self, _, number, label):
        pr, label = self.pulls[int(number)], label.replace("%20", " ")
        if label not in self.labels(int(number)):
            return 404, {"message": "Label does not exist"}
        pr["labels"] = [item for item in pr["labels"] if item["name"] != label]
        return 200, []

    def _comment(self, payload, number):
        self.comments.setdefault(int(number), []).append({"body": payload["body"], "user": {"login": batch.BOT}})
        return 201, {}

    def _drop_ref(self, _, name):
        return (204, None) if self.refs.pop(name, None) else (422, {"message": "Reference does not exist"})

    routes = [
        (r"GET ", _repo),
        (r"GET git/matching-refs/heads/batch/", _refs),
        (r"GET git/ref/heads/main", _main),
        (r"GET pulls\?state=all&head=o:(.+)", _pulls_for),
        (r"GET pulls/(\d+)", _pull),
        (r"GET issues\?labels=([^&]+)&state=(\w+)&per_page=100&page=1", _issues),
        (r"GET compare/([^.]+)\.\.\.([^?]+)\?per_page=1", _compare),
        (r"GET issues/(\d+)/comments\?per_page=100&page=1", _comments),
        (r"POST git/refs", _new_ref),
        (r"POST merges", _merge),
        (r"POST pulls", _new_pull),
        (r"PATCH pulls/(\d+)", _edit_pull),
        (r"POST issues/(\d+)/labels", _add_label),
        (r"DELETE issues/(\d+)/labels/(.+)", _drop_label),
        (r"POST issues/(\d+)/comments", _comment),
        (r"DELETE git/refs/heads/(.+)", _drop_ref),
    ]


def queue(gh, *numbers):
    for number in numbers:
        gh.add_pull(number, f"head{number}", labels=[QUEUED])


class Assembling(unittest.TestCase):
    def test_first_batch_is_started_opened_and_lists_what_went_in(self):
        gh = Fake()
        queue(gh, 12, 11)
        log = batch.sync(gh, NOW)
        self.assertEqual(list(gh.refs), ["batch/2026-11-23-0412"])
        opened = gh.pulls[112]
        self.assertEqual((opened["title"], opened["head"]["ref"]), ("Batch 2026-11-23-0412", "batch/2026-11-23-0412"))
        self.assertIn("- #11 at `head11`\n- #12 at `head12`", opened["body"])
        self.assertTrue(opened["body"].startswith(batch.BODY))
        self.assertEqual(gh.inside[gh.refs["batch/2026-11-23-0412"]] & {"head11", "head12"}, {"head11", "head12"})
        # Being in a batch that is still open to additions does not change a label.
        self.assertEqual((gh.labels(11), gh.labels(12)), ({QUEUED}, {QUEUED}))
        self.assertIn("added #11 to `batch/2026-11-23-0412`", log)

    def test_running_again_changes_nothing_more(self):
        gh = Fake()
        queue(gh, 11, 12)
        batch.sync(gh, NOW)
        head, gh.writes = gh.refs["batch/2026-11-23-0412"], []
        batch.sync(gh, NOW)
        self.assertEqual(gh.refs, {"batch/2026-11-23-0412": head})
        self.assertEqual(gh.writes, [])

    def test_new_arrival_joins_the_batch_being_assembled(self):
        gh = Fake()
        queue(gh, 11)
        batch.sync(gh, NOW)
        queue(gh, 13)
        batch.sync(gh, NOW + datetime.timedelta(hours=1))
        self.assertEqual(list(gh.refs), ["batch/2026-11-23-0412"])
        self.assertIn("- #11 at `head11`\n- #13 at `head13`", gh.pulls[111]["body"])

    def test_pull_request_that_cannot_be_merged_is_left_out_and_told_once(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add("head12")
        log = batch.sync(gh, NOW)
        self.assertIn("- #11 at `head11`", gh.pulls[112]["body"])
        self.assertIn("Left out, because GitHub could not merge them into this branch: #12.", gh.pulls[112]["body"])
        self.assertEqual(len(gh.comments[12]), 1)
        self.assertIn("was not added to the batch `batch/2026-11-23-0412`", gh.comments[12][0]["body"])
        self.assertIn("could not merge it with what is already there", gh.comments[12][0]["body"])
        self.assertEqual(gh.labels(12), {QUEUED})
        self.assertTrue(any(line.startswith("left #12 out") for line in log))
        # The same commit is not tried, or commented on, a second time.
        gh.writes = []
        batch.sync(gh, NOW)
        self.assertEqual(len(gh.comments[12]), 1)
        self.assertNotIn("merges", [path for _, path, _ in gh.writes])
        self.assertIn("#12", gh.pulls[112]["body"])

    def test_new_commit_on_a_refused_pull_request_is_tried_again(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add("head12")
        batch.sync(gh, NOW)
        gh.add_pull(12, "head12b", labels=[QUEUED])
        batch.sync(gh, NOW)
        self.assertIn("- #12 at `head12b`", gh.pulls[112]["body"])

    def test_merged_in_by_hand_counts_without_another_merge(self):
        gh = Fake()
        queue(gh, 11)
        batch.sync(gh, NOW)
        queue(gh, 13)
        gh.inside[gh.refs["batch/2026-11-23-0412"]].add("head13")
        gh.writes = []
        batch.sync(gh, NOW)
        self.assertNotIn("merges", [path for _, path, _ in gh.writes])
        self.assertIn("- #13 at `head13`", gh.pulls[111]["body"])

    def test_other_bases_and_batch_pull_requests_are_not_queued(self):
        gh = Fake()
        gh.add_pull(11, "head11", labels=[QUEUED], base="release")
        gh.add_pull(12, "head12", labels=[QUEUED], ref="batch/old", own=True)
        gh.refs["batch/old"] = "head12"
        self.assertEqual(batch.sync(gh, NOW), ["nothing to do"])
        self.assertEqual(list(gh.refs), ["batch/old"])

    def test_refused_merge_reports_what_github_said(self):
        gh = Fake()
        queue(gh, 11)
        gh._merge = lambda payload: (403, {"message": "Resource not accessible by integration"})
        gh.routes = [(pattern, handler if pattern != "POST merges" else (lambda self, payload: self._merge(payload)))
                     for pattern, handler in Fake.routes]
        batch.sync(gh, NOW)
        self.assertIn("GitHub refused the merge (403: `Resource not accessible by integration`)", gh.comments[11][0]["body"])
        self.assertNotIn(111, gh.pulls)


class Freezing(unittest.TestCase):
    def frozen(self):
        gh = Fake()
        queue(gh, 11, 12)
        batch.sync(gh, NOW)
        gh.pulls[112]["labels"].append({"name": BUILDING})
        return gh

    def test_frozen_batch_hands_its_label_to_what_it_contains(self):
        gh = self.frozen()
        log = batch.sync(gh, NOW)
        self.assertEqual((gh.labels(11), gh.labels(12)), ({BUILDING}, {BUILDING}))
        self.assertIn("This batch is frozen at", gh.pulls[112]["body"])
        self.assertIn("- #11 at `head11`\n- #12 at `head12`", gh.pulls[112]["body"])
        self.assertIn("#11 is in the frozen batch #112: now `building`", log)
        # And it stays that way on later runs.
        batch.sync(gh, NOW)
        self.assertEqual((gh.labels(11), gh.labels(12)), ({BUILDING}, {BUILDING}))
        self.assertIn("- #11 at `head11`\n- #12 at `head12`", gh.pulls[112]["body"])

    def test_arrival_after_the_freeze_starts_a_new_batch(self):
        gh = self.frozen()
        batch.sync(gh, NOW)
        frozen_head = gh.refs["batch/2026-11-23-0412"]
        queue(gh, 13)
        batch.sync(gh, NOW + datetime.timedelta(hours=2))
        self.assertEqual(gh.refs["batch/2026-11-23-0412"], frozen_head)
        self.assertIn("batch/2026-11-23-0612", gh.refs)
        newest = gh.pulls[max(gh.pulls)]
        self.assertEqual(newest["head"]["ref"], "batch/2026-11-23-0612")
        self.assertIn("- #13 at `head13`", newest["body"])
        self.assertNotIn("#11", newest["body"])
        self.assertEqual(gh.labels(13), {QUEUED})

    def test_freeze_during_a_run_stops_further_merges(self):
        gh = Fake()
        queue(gh, 11)
        batch.sync(gh, NOW)
        queue(gh, 12, 13)
        gh.after_merge = lambda: gh.pulls[111]["labels"].append({"name": BUILDING})
        log = batch.sync(gh, NOW)
        self.assertIn("head12", gh.inside[gh.refs["batch/2026-11-23-0412"]])
        self.assertNotIn("head13", gh.inside[gh.refs["batch/2026-11-23-0412"]])
        self.assertIn("batch #111 was frozen during this run: stopped adding to it", log)


class OpeningThePullRequest(unittest.TestCase):
    def test_when_workflows_may_not_open_pull_requests_the_branch_waits_for_a_person(self):
        gh = Fake()
        gh.allow_pulls = False
        queue(gh, 11)
        with self.assertRaises(batch.Refused) as caught:
            batch.sync(gh, NOW)
        self.assertIn("https://github.com/o/r/compare/main...batch/2026-11-23-0412?expand=1", str(caught.exception))
        self.assertIn("not permitted to create", str(caught.exception))
        self.assertIn("head11", gh.inside[gh.refs["batch/2026-11-23-0412"]])
        # A maintainer opens it by hand; the next run adopts it instead of starting another branch.
        gh.add_pull(50, gh.refs["batch/2026-11-23-0412"], ref="batch/2026-11-23-0412", own=True)
        queue(gh, 12)
        batch.sync(gh, NOW + datetime.timedelta(hours=1))
        self.assertEqual(list(gh.refs), ["batch/2026-11-23-0412"])
        self.assertIn("- #11 at `head11`\n- #12 at `head12`", gh.pulls[50]["body"])


class Landing(unittest.TestCase):
    def test_merged_batch_clears_building_and_removes_its_branch(self):
        gh = Fake()
        queue(gh, 11, 12)
        batch.sync(gh, NOW)
        gh.pulls[112]["labels"].append({"name": BUILDING})
        batch.sync(gh, NOW)
        gh.add_pull(14, "head14", labels=[BUILDING])  # building in some other batch
        gh.pulls[11].update(state="closed", merged=True)
        gh.pulls[112].update(state="closed", merged=True)
        log = batch.landed(gh, 112)
        self.assertEqual((gh.labels(11), gh.labels(12), gh.labels(112)), (set(), set(), set()))
        self.assertEqual(gh.labels(14), {BUILDING})
        self.assertEqual(gh.refs, {})
        self.assertIn("#11 landed with batch #112: `building` removed", log)

    def test_only_a_merged_batch_counts(self):
        gh = Fake()
        gh.add_pull(11, "head11", labels=[BUILDING], state="closed", merged=True)
        gh.add_pull(12, "head12", ref="batch/x", own=True, state="closed", merged=False)
        for number in (11, 12):
            gh.writes = []
            self.assertEqual(batch.landed(gh, number), [f"#{number} is not a merged batch: nothing to do"])
            self.assertEqual(gh.writes, [])


class DryRun(unittest.TestCase):
    def test_reads_but_sends_no_change(self):
        gh = Fake(dry_run=True)
        queue(gh, 11, 12)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            log = batch.sync(gh, NOW)
        self.assertEqual((gh.writes, gh.refs, gh.comments), ([], {}, {}))
        self.assertIn("would add #11 to `batch/2026-11-23-0412`", log)
        self.assertIn('would POST merges {"base": "batch/2026-11-23-0412", "head": "head11"', printed.getvalue())


if __name__ == "__main__":
    unittest.main()
