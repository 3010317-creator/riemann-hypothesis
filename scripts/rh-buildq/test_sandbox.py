#!/usr/bin/env python3
"""Tests of the fragment sandbox with a hostile lakefile. Needs bwrap and an installed toolchain.

  python3 scripts/rh-buildq/test_sandbox.py [-v]

RH_TEST_TOOLCHAIN may name a toolchain directory; by default the newest one under ~/.elan.
The hostile lakefile tries, while Lake elaborates it, to write into $HOME, read ~/.ssh, read
the runner's files outside the work tree and open network connections. Every attempt must
fail in the offline sandbox, and all but the network one in the network sandbox, while a
normal `lake build` of the same project succeeds. The stage step must not follow links that
code in the sandbox planted in the work tree.
"""
import importlib.util, json, os, shutil, subprocess, sys, tempfile, unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sandbox = load("rh_buildq_sandbox", "sandbox.py")
fragment = load("rh_buildq_fragment", "fragment.py")


def toolchain():
    if os.environ.get("RH_TEST_TOOLCHAIN"):
        return Path(os.environ["RH_TEST_TOOLCHAIN"])
    root = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains"
    found = sorted(p for p in root.glob("leanprover--lean4---v4.*") if (p / "bin/lake").exists())
    return found[-1] if found else None


TOOLCHAIN = toolchain()
HOME = Path.home()
SSH = next((p for p in sorted((HOME / ".ssh").glob("*.pub"))), HOME / ".ssh/known_hosts")
CANARY = HOME / "rh-sandbox-test-canary"

HOSTILE = r'''import Lake
open Lake DSL System

def attempt (name : String) (act : IO Unit) : IO Unit := do
  let out : System.FilePath := "attempts.txt"
  let prev ← if (← out.pathExists) then IO.FS.readFile out else pure ""
  let line ← try
      act
      pure s!"{name}: SUCCEEDED"
    catch e =>
      pure s!"{name}: blocked ({(toString e).replace "\n" " "})"
  IO.FS.writeFile out (prev ++ line ++ "\n")

def curl (url : String) : IO Unit := do
  let r ← IO.Process.output { cmd := "curl", args := #["-sS", "-o", "/dev/null", "--max-time", "8", url] }
  if r.exitCode != 0 then throw <| IO.userError r.stderr

#eval show IO Unit from do
  attempt "write-home" (IO.FS.writeFile "CANARY" "pwned")
  attempt "read-ssh" (discard <| IO.FS.readBinFile "SSH")
  attempt "list-ssh" (discard <| System.FilePath.readDir (System.FilePath.mk "SSHDIR"))
  attempt "read-runner-file" (discard <| IO.FS.readFile "RUNNERFILE")
  attempt "write-usr" (IO.FS.writeFile "/usr/rh-sandbox-test" "pwned")
  attempt "network-https" (curl "https://github.com")
  attempt "network-raw-ip" (curl "http://1.1.1.1")

package hostile

@[default_target] lean_lib Hello
'''


@unittest.skipUnless(shutil.which("bwrap") and TOOLCHAIN, "needs bwrap and a Lean toolchain")
class HostileLakefile(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="rh-sandbox-test-", dir=HOME))  # under $HOME on purpose
        self.work = self.tmp / "project"
        self.work.mkdir()
        (self.work / "Hello.lean").write_text("def hello : String := \"hello\"\n#eval hello\n")
        text = (HOSTILE.replace("CANARY", str(CANARY)).replace("SSHDIR", str(SSH.parent)).replace("SSH", str(SSH))
                .replace("RUNNERFILE", str(Path(__file__).resolve())))
        (self.work / "lakefile.lean").write_text(text)
        CANARY.unlink(missing_ok=True)

    def tearDown(self):
        CANARY.unlink(missing_ok=True)
        shutil.rmtree(self.tmp, ignore_errors=True)

    def lake(self, *args, net=False):
        cmd = sandbox.command(self.work, TOOLCHAIN, net=net, env={"LAKE_CACHE_DIR": str(self.work / ".lake/cache")})
        return subprocess.run(cmd + ["lake", *args], env=sandbox.host_env(), capture_output=True, text=True)

    def attempts(self):
        lines = (self.work / "attempts.txt").read_text().splitlines()
        return {l.split(":", 1)[0]: l.split(":", 1)[1].strip() for l in lines}

    def check(self, net):
        r = self.lake("build", "-v", "-o", str(self.work / ".lake/outputs.jsonl"), net=net)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)  # the normal build succeeds
        got = self.attempts()
        for name in ("write-home", "read-ssh", "list-ssh", "read-runner-file", "write-usr"):
            self.assertTrue(got[name].startswith("blocked"), f"{name}: {got[name]}")
        self.assertFalse(CANARY.exists())
        self.assertTrue((self.work / ".lake/build/lib/lean/Hello.olean").exists())
        return got

    def test_offline_build_blocks_everything(self):
        got = self.check(net=False)
        for name in ("network-https", "network-raw-ip"):
            self.assertTrue(got[name].startswith("blocked"), f"{name}: {got[name]}")

    def test_network_sandbox_keeps_filesystem_restrictions(self):
        got = self.check(net=True)
        if os.environ.get("RH_TEST_EXPECT_NETWORK"):
            self.assertEqual(got["network-https"], "SUCCEEDED")

    def test_probe(self):
        sandbox.probe(self.tmp / "probe", TOOLCHAIN)

    def test_stage_does_not_follow_planted_links(self):
        # Code in the sandbox can leave links to host files in the tree; the host-side stage
        # step must not copy what they point to.
        q = self.tmp / "queue"
        q.mkdir()
        os.rename(self.work, q / "project")
        p = q / "project"
        (q / "job.env").write_text(f"TARGET={'0' * 40}\nTOOLCHAIN_DIR=x\nTOOLCHAIN={TOOLCHAIN}\n")
        lib, ir = p / ".lake/build/lib/lean", p / ".lake/build/ir"
        for d in (lib / "Evil", ir / "Evil", lib / "Ok", ir / "Ok"):
            d.mkdir(parents=True)
        (lib / "Evil/Key.trace").write_text(json.dumps({"depHash": "1" * 16}))
        os.symlink(SSH, ir / "Evil/Key.ltar")
        (lib / "Evil/Dir.trace").write_text(json.dumps({"depHash": "2" * 16}))
        os.symlink(SSH.parent, ir / "Evil/Sub")
        (lib / "Evil/Sub").mkdir()
        (lib / "Evil/Sub/X.trace").write_text(json.dumps({"depHash": "3" * 16}))
        os.symlink(SSH.parent, lib / "Linked")  # a whole linked subtree of traces
        os.mkfifo(lib / "Evil/Fifo.trace")
        (ir / "Ok/Fine.ltar").write_bytes(b"artifact")
        (lib / "Ok/Fine.trace").write_text(json.dumps({"depHash": "4" * 16}))
        out = self.tmp / "stage"
        fragment.cmd_stage(type("A", (), {"queue": str(q), "out": str(out), "timings": None})())
        names = {m[0] for m in json.loads((out / "manifest.json").read_text())["modules"]}
        self.assertIn("Ok.Fine", names)
        self.assertFalse({n for n in names if n.startswith(("Evil", "Linked"))}, names)
        for f in (out / "artifacts").iterdir():
            self.assertFalse(f.is_symlink())
            self.assertNotEqual(f.read_bytes(), SSH.read_bytes())


if __name__ == "__main__":
    unittest.main()
