"""Run with python3 scripts/tests/test_move_modules.py (needs git, not Lean)."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "move_modules.py"


def write(root, rel, text):
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class MoveModules(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        write(self.root, "src/Lib/Flat/Old.lean", "module\n\ntheorem Lib.Flat.Old.foo : True := trivial\n")
        write(self.root, "src/Lib/Flat/Older.lean", "module\n\ntheorem older : True := trivial\n")
        write(self.root, "src/Lib/User.lean", (
            "module\n\n"
            "public import Lib.Flat.Older\n"
            "import all Lib.Flat.Old\n"
            "-- ===== clump member: Lib.Flat.Old =====\n"
            '-- clump-header: {"m": "Lib.Flat.Old", "h": "module\\n\\npublic import Lib.Flat.Old\\n"}\n'
            "example : True := Lib.Flat.Old.foo\n"
            "/-- Uses `Lib.Flat.Old`. -/\n"
            "example : True := older\n"
        ))
        write(self.root, "scripts/clump-exclude.txt", "# modules\nLib.Flat.Old\nLib.Flat.Older\n")
        subprocess.run(["git", "-C", str(self.root), "add", "-A"], check=True)
        self.mapping = self.root.parent / (self.root.name + "-mapping.tsv")
        self.mapping.write_text("# old\tnew\nLib.Flat.Old\tLib.Flat.Topic.Old\n", encoding="utf-8")

    def tearDown(self):
        self.mapping.unlink(missing_ok=True)
        self.tmp.cleanup()

    def run_script(self, *extra):
        return subprocess.run([sys.executable, str(SCRIPT), str(self.root), str(self.mapping), *extra],
                              capture_output=True, text=True, check=True).stdout

    def test_move_and_rewrite(self):
        out = self.run_script()
        self.assertIn("moved 1 files", out)
        self.assertFalse((self.root / "src/Lib/Flat/Old.lean").exists())
        self.assertTrue((self.root / "src/Lib/Flat/Topic/Old.lean").exists())
        user = (self.root / "src/Lib/User.lean").read_text(encoding="utf-8")
        self.assertEqual(user, (
            "module\n\n"
            "public import Lib.Flat.Older\n"
            "import all Lib.Flat.Topic.Old\n"
            "-- ===== clump member: Lib.Flat.Topic.Old =====\n"
            '-- clump-header: {"m": "Lib.Flat.Topic.Old", "h": "module\\n\\npublic import Lib.Flat.Topic.Old\\n"}\n'
            "example : True := Lib.Flat.Old.foo\n"
            "/-- Uses `Lib.Flat.Topic.Old`. -/\n"
            "example : True := older\n"
        ))
        moved = (self.root / "src/Lib/Flat/Topic/Old.lean").read_text(encoding="utf-8")
        self.assertIn("theorem Lib.Flat.Old.foo", moved)
        exclude = (self.root / "scripts/clump-exclude.txt").read_text(encoding="utf-8")
        self.assertEqual(exclude, "# modules\nLib.Flat.Topic.Old\nLib.Flat.Older\n")
        staged = subprocess.run(["git", "-C", str(self.root), "status", "--porcelain"],
                                capture_output=True, text=True, check=True).stdout
        self.assertNotIn("??", staged)
        self.assertNotIn(" M ", staged)

    def test_keeps_crlf(self):
        write(self.root, "src/Lib/Crlf.lean", "")
        (self.root / "src/Lib/Crlf.lean").write_bytes(b"module\r\n\r\nimport Lib.Flat.Old\r\n")
        subprocess.run(["git", "-C", str(self.root), "add", "-A"], check=True)
        self.run_script()
        self.assertEqual((self.root / "src/Lib/Crlf.lean").read_bytes(), b"module\r\n\r\nimport Lib.Flat.Topic.Old\r\n")

    def test_rewrite_only(self):
        (self.root / "src/Lib/Flat/Old.lean").unlink()
        out = self.run_script("--rewrite-only")
        self.assertNotIn("moved", out)
        self.assertIn("import all Lib.Flat.Topic.Old\n", (self.root / "src/Lib/User.lean").read_text(encoding="utf-8"))

    def test_refuses_existing_target(self):
        write(self.root, "src/Lib/Flat/Topic/Old.lean", "module\n")
        r = subprocess.run([sys.executable, str(SCRIPT), str(self.root), str(self.mapping)],
                           capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("already exists", r.stderr)
        self.assertTrue((self.root / "src/Lib/Flat/Old.lean").exists())


if __name__ == "__main__":
    unittest.main()
