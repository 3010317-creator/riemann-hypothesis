"""Run with LEAN=/path/to/lean python3 scripts/tests/test_collapse_wrappers_scaffolding.py."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "collapse_wrappers.py"


def wrapper(name, scaffolding=""):
    return (
        "module\npublic import Core\n@[expose] public section\n"
        f"{scaffolding}theorem N.{name} : True := original\n"
    )


def clump_user(wrapper_module, body):
    """A caller laid out the way scripts/clump.py writes a clump, header comments included."""
    return (
        f"module\nimport {wrapper_module}\n\n"
        "-- This file was produced by scripts/clump.py from the modules listed below.\n"
        "-- Members: A, B\n"
        "-- ===== clump member: A =====\n"
        f'-- clump-header: {{"m": "A", "h": "module\\n\\nimport {wrapper_module}\\n"}}\n'
        f"{body}"
        "-- ===== end clump member: A =====\n"
        "-- ===== clump member: B =====\n"
        '-- clump-header: {"m": "B", "h": "module\\n"}\n'
        "example : True := trivial\n"
        "-- ===== end clump member: B =====\n"
    )


class WrapperScaffolding(unittest.TestCase):
    def test_scaffolding_clumps_and_callers(self):
        sources = {
            "Core": (
                "module\n@[expose] public section\n"
                "theorem original : True := by trivial\n"
                "theorem pairOriginal : True ∧ True := ⟨trivial, trivial⟩\n"
                "def localInst : Inhabited Nat := ⟨0⟩\n"
                "instance globalInst : Inhabited Unit := ⟨()⟩\n"
            ),
            "Extra": "module\n@[expose] public section\ntheorem extra : True := trivial\n",
            "Local": wrapper("localProof", "attribute [local instance] localInst\n"),
            "LocalUser": "module\nimport Local\nexample : True := N.localProof\n",
            "Priority": wrapper("priorityProof", "attribute [local instance 100] localInst\n"),
            "PriorityUser": "module\nimport Priority\nexample : True := N.priorityProof\n",
            # Erasing an instance is not a local instance; such wrappers stay.
            "Erased": wrapper("erasedProof", "attribute [-instance] globalInst\n"),
            "ErasedUser": "module\nimport Erased\nexample : True := N.erasedProof\n",
            "Clumped": wrapper("clumpedProof"),
            "ClumpedUser": clump_user("Clumped", "example : True := N.clumpedProof\n"),
            # A real string literal in a clump still keeps the wrapper.
            "Quoted": wrapper("quotedProof"),
            "QuotedUser": clump_user(
                "Quoted",
                'def label : String := "N.quotedProof"\nexample : True := N.quotedProof\n',
            ),
            # Only direct importers are rewritten, so a name used further down keeps the wrapper.
            "Indirect": wrapper("indirectProof"),
            "IndirectMid": "module\npublic import Indirect\n",
            "IndirectUser": "module\nimport IndirectMid\nexample : True := N.indirectProof\n",
            # `N.left` is field notation on the wrapper, which the rewrite does not replace.
            "Field": (
                "module\npublic import Core\n@[expose] public section\n"
                "theorem N.fieldProof : True ∧ True := pairOriginal\n"
            ),
            "FieldUser": "module\nimport Field\nexample : True := N.fieldProof.left\n",
            # The rewritten header keeps a private import ahead of the public ones.
            "Ordered": wrapper("orderedProof"),
            "OrderedUser": "module\nimport Extra\npublic import Ordered\nexample : True := N.orderedProof\n",
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            src.mkdir()
            for name, text in sources.items():
                (src / f"{name}.lean").write_text(text, encoding="utf-8")
            subprocess.run(["git", "init", "-q", directory], check=True)
            subprocess.run(["git", "-C", directory, "add", "src"], check=True)

            def compile_sources():
                # Remove old artifacts so a deleted wrapper cannot mask a broken caller.
                for artifact in src.glob("*.olean*"):
                    artifact.unlink()
                for name in sources:
                    if (src / f"{name}.lean").exists():
                        subprocess.run(
                            [os.environ["LEAN"], "-o", f"{name}.olean", f"{name}.lean"],
                            cwd=src, env={**os.environ, "LEAN_PATH": str(src)}, check=True,
                        )

            if os.environ.get("LEAN"):
                compile_sources()
            subprocess.run([sys.executable, str(SCRIPT), directory], check=True)
            if os.environ.get("LEAN"):
                compile_sources()
            for name in ("Local", "Priority", "Clumped", "Ordered"):
                self.assertFalse((src / f"{name}.lean").exists(), name)
                self.assertIn("_root_.original", (src / f"{name}User.lean").read_text(encoding="utf-8"))
            self.assertTrue((src / "OrderedUser.lean").read_text(encoding="utf-8").startswith(
                "module\n\nimport Extra\npublic import Core\n"))
            for name in ("Erased", "Quoted", "Indirect", "Field"):
                self.assertTrue((src / f"{name}.lean").exists(), name)
                self.assertEqual((src / f"{name}User.lean").read_text(encoding="utf-8"), sources[name + "User"])
            self.assertEqual((src / "IndirectMid.lean").read_text(encoding="utf-8"), sources["IndirectMid"])
            self.assertIn("import Core", (src / "ClumpedUser.lean").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
