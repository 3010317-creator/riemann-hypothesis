#!/usr/bin/env python3
"""Regression tests for import headers and restoring clumped modules."""

import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

import clump


class ClumpTests(unittest.TestCase):
    def test_trailing_import_comments_remain_in_header(self):
        for modifiers, public, exotic in [
            ("", False, False),
            ("public ", True, False),
            ("private ", False, False),
            ("meta ", False, True),
            ("public meta ", True, True),
        ]:
            for all_modifier in ["", "all "]:
                with self.subTest(modifiers=modifiers, all_modifier=all_modifier):
                    header = (f"module\n\n{modifiers}import {all_modifier}A.B -- unfold π\n"
                              "import Next\n\n")
                    body = "@[expose] public section\ntheorem sample : True := trivial\n"
                    mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", header + body)
                    self.assertEqual(mod.imports, [("A.B", public), ("Next", False)])
                    self.assertEqual(mod.exotic, exotic or bool(all_modifier))
                    self.assertEqual(mod.header, header)
                    self.assertEqual(mod.body, body)

    def test_standalone_import_comments_remain_in_header(self):
        for modifier, exotic in [("public ", False), ("meta ", True)]:
            with self.subTest(modifier=modifier):
                header = ("-- module comment\nmodule\n\n-- dependency π\n"
                          f"{modifier}import Core\n  -- another dependency\nimport Next\n\n")
                body = "@[expose] public section\ntheorem sample : True := trivial\n"
                mod = clump.Module("Lemmata.A", "src/Lemmata/A.lean", header + body)
                self.assertEqual(mod.imports, [("Core", modifier == "public "), ("Next", False)])
                self.assertEqual(mod.exotic, exotic)
                self.assertEqual(mod.header, header)
                self.assertEqual(mod.body, body)

    def test_commented_import_all_still_prevents_clumping(self):
        texts = {
            "Lemmata.A": "module\nimport all External -- unfold a definition\n\ndef a := 1\n",
            "Lemmata.Root": "module\npublic import Lemmata.A\n\ndef root := a\n",
        }
        mods = {n: clump.Module(n, "src/" + n.replace(".", "/") + ".lean", text)
                for n, text in texts.items()}
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(clump.plan(mods, 2000), {})

    def test_unclump_recreates_absorbed_directories_byte_for_byte(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            originals = {
                "src/Lemmata/Only/Leaf.lean":
                    "module\n-- external dependency\npublic import Core\n\n"
                    "@[expose] public section\n-- π\ntheorem leaf : True := trivial",
                "src/Lemmata/Root.lean":
                    "module\npublic import Lemmata.Only.Leaf\n\n"
                    "@[expose] public section\ntheorem root : True := leaf\n",
            }
            for path, text in originals.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(text.encode())
            subprocess.run(["git", "-C", str(root), "add", "src"], check=True)
            with contextlib.redirect_stderr(io.StringIO()):
                plan = clump.plan(clump.load(root), 2000)
            self.assertEqual(plan, {"Lemmata.Root": ["Lemmata.Only.Leaf", "Lemmata.Root"]})
            clump.apply(root, plan)
            combined = (root / "src/Lemmata/Root.lean").read_text()
            header, members = combined.split(clump.SEAM_BEGIN, 1)
            self.assertIn("public import Core\n", header)
            self.assertNotIn("\npublic import Core\n", members)
            self.assertTrue(clump.is_clump_file(
                clump.Module("Lemmata.Root", "src/Lemmata/Root.lean", combined)))
            # Git does not preserve the empty directory in a fresh checkout.
            (root / "src/Lemmata/Only").rmdir()
            with contextlib.redirect_stdout(io.StringIO()):
                clump.unclump(root)
            for path, text in originals.items():
                self.assertEqual((root / path).read_bytes(), text.encode())


if __name__ == "__main__":
    unittest.main()
