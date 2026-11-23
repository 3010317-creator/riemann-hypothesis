#!/usr/bin/env python3
"""Regression tests for the small-runner Lean import-header scanner.

Run from the repository root with:
    python3 -m unittest discover -s scripts -p 'test_quick_check_imports.py'

Load only the function under test so the CI runner and its dependencies are
never initialized by a unit test.
"""
import ast
from pathlib import Path
import re
import tempfile
import unittest


def load_import_scanner():
    path = Path(__file__).with_name('quick-check.py')
    module = ast.parse(path.read_text(encoding='utf-8'), filename=str(path))
    definitions = [node for node in module.body
                   if isinstance(node, ast.FunctionDef) and node.name == 'imports']
    if len(definitions) != 1:
        raise AssertionError('expected exactly one imports function')
    namespace = {'re': re}
    exec(compile(ast.Module(body=definitions, type_ignores=[]), str(path), 'exec'), namespace)
    return namespace['imports']


class ImportHeaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.imports = staticmethod(load_import_scanner())

    def scan(self, source):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'Input.lean'
            path.write_text(source, encoding='utf-8')
            return self.imports(path)

    def test_plain_imports_and_header_directives(self):
        self.assertEqual(self.scan('module\nprelude\nimport Mathlib\npublic import Foo.Bar\n'
                                   'meta import all Baz.Qux\ntheorem t : True := .intro\n'),
                         ['Mathlib', 'Foo.Bar', 'Baz.Qux'])

    def test_nested_comments_and_line_comments(self):
        source = ('/- outside /- nested -/ outside -/\n'
                  '-- import Unused\n'
                  'import First -- import Unused\n'
                  '/- across\n lines -/ public import Second.Third\n'
                  'def value := 1\n')
        self.assertEqual(self.scan(source), ['First', 'Second.Third'])

    def test_ignored_body_imports(self):
        self.assertEqual(self.scan('import Real\nnamespace N\nimport NotAHeader\n'), ['Real'])

    def test_malformed_body_is_not_header_checked(self):
        self.assertEqual(self.scan('import Real\ntheorem t : True := by trivial\n/- unclosed\n'), ['Real'])

    def test_unsupported_import_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'unsupported import header'):
            self.scan('import First\nimport Second Third\n')

    def test_unterminated_header_comment_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'unterminated header/source comment'):
            self.scan('module\nimport First\n/- incomplete')

    def test_no_imports_and_empty_file(self):
        self.assertEqual(self.scan(''), [])
        self.assertEqual(self.scan('example : True := .intro\nimport TooLate\n'), [])

    def test_four_megabyte_bound(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'Input.lean'
            with path.open('wb') as f:
                f.truncate(4 * 1024 ** 2 + 1)
            with self.assertRaisesRegex(ValueError, 'source/header exceeds quick-check limit'):
                self.imports(path)

    def test_crlf_and_blank_lines(self):
        self.assertEqual(self.scan('\r\nmodule\r\nimport One\r\n\r\nimport Two\r\ndef x := 0\r\n'),
                         ['One', 'Two'])


if __name__ == '__main__':
    unittest.main()
