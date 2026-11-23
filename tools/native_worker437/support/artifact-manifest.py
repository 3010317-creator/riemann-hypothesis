from pathlib import Path
implementation = Path(__file__).with_name('artifact-manifest-fast-v1.py')
exec(compile(implementation.read_bytes(), str(implementation), 'exec'), globals(), globals())
