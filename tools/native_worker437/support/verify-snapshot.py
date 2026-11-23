#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,sys
root=Path.cwd()
expected=json.loads((root/'.snapshot.json').read_text())
assert expected['fingerprint']==sys.argv[1],'requested snapshot does not match snapshot file'
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert head==expected['git_commit'],'HEAD changed after snapshot freeze'
tree=subprocess.check_output(['git','rev-parse','HEAD:src'],text=True).strip()
assert tree==expected['source_tree'],'source tree changed after snapshot freeze'
for name,key in [('lakefile.toml','lakefile_sha256'),('lake-manifest.json','manifest_sha256')]:
 if key in expected:assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected[key],name+' changed'
assert (root/'lean-toolchain').read_text().strip()==expected['toolchain'],'toolchain changed'
dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=all','--','src','lakefile.toml','lake-manifest.json','lean-toolchain'],text=True)
assert not dirty,'source/config files changed after snapshot freeze: '+dirty[:1000]
print(json.dumps({'ok':True,'snapshot':expected['fingerprint'],'git_commit':head}))
