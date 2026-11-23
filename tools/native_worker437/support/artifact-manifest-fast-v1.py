#!/usr/bin/env python3
from pathlib import Path,PurePosixPath
import hashlib,json,sys,os

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def atomic(p,data):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(data);t.replace(p)

# Requested modules are complete before create; cache each directory enumeration once.
_SUFFIXES = ('.bc', '.bc.hash', '.c', '.c.hash', '.c.o', '.c.o.hash',
             '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.ir.sig.hash',
             '.ir.trace', '.ltar', '.ltar.hash', '.olean', '.olean.hash',
             '.olean.private', '.olean.private.hash', '.olean.server',
             '.olean.server.hash', '.trace')
def module_files(directory, basename):
 return sorted(p for suffix in _SUFFIXES
               if (p := directory/(basename+suffix)).is_file() and not p.is_symlink())
mode=sys.argv[1];root=Path(sys.argv[2]).resolve();snapshot=sys.argv[3]
if mode=='create':
 result=json.loads(Path(sys.argv[4]).read_text());out=Path(sys.argv[5])
 modules=[x['module'] for x in result.get('modules',[]) if x.get('ok')]
 rows=[]
 for m in modules:
  stem=Path(*m.split('.'))
  for part in ['lib/lean','ir']:
   d=root/'.lake/build'/part/stem.parent
   for p in module_files(d,stem.name):
    if p.name.endswith('.setup.json'):continue
    if p.is_file() and not p.is_symlink():
     rows.append({'module':m,'path':p.relative_to(root).as_posix(),'bytes':p.stat().st_size,'sha256':digest(p)})
 data={'schema':1,'snapshot':snapshot,'modules':modules,'files':rows}
 atomic(out,json.dumps(data,separators=(',',':'))+'\n')
 print(json.dumps({'manifest':str(out),'sha256':digest(out),'files':len(rows),'modules':len(modules),'bytes':sum(x['bytes'] for x in rows)}))
elif mode=='verify':
 count=0;size=0
 for name in sys.argv[4:]:
  d=json.loads(Path(name).read_text());assert d['schema']==1 and d['snapshot']==snapshot,'artifact snapshot mismatch'
  for row in d['files']:
   rel=PurePosixPath(row['path']);assert not rel.is_absolute() and '..' not in rel.parts and rel.parts[:2]==('.lake','build'),'unsafe artifact path'
   p=root/Path(rel);assert not p.is_symlink() and p.resolve().is_relative_to(root),'artifact escaped root'
   assert p.is_file() and p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'artifact integrity failure '+str(p)
   count+=1;size+=row['bytes']
 print(json.dumps({'ok':True,'files':count,'bytes':size}))
else:raise SystemExit('unknown mode')
