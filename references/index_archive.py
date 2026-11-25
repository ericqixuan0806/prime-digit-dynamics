"""Index an original RH archive without importing its modules or running its code."""
import argparse
from collections import Counter
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile

ARCHIVE_SHA = '9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc'
OUT=Path(__file__).resolve().parent
IMPORT=re.compile(rb'^[ \t]*(?:(?:public|private|meta|all)\s+)*import[ \t]+([^\r\n]+)',re.M)
DECL=re.compile(rb'^(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|axiom|opaque)\s+([^\s(:{\[]+)',re.M)
FOCUS={b'everyCharacter',b'rh_of_every',b'critLine',b'rowNGP_of_siegelWeil',b'windowBound',b'window_bound',b'log_derivative_bound',b'sum_size_finite_away_archimedean_combined'}
def canon(h, name, digest):
    h.update(name.encode()+b'\0'+bytes.fromhex(digest))

def run(archive, extract, git_listing, declaration_index):
    with archive.open('rb') as f:
        if hashlib.file_digest(f,'sha256').hexdigest()!=ARCHIVE_SHA:
            raise ValueError('archive SHA-256 mismatch')
    expected={}
    if git_listing:
        for line in Path(git_listing).read_bytes().splitlines():
            left,name=line.split(b'\t',1)
            expected[name.decode()]=left.split()[2].decode()
    graph, files, focus, source_sha = {},{},[],hashlib.sha256()
    ndecl=nlines=0
    extract.mkdir(parents=True,exist_ok=True)
    idx=(io.TextIOWrapper(gzip.GzipFile(filename='', fileobj=Path(declaration_index).open('wb'),
                                 mode='wb', compresslevel=2, mtime=0),encoding='utf-8')
         if declaration_index else None)
    with tarfile.open(archive,'r|gz') as t:
        for member in t:
            if not member.isfile():
                continue
            rel=member.name.removeprefix('lean/')
            data=t.extractfile(member).read()
            digest=hashlib.sha256(data).hexdigest()
            if expected:
                oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
                if expected.get(rel)!=oid:
                    raise ValueError(('Git blob mismatch',rel))
            files[rel]=digest
            if not rel.startswith('src/') or not rel.endswith('.lean'):
                continue
            module=rel[4:-5].replace('/','.')
            imports=[s.decode() for line in IMPORT.findall(data) for s in line.split(b'--')[0].split()]
            graph[module]=imports
            nlines+=len(data.splitlines())
            declarations=list(DECL.finditer(data))
            ndecl+=len(declarations)
            if idx:
                idx.write(json.dumps([module,[m[1].decode() for m in declarations]],ensure_ascii=False,separators=(',',':'))+'\n')
            hits=[(m[1].decode(),data.count(b'\n',0,m.start())+1) for m in declarations if m[1].split(b'.')[-1] in FOCUS]
            if hits or module in ('Main','Statements') or module.startswith('Supplements.Kernels.MainTheorems'):
                p=extract/rel
                p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
                focus.append([rel,hits])
    if idx:idx.close()
    if expected and {f for f in expected if f.startswith('src/')}!={f for f in files if f.startswith('src/')}:
        raise ValueError('source file sets differ')
    for f in sorted(files):canon(source_sha,f,files[f])
    seen,external,queue=set(),set(),['Main']
    while queue:
        m=queue.pop()
        if m in seen:continue
        seen.add(m)
        for dep in graph[m]:
            if dep in graph:queue.append(dep)
            else:external.add(dep)
    data=''.join(json.dumps([m,graph[m]],separators=(',',':'))+'\n' for m in sorted(graph)).encode()
    (OUT/'rh-imports.jsonl.gz').write_bytes(gzip.compress(data,compresslevel=6,mtime=0))
    report=dict(archive_sha256=ARCHIVE_SHA,canonical_files_sha256=source_sha.hexdigest(),
                canonical_format='sorted relative UTF-8 path, NUL, 32 raw SHA-256 digest bytes; includes three build files',
                files=len(files),source_modules=len(graph),source_lines=nlines,lexical_declarations=ndecl,
                main_import_closure=len(seen),direct_external_imports_in_closure=sorted(external),
                checked_against_git_blobs=bool(expected),top_namespaces=dict(sorted(Counter(m.split('.')[0] for m in seen).items())),
                selected_files=sorted(focus))
    (OUT/'rh-index.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print({k:v for k,v in report.items() if k not in ('selected_files','direct_external_imports_in_closure','top_namespaces')})
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('archive',type=Path);p.add_argument('--extract',type=Path,required=True)
    p.add_argument('--git-listing');p.add_argument('--declaration-index')
    args=p.parse_args()
    run(args.archive,args.extract,args.git_listing,args.declaration_index)
