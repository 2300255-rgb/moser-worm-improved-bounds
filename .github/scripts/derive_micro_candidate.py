#!/usr/bin/env python3
"""Construct a strictly derived (NOT yet Lean-proven) micro-shrunk Upper candidate.

Run only in a disposable checkout/copy of upstream commit
9a3394130fe4f7b1df6ffdeffda16601795d9ce4.

No untrusted shortcuts: original source/input fingerprints are required; leaf/tree
binaries remain bit-identical; the changed header manifest is rehashed.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import sys

PIN = '9a3394130fe4f7b1df6ffdeffda16601795d9ce4'
ORIGINAL_SOURCE = '6bb6aea19cedc7d533eec5344eb8f552456c3c717e3f621009176755114171d9'
ORIGINAL_INPUT = 'f2d343224b0ba055cd530d5ded53e0c667c3cbbd30be2f2412906448cb39f0dc'
OLD_AREA = F(7170601298323360123534337,29109471743520000000000000)
NEW_AREA = F(70988942955609283719006199,288183770260848000000000000)
DELTA = F(1,30_000_000)

def digest(b):return hashlib.sha256(b).hexdigest()
def rational(x):return f'{x.numerator}/{x.denominator}' if x.denominator!=1 else str(x.numerator)
def fmt_point(v):return '(' + ', '.join(map(rational,v)) + ')'
def substitute_once(text,pat,replacement,label,flags=0):
    out,n=re.subn(pat,lambda m:replacement,text,flags=flags)
    if n!=1: raise RuntimeError(f'{label}: expected 1 match, got {n}')
    return out

def intersection(n1,n2,h1,h2):
    a,b=n1; c,d=n2
    det=a*d-b*c
    if det==0:raise RuntimeError('parallel normal pair')
    return ((h1*d-b*h2)/det,(a*h2-c*h1)/det)

def geometry(normals,hs):
    vertices=[intersection(normals[i],normals[(i+1)%4],hs[i],hs[(i+1)%4]) for i in range(4)]
    for v in vertices:
        for n,h in zip(normals,hs):
            if n[0]*v[0]+n[1]*v[1]>h:
                raise RuntimeError('candidate vertex outside one of four half-planes')
    area=sum(vertices[i][0]*vertices[(i+1)%4][1]-vertices[(i+1)%4][0]*vertices[i][1] for i in range(4))/2
    assert area>0
    return area,vertices

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,default=Path.cwd(),help='A disposable upstream checkout directory')
    p.add_argument('--report',type=Path,default=None)
    args=p.parse_args()
    root=args.root.resolve()
    sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
    from exact import H,NORMALS,inputs
    from common import source_snapshot
    from export import export_sources
    source_before=source_snapshot()
    inp_before,header,manifest=inputs(root/'certificates/upper')
    assert source_before['sha256']==ORIGINAL_SOURCE, 'not pinned original source; refusing modification'
    assert inp_before['sha256']==ORIGINAL_INPUT, 'not pinned original certificate; refusing modification'
    assert header.get('complete') is True and header.get('leaves')==12663
    assert [F(x) for x in header['h']]==H
    assert H==[F(0),F(0),F(130783,250000),F(446199,1000000)]
    assert len(header['specs'])>0 and manifest.get('files')
    old_area,old_vertices=geometry(NORMALS,H)
    assert old_area==OLD_AREA, 'original shape/area mismatch'
    new_h=[H[0],H[1],H[2]-DELTA,H[3]-DELTA]
    area,vertices=geometry(NORMALS,new_h)
    assert area==NEW_AREA, 'independent candidate exact area mismatch'
    assert area<OLD_AREA
    chord_sq=sum((vertices[1][i]-vertices[3][i])**2 for i in range(2))
    assert chord_sq>F(103,100), 'original long-chord threshold no longer valid'
    for ray in ([F('5541045/8027539'),F('24427652/40137695'),F(1),F(0)],
                [F('47299645/118570699'),F('502233812/592853495'),F(0),F(1)]):
        target = new_h[2] if ray[2] == 1 else new_h[3]
        assert sum(ray[i]*new_h[i] for i in range(4)) == target

    spec=root/'MoserWorm/UpperBound/Certificate/Spec.lean'
    shape=root/'MoserWorm/UpperBound/Shape.lean'
    exact=root/'scripts/upper/exact.py'
    theorem=root/'MoserWorm/MainTheorem.lean'
    changes={}
    spec_original=spec.read_text()
    changes[spec]=substitute_once(spec_original,
        r'def hLit : Fin 4 → ℚ := !\[0, 0, 130783/250000, 446199/1000000\]',
        'def hLit : Fin 4 → ℚ := ![0, 0, '+rational(new_h[2])+', '+rational(new_h[3])+']',
        'Spec.hLit')
    shape_original=shape.read_text()
    new_points='def vK : Fin 4 → Q2 :=\n  !['+',\n    '.join(fmt_point(v) for v in vertices)+']\n\ndef vtx'
    changes[shape]=substitute_once(shape_original,r'def vK : Fin 4 → Q2 :=\s*!\[.*?\]\s*\ndef vtx',new_points,'Shape.vK',re.S)
    changes[shape]=substitute_once(changes[shape],r'def areaK : ℚ := 7170601298323360123534337 / 29109471743520000000000000',
        'def areaK : ℚ := '+rational(area),'Shape.areaK')
    exact_original=exact.read_text()
    changes[exact]=substitute_once(exact_original,
        r'H = \[Q\(0\), Q\(0\), Q\("130783/250000"\), Q\("446199/1000000"\)\]',
        'H = [Q(0), Q(0), Q("'+rational(new_h[2])+'"), Q("'+rational(new_h[3])+'")]',
        'Python.H')
    main_original=theorem.read_text()
    changes[theorem]=substitute_once(main_original,
        r'7170601298323360123534337 / 29109471743520000000000000',
        rational(area),'MainTheorem.bound')
    for path,updated in changes.items():
        assert updated != path.read_text(), f'No change in {path}'
    # Preserve every original certificate binary; only rewrite header and its manifest digest.
    certdir=root/'certificates/upper'
    headerfile=certdir/'header.json';manifestfile=certdir/'manifest.json'
    new_header=dict(header);new_header['h']=[rational(q) for q in new_h]
    new_header_bytes=(json.dumps(new_header,indent=2,sort_keys=True)+'\n').encode()
    new_manifest=dict(manifest)
    new_manifest['sha256']=dict(manifest['sha256'])
    new_manifest['sha256']['header.json']=digest(new_header_bytes)
    new_manifest_bytes=(json.dumps(new_manifest,indent=2,sort_keys=True)+'\n').encode()
    # Actual writes start only after all structural validations.
    for path,updated in changes.items():path.write_text(updated)
    headerfile.write_bytes(new_header_bytes)
    manifestfile.write_bytes(new_manifest_bytes)

    # Inspect in a fresh interpreter: module 'exact' in this interpreter is the old import.
    from subprocess import check_output
    verify_code='''import sys,json
from pathlib import Path
from fractions import Fraction as F
root=Path(sys.argv[1]);sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
from exact import H,inputs
from common import source_snapshot
from export import export_sources
inp,header,_=inputs(root/'certificates/upper')
assert [F(x) for x in header['h']]==H
print(json.dumps({'source':source_snapshot()['sha256'],'inputs':inp['sha256'],'export_sources':export_sources()['sha256']}))'''
    recheck=json.loads(check_output([sys.executable,'-c',verify_code,str(root)],text=True))
    record={'schema':1,'status':'DERIVED_INPUTS_READY_NOT_A_LEAN_PROOF',
        'upstream_commit':PIN,'delta2':rational(DELTA),'delta3':rational(DELTA),
        'original_source_fingerprint':ORIGINAL_SOURCE,'original_certificate_fingerprint':ORIGINAL_INPUT,
        'derived_source_fingerprint':recheck['source'],'derived_certificate_fingerprint':recheck['inputs'],
        'derived_export_sources_fingerprint':recheck['export_sources'],
        'h':list(map(rational,new_h)),'vertices':[list(map(rational,v)) for v in vertices],
        'exact_area':rational(area),'original_area':rational(OLD_AREA),
        'exact_improvement':rational(OLD_AREA-area),
        'chord_squared':rational(chord_sq),
        'changed_paths':[str(q.relative_to(root)) for q in changes]+['certificates/upper/header.json','certificates/upper/manifest.json'],
        'unchanged_binary_hashes':{name:manifest['sha256'][name] for name in ['tree.json.gz',*manifest['files']]},
        'original_modules_not_modified':True,'lean_compiled':False,
        'notes':['Existing leaf multipliers and split tree are bit-identical; modified rows/constants require new Lean kernel checks.',
                 'MainTheorem bound is updated for source coherence but is not compiled by the preflight.',
                 'Do not report new universal cover bound until derivative Main and audit_axioms compile.']}
    dest=args.report or (root/'micro-derived-input-report.json')
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print('MICRO_DERIVED_SOURCE_AND_CERTIFICATE_PASS',flush=True)
    print('MICRO_AREA_EXACT',rational(area),flush=True)
    print('MICRO_CHORD_SQ',rational(chord_sq),flush=True)
    print('LEAN_PROOF_NOT_ATTEMPTED',flush=True)

if __name__=='__main__':main()
