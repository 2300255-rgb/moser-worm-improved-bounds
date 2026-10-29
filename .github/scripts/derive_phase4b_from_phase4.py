#!/usr/bin/env python3
"""Derive Phase 4B from the independently frozen, Lean-passed Phase 4 inputs.

Exact equal support shift t=1/25_000_000 (total delta=7/50_000_000).
Changes only an expendable checkout. A numerical certificate preflight, NOT a Lean proof.
Never modifies the pinned original upstream or the proven Phase 4 archive.
"""
import argparse
import gzip
import hashlib
import io
import json
import re
import sys
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
from subprocess import check_output

BASE_DELTA = Q(1, 10_000_000)
SHIFT = Q(1, 25_000_000)
NEW_DELTA = BASE_DELTA + SHIFT
BASE_H = [Q(0), Q(0), Q(130783, 250000)-BASE_DELTA, Q(446199, 1000000)-BASE_DELTA]
NEW_H = [Q(0), Q(0), Q(130783, 250000)-NEW_DELTA, Q(446199, 1000000)-NEW_DELTA]
BASE_AREA = Q(13146096881486542786561993, 53367364863120000000000000)
NEW_AREA = Q(985957101148325639719241171, 4002552364734000000000000000)
BASE_SOURCE_SHA = '24369c3b0e4ce582a64a28891d923de11cbad91ee7603064c4ea6186d4a897a8'
BASE_CERT_SHA = 'c2650647317eaee181d53e447acd3e0f5f86f39a48d1f07fd40c6d6b800de594'
LEAVES = (2056, 4093, 7875, 9312, 11786)


def rat(v):
    v = Q(v)
    return str(v.numerator) if v.denominator == 1 else f'{v.numerator}/{v.denominator}'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def replace_once(s, old, new, label):
    assert s.count(old) == 1, (label, s.count(old), old)
    return s.replace(old, new, 1)


def shape_vertices_area(normals, offsets):
    vs = []
    for i in range(4):
        a,b = normals[i]
        c,d = normals[(i+1)%4]
        h,k = offsets[i], offsets[(i+1)%4]
        det = a*d-b*c
        assert det != 0
        vs.append(((h*d-b*k)/det,(a*k-h*c)/det))
    assert all(a*x+b*y<=h for x,y in vs for (a,b),h in zip(normals,offsets))
    area = sum(vs[i][0]*vs[(i+1)%4][1]-vs[(i+1)%4][0]*vs[i][1] for i in range(4))/2
    return vs,area


def all_leaf_rects(tree, header):
    rects = {}
    stack = [(tree,(0,header['kR'],0,header['kL']))]
    while stack:
        node,rect=stack.pop()
        if node[0]=='l':
            i=int(node[1]); assert i not in rects;rects[i]=rect
        elif node[0]=='p':
            stack.extend([(node[2],rect),(node[3],rect)])
        elif node[0]=='s':
            stack.extend((child,tuple(r)) for r,child in node[1])
        else: raise ValueError('Unknown tree branch '+str(node[0]))
    assert len(rects)==header['leaves']==12663
    assert set(rects)==set(range(header['leaves']))
    return rects


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--witnesses',type=Path,required=True)
    ap.add_argument('--report',type=Path,default=Path('phase4b-derived-report.json'))
    a=ap.parse_args()
    root=a.root.resolve()
    sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
    from common import source_snapshot
    import exact
    from exact import Geometry,inputs

    snap=source_snapshot()
    cert=root/'certificates/upper'
    inp,header,manifest=inputs(cert)
    assert snap['sha256']==BASE_SOURCE_SHA,('Base source fingerprint',snap['sha256'])
    assert inp['sha256']==BASE_CERT_SHA,('Base certificate fingerprint',inp['sha256'])
    assert [Q(x) for x in header['h']]==BASE_H
    assert exact.H==BASE_H
    assert header['complete'] is True and header['leaves']==12663
    assert len(manifest['files'])==50
    assert NEW_DELTA==Q(7,50_000_000)

    with gzip.open(a.witnesses,'rt',encoding='utf8') as f: data=json.load(f)
    assert data['source_phase4_certificate_sha256']==BASE_CERT_SHA
    assert Q(data['shift'])==SHIFT
    witness={int(item['leaf']):item for item in data['witnesses']}
    assert set(witness)==set(LEAVES) and len(data['witnesses'])==5
    for i,item in witness.items():
        assert item['leaf']==i
        assert int(item['denominator'])>0
        assert len(item['pairs'])>0

    # Geometry.escape caches the H-dependent escape bounds at construction.
    # Update exact.H BEFORE building Geometry (otherwise the old Phase 4
    # bounds would silently be used in its cached rows).
    exact.H=NEW_H
    g=Geometry(header['specs'])
    floor=g.n*g.n
    assert g.kR==header['kR'] and g.kL==header['kL']
    with gzip.open(cert/'tree.json.gz','rt') as f: tree=json.load(f)
    rects=all_leaf_rects(tree,header)

    # Evaluate all five witnesses with the EXACT source Geometry.valid method.
    # Do not claim all other 12658 geometrical constraints are recomputed here;
    # earlier full arithmetic scans are distinct evidence.
    vertices,area=shape_vertices_area(exact.NORMALS,NEW_H)
    assert area==NEW_AREA,('Area mismatch',rat(area))
    assert area<BASE_AREA
    assert (vertices[3][0]-vertices[1][0])**2+(vertices[3][1]-vertices[1][1])**2>Q(103,100)

    converted={};modified=set();count=0
    files={};full_keys_tested=0
    for name in manifest['files']:
        lines=[]
        with gzip.open(cert/name,'rt') as f:
            for line in f:
                i,den,pairs=json.loads(line)
                i=int(i);den=int(den)
                assert den>0 and i==count,(name,i,count)
                keys=[int(x[0]) for x in pairs]
                nums=[int(x[1]) for x in pairs]
                assert all(n>0 for n in nums)
                assert all(k>=0 for k in keys)
                assert sum(n*BASE_H[2+(k-floor-1)%2] for k,n in zip(keys,nums) if k>floor)==den,('Base LB mismatch',i)
                if i in witness:
                    item=witness[i]
                    newpairs=[(int(k),int(n)) for k,n in item['pairs']]
                    assert [k for k,_ in newpairs]==keys,('Changed row keys',i)
                    assert all(n>0 for _,n in newpairs)
                    new_nums=[n for _,n in newpairs]
                    assert g.valid(new_nums,g.integer_rows(keys),rects[i]),('New Geometry.valid false',i)
                    modified.add(i)
                    full_keys_tested+=len(keys)
                else:
                    new_nums=nums
                bound=sum(n*NEW_H[2+(k-floor-1)%2] for k,n in zip(keys,new_nums) if k>floor)
                assert bound>0,('Nonpositive bound',i)
                # normalize to exact LB=1; row force arithmetic is homogeneous.
                c=gcd(bound.numerator,gcd(*new_nums)*bound.denominator)
                newden=bound.numerator//c
                new_nums=[n*bound.denominator//c for n in new_nums]
                assert newden>0 and all(n>0 for n in new_nums)
                assert sum(n*NEW_H[2+(k-floor-1)%2] for k,n in zip(keys,new_nums) if k>floor)==newden,('LB not 1',i)
                lines.append(json.dumps([i,newden,[[k,n] for k,n in zip(keys,new_nums)]],separators=(',',':'))+'\n')
                count+=1
                if count%2500==0:print('PHASE4B_NORMALIZED_PROGRESS',count,flush=True)
        buf=io.BytesIO()
        with gzip.GzipFile(fileobj=buf,mode='wb',filename='',mtime=0,compresslevel=1) as gz:
            gz.write(''.join(lines).encode())
        files[name]=buf.getvalue()
    assert count==12663 and modified==set(LEAVES)

    # Change source declarations to the new rational quadrilateral.
    spec=root/'MoserWorm/UpperBound/Certificate/Spec.lean'
    changes={spec:replace_once(spec.read_text(),
        'def hLit : Fin 4 → ℚ := ![0, 0, '+rat(BASE_H[2])+', '+rat(BASE_H[3])+']',
        'def hLit : Fin 4 → ℚ := ![0, 0, '+rat(NEW_H[2])+', '+rat(NEW_H[3])+']','Spec.hLit')}
    shape=root/'MoserWorm/UpperBound/Shape.lean'
    s=shape.read_text(); pat=r'def vK : Fin 4 → Q2 :=\s*!\[.*?\]\s*\ndef vtx'
    newv='def vK : Fin 4 → Q2 :=\n  !['+',\n    '.join('('+rat(x)+', '+rat(y)+')' for x,y in vertices)+']\n\ndef vtx'
    s,n=re.subn(pat,lambda m:newv,s,flags=re.S)
    assert n==1,('Shape.vK',n)
    changes[shape]=replace_once(s,'def areaK : ℚ := '+rat(BASE_AREA),
                                'def areaK : ℚ := '+rat(NEW_AREA),'Shape.areaK')
    exactpath=root/'scripts/upper/exact.py'
    oldH='H = [Q(0), Q(0), Q("'+rat(BASE_H[2])+'"), Q("'+rat(BASE_H[3])+'")]'
    newH='H = [Q(0), Q(0), Q("'+rat(NEW_H[2])+'"), Q("'+rat(NEW_H[3])+'")]'
    changes[exactpath]=replace_once(exactpath.read_text(),oldH,newH,'Python.H')
    theorem=root/'MoserWorm/MainTheorem.lean'
    changes[theorem]=replace_once(theorem.read_text(),rat(BASE_AREA),rat(NEW_AREA),'MainTheorem.bound')

    newheader=dict(header);newheader['h']=list(map(rat,NEW_H))
    headerbytes=(json.dumps(newheader,indent=2,sort_keys=True)+'\n').encode()
    newmanifest=dict(manifest);newmanifest['sha256']=dict(manifest['sha256'])
    newmanifest['sha256']['header.json']=digest(headerbytes)
    for name,blob in files.items():newmanifest['sha256'][name]=digest(blob)

    # Write only into the disposable working checkout, not any pinned sources.
    for path,txt in changes.items():path.write_text(txt)
    (cert/'header.json').write_bytes(headerbytes)
    for name,blob in files.items():(cert/name).write_bytes(blob)
    (cert/'manifest.json').write_text(json.dumps(newmanifest,indent=2,sort_keys=True)+'\n')

    # Re-read with a FRESH Python process to avoid import-time H snapshots.
    check = '''import json,sys
from pathlib import Path
p=Path(sys.argv[1]);sys.path[:0]=[str(p/'scripts'),str(p/'scripts/upper')]
from common import source_snapshot
from exact import inputs,H
x,h,m=inputs(p/'certificates/upper')
print(json.dumps({'source':source_snapshot()['sha256'],'certificate':x['sha256'],'h':list(map(str,H))}))'''
    status=json.loads(check_output([sys.executable,'-c',check,str(root)],text=True))
    assert [Q(v) for v in status['h']]==NEW_H
    assert inputs(cert)[1]==newheader
    result={
      'status':'PHASE4B_DERIVED_EXACT_INPUTS_NOT_YET_LEAN_PROOF',
      'author':'Kazuma Iwai',
      'based_on_phase4_source_fingerprint':BASE_SOURCE_SHA,
      'based_on_phase4_certificate_fingerprint':BASE_CERT_SHA,
      'additional_shift':rat(SHIFT),'delta2':rat(NEW_DELTA),'delta3':rat(NEW_DELTA),
      'area_exact':rat(NEW_AREA),'leaves':count,'changed_leaves':sorted(modified),
      'all_LB_equal_1':True,'changed_leaf_geometry_valid_exact':True,
      'changed_leaf_rows':full_keys_tested,
      'normalized_certificate_files_updated':len(files),
      'source_fingerprint':status['source'],'certificate_fingerprint':status['certificate'],
      'lean_verified':False,
      'scope_note':'All 12663 LB normalized; Geometry.valid exact check is done here for 5 replaced leaves. The other leaves are covered by earlier separate exact arithmetic scan, and must be Lean checked.'
    }
    dest=a.report if a.report.is_absolute() else root/a.report
    dest.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PHASE4B_ALL_12663_LB_NORMALIZED_AND_FIVE_EXACT_GEOMETRY_VALID_PASS',flush=True)
    print('PHASE4B_DERIVED_AREA',rat(NEW_AREA),flush=True)
    print('PHASE4B_SOURCE_FINGERPRINT',status['source'],flush=True)
    print('PHASE4B_CERTIFICATE_FINGERPRINT',status['certificate'],flush=True)
    print('PHASE4B_LEAN_PROOF_NOT_YET_RUN',flush=True)

if __name__=='__main__':main()
