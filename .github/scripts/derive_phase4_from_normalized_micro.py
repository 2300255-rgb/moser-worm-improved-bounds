#!/usr/bin/env python3
"""Phase 4 derived upper certificate for delta=1/10^7, EXACT Python preflight.

Input: disposable derived + *normalized* micro checkout (delta=1/30e6).
Output: 5 modified witnesses, all other leaf ratios preserved, all normalized LB=1.
Provenance: immutable upstream + experimental derivation scripts, never original git tree.
This does NOT establish the universal-cover theorem; run Lean separately.
"""
import argparse, gzip, hashlib, io, json, re, sys
from fractions import Fraction as Q
from pathlib import Path
from math import gcd

MICRO = Q(1, 30000000)
NEW = Q(1, 10000000)
OLD_H = [Q(0), Q(0), Q(130783,250000)-MICRO, Q(446199,1000000)-MICRO]
NEW_H = [Q(0), Q(0), Q(130783,250000)-NEW, Q(446199,1000000)-NEW]
MICRO_AREA = Q(70988942955609283719006199,288183770260848000000000000)
PHASE4_AREA = Q(13146096881486542786561993,53367364863120000000000000)
MICRO_SOURCE_SHA = '1bbf49771dce22c70d5a6087c61940e068fc615c07079526809c22d28851611d'
MICRO_CERT_SHA = '182edf6da38446623a3b3c288aa49097402cc430146d00688e6135f52d0c27e5'
WITNESS_IDS = {2056, 4093, 7875, 9312, 11786}

def rat(x):
    return str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'

def change_once(text, old, new, label):
    assert text.count(old) == 1, f'{label}: expected exactly one old literal, found {text.count(old)}'
    return text.replace(old, new, 1)

def sha(data):return hashlib.sha256(data).hexdigest()

def vertices_area(normals, hs):
    vertices=[]
    for i in range(4):
        a,b=normals[i];c,d=normals[(i+1)%4]
        det=a*d-b*c
        assert det
        vertices.append(((hs[i]*d-b*hs[(i+1)%4])/det,(a*hs[(i+1)%4]-hs[i]*c)/det))
    assert all(a*x+b*y <= h for x,y in vertices for (a,b),h in zip(normals,hs))
    area=sum(vertices[i][0]*vertices[(i+1)%4][1]-vertices[(i+1)%4][0]*vertices[i][1] for i in range(4))/2
    return vertices,area

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,required=True)
    p.add_argument('--witnesses',type=Path,required=True)
    p.add_argument('--report',type=Path,default=Path('phase4-derived-report.json'))
    a=p.parse_args(); root=a.root.resolve()
    sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
    import exact
    from exact import Geometry,inputs
    from common import source_snapshot
    assert exact.H==OLD_H, ('Not micro-normalized checkout',exact.H)
    snap=source_snapshot();inp,header,manifest=inputs(root/'certificates/upper')
    assert snap['sha256']==MICRO_SOURCE_SHA,snap['sha256']
    assert inp['sha256']==MICRO_CERT_SHA,inp['sha256']
    assert header['complete'] is True and header['leaves']==12663
    assert [Q(v) for v in header['h']]==OLD_H
    data=json.loads(a.witnesses.read_text())
    assert data['delta']=='1/10000000'
    witness={int(i):v for i,v in data['leaf_witnesses'].items()}
    assert set(witness)==WITNESS_IDS
    # Check witnesses before writing. The exact row-key sets are immutable.
    geom=Geometry(header['specs']);floor=geom.n**2
    oldH=exact.H
    exact.H=NEW_H
    vertices,area=vertices_area(exact.NORMALS,NEW_H)
    assert area==PHASE4_AREA, (area,PHASE4_AREA)
    with gzip.open(root/'certificates/upper/tree.json.gz','rt') as f:tree=json.load(f)
    cells={};stack=[(tree,(0,header['kR'],0,header['kL']))]
    while stack:
        node,rect=stack.pop()
        if node[0]=='l':
            i=node[1];assert i not in cells;cells[i]=rect
        elif node[0]=='p':
            stack.append((node[2],rect));stack.append((node[3],rect))
        elif node[0]=='s':
            for sub,ch in node[1]:stack.append((ch,tuple(sub)))
        else:raise AssertionError(node[0])
    assert set(cells)==set(range(12663))
    # Build transformed gz shards in memory, but do not touch originals until verified.
    rewritten={};count=0;replaced=set();files=manifest['files']
    for name in files:
        lines=[]
        with gzip.open(root/'certificates/upper'/name,'rt') as f:
            for line in f:
                i,den,pairs=json.loads(line); i=int(i)
                keys=[int(k) for k,_ in pairs];nums=[int(v) for _,v in pairs]
                assert den>0 and all(v>0 for v in nums)
                assert cells[i] is not None
                if i in witness:
                    assert list(map(int,[x[0] for x in witness[i]['normalized_weights']]))==keys, f'key mismatch {i}'
                    normden=int(witness[i]['normalized_den'])
                    normnums=[int(x[1]) for x in witness[i]['normalized_weights']]
                    assert sha(json.dumps(normnums,separators=(',',':')).encode())==witness[i]['normalized_weight_sha256']
                    replaced.add(i)
                else:
                    L=sum(n*NEW_H[2+(k-floor-1)%2] for k,n in pairs if k>floor)
                    assert L>0,i
                    c=gcd(L.numerator,gcd(*nums)*L.denominator)
                    normden=L.numerator//c
                    normnums=[n*L.denominator//c for n in nums]
                L2=sum(n*NEW_H[2+(k-floor-1)%2] for k,n in zip(keys,normnums) if k>floor)
                assert L2==normden,('LB≠1',i,L2,normden)
                if i in witness:
                    assert geom.valid(normnums,geom.integer_rows(keys),cells[i]),('Geometry.valid false',i)
                lines.append(json.dumps([i,normden,list(map(list,zip(keys,normnums)))],separators=(',',':'))+'\n')
                count+=1
                if count%2500==0:print('PHASE4_VERIFIED_LEAVES',count,flush=True)
        out=io.BytesIO()
        with gzip.GzipFile(fileobj=out,mode='wb',compresslevel=1,mtime=0,filename='') as z:
            z.write(''.join(lines).encode())
        rewritten[name]=out.getvalue()
    assert count==12663 and replaced==WITNESS_IDS
    # Update geometric constants, exactly once each.
    changes={}
    spec=root/'MoserWorm/UpperBound/Certificate/Spec.lean'
    changes[spec]=change_once(spec.read_text(),'def hLit : Fin 4 → ℚ := ![0, 0, '+rat(OLD_H[2])+', '+rat(OLD_H[3])+']',
                                  'def hLit : Fin 4 → ℚ := ![0, 0, '+rat(NEW_H[2])+', '+rat(NEW_H[3])+']','Spec.hLit')
    shape=root/'MoserWorm/UpperBound/Shape.lean'
    s=shape.read_text();vpattern=r'def vK : Fin 4 → Q2 :=\s*!\[.*?\]\s*\ndef vtx'
    new_vertices='def vK : Fin 4 → Q2 :=\n  !['+',\n    '.join('('+rat(x)+', '+rat(y)+')' for x,y in vertices)+']\n\ndef vtx'
    s,n=re.subn(vpattern,lambda m:new_vertices,s,flags=re.S);assert n==1,n
    s=change_once(s,'def areaK : ℚ := '+rat(MICRO_AREA),'def areaK : ℚ := '+rat(area),'Shape.areaK')
    changes[shape]=s
    exactfile=root/'scripts/upper/exact.py'
    oldline='H = [Q(0), Q(0), Q("'+rat(OLD_H[2])+'"), Q("'+rat(OLD_H[3])+'")]'
    newline='H = [Q(0), Q(0), Q("'+rat(NEW_H[2])+'"), Q("'+rat(NEW_H[3])+'")]'
    changes[exactfile]=change_once(exactfile.read_text(),oldline,newline,'Python.H')
    theorem=root/'MoserWorm/MainTheorem.lean'
    changes[theorem]=change_once(theorem.read_text(),rat(MICRO_AREA),rat(area),'MainTheorem.bound')
    newheader=dict(header);newheader['h']=list(map(rat,NEW_H))
    headerbytes=(json.dumps(newheader,indent=2,sort_keys=True)+'\n').encode()
    newmanifest=dict(manifest);newmanifest['sha256']=dict(manifest['sha256']);newmanifest['sha256']['header.json']=sha(headerbytes)
    for name,data in rewritten.items():newmanifest['sha256'][name]=sha(data)
    # Now commit changes in disposable root; re-open through exact.inputs in fresh interpreter.
    for path,text in changes.items():path.write_text(text)
    cert=root/'certificates/upper'
    (cert/'header.json').write_bytes(headerbytes)
    for name,blob in rewritten.items():(cert/name).write_bytes(blob)
    (cert/'manifest.json').write_text(json.dumps(newmanifest,indent=2,sort_keys=True)+'\n')
    assert inputs(cert)[1]==newheader
    from subprocess import check_output
    check='''import sys,json
from pathlib import Path
r=Path(sys.argv[1]);sys.path[:0]=[str(r/'scripts'),str(r/'scripts/upper')]
from common import source_snapshot
from exact import inputs,H
x,h,m=inputs(r/'certificates/upper')
print(json.dumps({'source':source_snapshot()['sha256'],'inputs':x['sha256'],'h':list(map(str,H))}))'''
    from subprocess import check_output
    checkdata=json.loads(check_output([sys.executable,'-c',check,str(root)],text=True))
    assert list(map(Q,checkdata['h']))==NEW_H
    result={'status':'PHASE4_EXACT_DERIVED_INPUTS_NOT_LEAN_PROOF','upstream_commit':'9a3394130fe4f7b1df6ffdeffda16601795d9ce4',
            'delta2':rat(NEW),'delta3':rat(NEW),'area_exact':rat(area),'leaves':count,'reoptimized_leaves':sorted(replaced),
            'source_fingerprint':checkdata['source'],'certificate_fingerprint':checkdata['inputs'],
            'original_micro_source_fingerprint':MICRO_SOURCE_SHA,'original_micro_certificate_fingerprint':MICRO_CERT_SHA,
            'certificate_files_updated':len(files),'all_LB_equal_1':True,'five_modified_Geometry_valid':True,'unchanged_leaf_exact_integer_audit':'see Phase4 composite audit','lean_verified':False}
    dest=a.report if a.report.is_absolute() else root/a.report
    dest.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('PHASE4_ALL_12663_LB_EQUAL_1_AND_FIVE_GEOMETRY_VALID_PASS',flush=True)
    print('PHASE4_DERIVED_AREA',rat(area),flush=True)
    print('PHASE4_REOPTIMIZED_LEAVES',sorted(replaced),flush=True)
    print('PHASE4_SOURCE_FINGERPRINT',checkdata['source'],flush=True)
    print('PHASE4_CERTIFICATE_FINGERPRINT',checkdata['inputs'],flush=True)
    print('PHASE4_NOT_YET_A_LEAN_PROOF',flush=True)

if __name__=='__main__':main()
