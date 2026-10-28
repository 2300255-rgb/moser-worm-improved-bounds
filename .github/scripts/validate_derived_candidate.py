#!/usr/bin/env python3
"""Exact full-tree numerical preflight for DERIVED micro candidate (NOT Lean proof)."""
import argparse, gzip, json, sys, time
from pathlib import Path
from fractions import Fraction as F

PIN_H=[F(0),F(0),F(15693959,30000000),F(13385969,30000000)]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path.cwd())
    ap.add_argument('--report',type=Path,default=None)
    ap.add_argument('--skip-export',action='store_true',help='Only verify exact leaf conditions; generate Lean modules in a separate run')
    args=ap.parse_args();root=args.root.resolve()
    sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
    from exact import H,Geometry,inputs
    from export import export,SHARD_SIZE
    from common import source_snapshot
    start=time.monotonic()
    assert H==PIN_H
    snap,header,manifest=inputs(root/'certificates/upper')
    assert header['complete'] is True and [F(x) for x in header['h']]==H
    assert header['leaves']==12663 and header['kR']==30 and header['kL']==30
    g=Geometry(header['specs'])
    assert (g.kR,g.kL)==(header['kR'],header['kL'])
    with gzip.open(root/'certificates/upper/tree.json.gz','rt') as fp: tree=json.load(fp)
    cells={};stack=[(tree,(0,header['kR'],0,header['kL']))]
    while stack:
        node,rect=stack.pop()
        if node[0]=='l':
            idx=node[1];assert idx not in cells;cells[idx]=rect
        elif node[0]=='p':
            stack.append((node[2],rect));stack.append((node[3],rect))
        elif node[0]=='s':
            for sub,child in node[1]:stack.append((child,tuple(sub)))
        else: raise ValueError('Unexpected tree node '+str(node[0]))
    assert set(cells)==set(range(12663))
    failed=[];count=0
    for name in manifest['files']:
        with gzip.open(root/'certificates/upper'/name,'rt') as fp:
            for line in fp:
                idx,den,pairs=json.loads(line)
                weights=[v for k,v in pairs]
                assert den>0 and all(v>0 for v in weights)
                result=g.valid(weights,g.integer_rows(k for k,v in pairs),cells[idx])
                if not result:failed.append(idx)
                count+=1
                if count%2500==0:print('DERIVED_LEAF_PRECHECK',count,flush=True)
    assert count==12663 and not failed, (count,failed[:15])
    print('DERIVED_ALL_12663_NUMERICAL_LEAVES_PASS',flush=True)
    sources=source_snapshot()
    out=root/'MoserWorm/UpperBound/Certificate/Generated'
    if args.skip_export:
        gen={'modules':[],'shards':None}
        print('LEAN_SOURCE_GENERATION_SKIPPED',flush=True)
    else:
        gen=export(root/'certificates/upper',out)
        assert gen['complete'] is True and gen['inputs']==snap and gen['shard_size']==SHARD_SIZE
        assert gen['shards']==1583 and len(gen['modules'])==1636
        print('DERIVED_ALL_1636_LEAN_SOURCES_GENERATED',flush=True)
    record={'status':'DERIVED_PYTHON_PREFLIGHT_PASS_NOT_LEAN_PROOF',
            'complete':False,'number_of_leaves':count,'numerically_failed_leaves':len(failed),
            'source_fingerprint':sources['sha256'],'certificate_fingerprint':snap['sha256'],
            'generated_module_count':len(gen['modules']) if not args.skip_export else None,'generated_shard_count':gen['shards'],
            'elapsed_seconds':round(time.monotonic()-start,2),
            'notes':['Exact Python preflight does not establish soundness of changed geometry.',
                     'No Lean kernel or audit_axioms execution occurred.']}
    dest=args.report or root/'micro-numeric-preflight.json'
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print('DERIVED_PREFLIGHT_PYTHON_PASS; NOT_A_NEW_UNIVERSAL_COVER_THEOREM',flush=True)
if __name__=='__main__':main()
