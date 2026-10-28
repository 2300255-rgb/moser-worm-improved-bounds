#!/usr/bin/env python3
"""Normalize micro-derived Upper leaf multipliers to Lean's absolute target LB >= 1.

Run *after* derive_micro_candidate.py in a disposable pinned upstream checkout,
*before* export().  This changes ONLY the derived certificate multiplier shards
and the corresponding SHA-256 entries of its manifest.  Original pinned inputs
remain separate and unchanged.

For each leaf with original rational multipliers mu_i = n_i / d and
L = sum_{E-rows} n_i * h_ray > 0, set mu_i' = n_i / L.
Then sum_E mu_i' * h_ray = 1, and every force is divided by the old LB=L/d.
The existing exact Python Geometry.valid preflight tests the required
scale-invariant inequality; after this normalization, it is equivalent to
norm^2 <= 1 at LB = 1.  Lean compilation is still required.
"""
import argparse
import csv
from fractions import Fraction as F
import gzip
import hashlib
import json
from math import gcd
from pathlib import Path
import sys

PIN='9a3394130fe4f7b1df6ffdeffda16601795d9ce4'
SOURCE_FINGERPRINT='6bb6aea19cedc7d533eec5344eb8f552456c3c717e3f621009176755114171d9'
EXPECTED_H=[F(0),F(0),F(15693959,30000000),F(13385969,30000000)]


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as fp:
        for chunk in iter(lambda:fp.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path.cwd())
    ap.add_argument('--derive-report',type=Path,default=Path('micro-derived-input-report.json'))
    ap.add_argument('--report',type=Path,default=Path('micro-normalization-report.json'))
    ap.add_argument('--csv',type=Path,default=Path('micro-normalization-per-leaf.csv'))
    args=ap.parse_args()
    root=args.root.resolve()
    def at(p):return p if p.is_absolute() else root/p
    sys.path[:0]=[str(root/'scripts'),str(root/'scripts/upper')]
    from common import source_snapshot
    from exact import H,Geometry,inputs
    derive=json.loads(at(args.derive_report).read_text())
    assert derive['upstream_commit']==PIN
    assert derive['derived_source_fingerprint']==source_snapshot()['sha256']
    assert [F(x) for x in H]==EXPECTED_H
    cert=root/'certificates/upper'
    snapshot,header,manifest=inputs(cert)
    assert header['complete'] is True and header['leaves']==12663
    assert snapshot['sha256']==derive['derived_certificate_fingerprint'], 'Input not original derived certificate (already modified?)'
    geom=Geometry(header['specs'])
    floor=geom.n**2
    filenames=manifest['files']
    assert len(filenames)>0
    assert sha(cert/'tree.json.gz')==derive['unchanged_binary_hashes']['tree.json.gz']
    pending={}; table=[]
    counts={'lt':0,'eq':0,'gt':0}
    min_LB=None; max_LB=None
    ids=set()
    for fn in filenames:
        path=cert/fn
        assert sha(path)==derive['unchanged_binary_hashes'][fn],f'Unexpected input shard: {fn}'
        out_lines=[]
        with gzip.open(path,'rt',encoding='utf8') as fp:
            for line in fp:
                i,den,pairs=json.loads(line)
                assert isinstance(i,int) and i not in ids and 0<=i<header['leaves']
                ids.add(i)
                assert isinstance(den,int) and den>0 and pairs
                assert all(isinstance(k,int) and isinstance(n,int) and k>=0 and n>0 for k,n in pairs)
                e0=sum(n for k,n in pairs if k>floor and (k-floor-1)%2==0)
                e1=sum(n for k,n in pairs if k>floor and (k-floor-1)%2==1)
                L=e0*H[2]+e1*H[3]
                assert L>0,f'No positive escape bound for leaf {i}'
                oldLB=L/den
                if oldLB<1:counts['lt']+=1
                elif oldLB==1:counts['eq']+=1
                else:counts['gt']+=1
                min_LB=oldLB if min_LB is None or oldLB<min_LB else min_LB
                max_LB=oldLB if max_LB is None or oldLB>max_LB else max_LB
                # Rational: n/den divided by L/den is n/L. gcd reduces numerator and denominator.
                common=gcd(L.numerator, gcd(*[n for _,n in pairs])*L.denominator)
                newden=L.numerator//common
                newpairs=[[k,(n*L.denominator)//common] for k,n in pairs]
                assert newden>0 and all(n>0 for _,n in newpairs)
                newLB=F(L.denominator,common)*L/newden
                assert newLB==1, f'Normalization failed leaf {i}'
                out_lines.append(json.dumps([i,newden,newpairs],separators=(',',':'))+'\n')
                table.append([i,den,newden,oldLB.numerator,oldLB.denominator,len(pairs)])
        # Reproducible gzip bytes; independent of current timestamp and source filename.
        import io
        buff=io.BytesIO()
        with gzip.GzipFile(fileobj=buff,mode='wb',compresslevel=1,mtime=0,filename='') as fp:
            fp.write(''.join(out_lines).encode())
        pending[path]=buff.getvalue()
        print('PREPARED_NORMALIZED_SHARD',fn,'leaf_count',len(out_lines),flush=True)
    assert ids==set(range(header['leaves']))
    # Only after all leaves validate: update each compressed shard and its manifest digest.
    newmanifest=dict(manifest)
    newmanifest['sha256']=dict(manifest['sha256'])
    for path,data in pending.items():
        path.write_bytes(data)
        newmanifest['sha256'][path.name]=hashlib.sha256(data).hexdigest()
    (cert/'manifest.json').write_text(json.dumps(newmanifest,indent=2,sort_keys=True)+'\n')
    newfp,newheader,newm=inputs(cert)
    assert newheader==header and newm==newmanifest
    assert sha(cert/'tree.json.gz')==derive['unchanged_binary_hashes']['tree.json.gz']
    assert source_snapshot()['sha256']==derive['derived_source_fingerprint']
    table.sort()
    with at(args.csv).open('w',newline='') as fp:
        w=csv.writer(fp)
        w.writerow(['leaf','original_den','normalized_den','raw_LB_numerator','raw_LB_denominator','row_count'])
        w.writerows(table)
    record={'status':'NORMALIZED_EXACT_INPUTS_NOT_A_LEAN_PROOF',
            'upstream_commit':PIN,'number_of_leaves':len(ids),
            'original_derived_certificate_fingerprint':snapshot['sha256'],
            'normalized_certificate_fingerprint':newfp['sha256'],
            'derived_source_fingerprint':derive['derived_source_fingerprint'],
            'changed_multiplier_files':filenames,
            'tree_sha256_unchanged':sha(cert/'tree.json.gz'),
            'number_of_raw_LB_below_1':counts['lt'],
            'number_of_raw_LB_equal_1':counts['eq'],
            'number_of_raw_LB_above_1':counts['gt'],
            'minimum_raw_LB':str(min_LB),'maximum_raw_LB':str(max_LB),
            'normalized_all_LB_equal_1':True,
            'evidence_per_leaf_csv':str(args.csv),
            'lean_verified':False,
            'note':'Normalization is exact and preserves the original per-leaf coefficient ratios. It is not an independently checked universal cover theorem.'}
    at(args.report).write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print('NORMALIZED_ALL_12663_LEAF_BOUNDS_EQUAL_1',flush=True)
    print('RAW_BOUNDS_LT_EQ_GT',counts,flush=True)
    print('NORMALIZED_CERTIFICATE_FINGERPRINT',newfp['sha256'],flush=True)
    print('LEAN_PROOF_NOT_EXECUTED',flush=True)

if __name__=='__main__':main()
