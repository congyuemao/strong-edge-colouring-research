"""Arithmetic cross-check of the pure table in joint_critical_size_bound.md."""
from itertools import product
from pathlib import Path
import json

rows = []
minimum = {}
for rp, rq in product(range(2), repeat=2):
    for t in range(6):
        for sp, sq in product(range(4), repeat=2):
            if sp+t > 4+rp or sq+t > 4+rq:
                continue
            h = rp+rq+sp+sq+t
            if h == 0 or h % 2:
                continue
            e0 = rp*(sp+t)+rq*(sq+t)+sp*(sp-1)//2+sq*(sq-1)//2
            j = int(rp == 0 and sp+t == 4)+int(rq == 0 and sq+t == 4)
            charge = 4*e0+7*j
            bound = max(h+j, 11*h-charge-4)
            row = dict(rp=rp,rq=rq,sp=sp,sq=sq,t=t,h=h,e0=e0,j=j,
                       charge=charge,bound=bound)
            rows.append(row)
            key = str(h)+','+str(rp+rq)
            minimum[key] = min(minimum.get(key, charge), charge)
expected = {'2,0':0,'2,1':0,'2,2':0,'4,0':0,'4,1':8,'4,2':8,
            '6,0':22,'6,1':20,'6,2':24,'8,1':43,'8,2':40,'10,2':64}
assert minimum == expected
assert max(row['bound'] for row in rows) == 44
out = {'scope':'Arithmetic necessary-parameter check; not a graph enumeration.',
       'minimum_charge':minimum,'global_bound':44,'rows':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k != 'rows'}))
