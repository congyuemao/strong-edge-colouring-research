"""Exact conditional potential on the three-saturated central core.

This does not assert the boundary can be completed globally.  It tests only
the abstract induced core and degree counts forced by an optimal partition.
The subsequent pure proof three_saturated_cross.md excludes the putative
optimal partition by using its exterior red edges.  This computation is kept
only to document why recoloring the 24-vertex core alone did not suffice.
"""
import itertools, json
from pathlib import Path

def solve_cross():
    # q_i=0..3, r_i=4..7; R_i are four satellite vertices 8+4*i+j.
    n=24
    adj=[set() for _ in range(n)]
    def edge(a,b): adj[a].add(b); adj[b].add(a)
    for group in [range(4),range(4,8)]:
        for a,b in itertools.combinations(group,2):edge(a,b)
    for i in range(4):
        for j in range(4):
            if j!=(i+2)%4:edge(i,4+j)
        sat=list(range(8+4*i,12+4*i))
        for a,b in itertools.combinations(sat,2):edge(a,b)
        for j,a in enumerate(sat):
            edge(i,a); edge(a,4+(i if j<2 else (i-1)%4))
    original=[1,1,0,1,1,2,2,2]+[0]*16
    # Each old A satellite has degree (4 or 3, 4 or 5, 4),
    # according to whether its central q is in A.
    full=[]
    for i in range(4):full.append([4,4,4] if i==2 else [5,3,4])
    # r_i has four satellite A-neighbors plus q_2 iff i != 0.
    for i in range(4):full.append([4,3,5] if i==0 else [5,5,2])
    for i in range(4):
        full.extend([[4,4,4] if i==2 else [3,5,4]]*4)
    outside=[]
    for v in range(n):
        inside=[sum(original[u]==c for u in adj[v]) for c in range(3)]
        out=[full[v][c]-inside[c] for c in range(3)]
        assert min(out)>=0,(v,full[v],inside)
        outside.append(out)
    rcap=[4,3,3]
    unary=[[out[c]-rcap[c] for c in range(3)] for out in outside]
    def phi(p):return sum(unary[v][p[v]] for v in range(n))+sum(p[v]==p[u] for v in range(n) for u in adj[v] if v<u)
    opts={}
    for i in range(4):
        sats=range(8+4*i,12+4*i)
        for q,a,b in itertools.product(range(3),repeat=3):
            best=None
            for vals in itertools.product(range(3),repeat=4):
                score=sum(unary[v][val] for v,val in zip(sats,vals))
                score+=sum(vals[j]==vals[k] for j,k in itertools.combinations(range(4),2))
                score+=sum(v==q for v in vals)+sum(vals[j]==a for j in (0,1))+sum(vals[j]==b for j in (2,3))
                if best is None or score<best[0]:best=(score,vals)
            opts[i,q,a,b]=best
    result=None
    for core in itertools.product(range(3),repeat=8):
        score=sum(unary[v][core[v]] for v in range(8))+sum(core[v]==core[u] for v in range(8) for u in adj[v] if v<u<8)
        vals=[]
        for i in range(4):
            local=opts[i,core[i],core[4+i],core[4+(i-1)%4]]
            score+=local[0]; vals.extend(local[1])
        if result is None or score<result[0]:result=(score,list(core)+vals)
    assert phi(result[1])==result[0]
    return dict(scope='Conditional abstract core only; not a globally optimal real G/F certificate. Full branch subsequently excluded by three_saturated_cross.md.',case='all_four_cross_edges_red',original=original,original_phi=phi(original),best_phi=result[0],best_partition=result[1],outside=outside,edges=[[v,u] for v in range(n) for u in sorted(adj[v]) if v<u])

if __name__=='__main__':
    result=solve_cross()
    target=Path(__file__).with_suffix('.json')
    target.write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:result[k] for k in ['case','original_phi','best_phi','original','best_partition']},indent=2))
