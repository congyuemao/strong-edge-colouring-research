"""Offline abstract probe: avoid A-edges in colour A and B-edges in colour B.

Each constraint graph has components P2 or P3. This is only an abstract
constraint test, not a realization in the original red/blue graph.
"""
import itertools, json, pathlib, time

def partitions_forest(vertices):
    if not vertices:
        yield []
        return
    v, *rest = vertices
    for w in rest:
        left = [x for x in rest if x != w]
        for tail in partitions_forest(left):
            yield [(v,w)] + tail
    for w,z in itertools.combinations(rest,2):
        left = [x for x in rest if x not in (w,z)]
        for center in (v,w,z):
            edges = [(center,x) for x in (v,w,z) if x != center]
            for tail in partitions_forest(left):
                yield edges + tail

def canonical_a(n, triples):
    pairs = (n-3*triples)//2
    if pairs < 0 or 2*pairs+3*triples != n:
        return None
    edges=[]
    i=0
    for _ in range(triples):
        edges += [(i,i+1),(i,i+2)]
        i += 3
    for _ in range(pairs):
        edges += [(i,i+1)]
        i += 2
    return edges

def indep_masks(n,edges):
    pairs=[(1<<a)|(1<<b) for a,b in edges]
    return [m for m in range(1<<n) if all(m&e!=e for e in pairs)]

def main():
    started=time.monotonic()
    counts=[]
    for n in range(2,11):
        for triples in range(n//3+1):
            a=canonical_a(n,triples)
            if a is None:
                continue
            candidates=indep_masks(n,a)
            tested=0
            for b in partitions_forest(list(range(n))):
                tested+=1
                bm=[(1<<x)|(1<<y) for x,y in b]
                if not any(all(m&e for e in bm) for m in candidates):
                    result={"n":n,"A":a,"B":b,"tested":tested,
                            "status":"abstract_monotone_2sat_unsatisfiable",
                            "A_independent_masks":candidates,
                            "earlier_counts":counts,
                            "elapsed":time.monotonic()-started}
                    out=pathlib.Path(__file__).with_suffix('.json')
                    out.write_text(json.dumps(result,indent=2),encoding='utf-8')
                    print(json.dumps(result),flush=True)
                    return
            counts.append([n,triples,tested])
            print(counts[-1],flush=True)
    print(json.dumps({"status":"no_counterexample_up_to_10", "counts":counts}))

if __name__=='__main__':
    main()
