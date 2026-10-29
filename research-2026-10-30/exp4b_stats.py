"""Instrumented version of exp4: odd cycles after first descent, phase-2 work, and a 9-class control."""
import random, sys, time
import networkx as nx
import exp4_local_search as X
from sec import blowup_cycle

def odd_cycles(part, cnt, adj, m):
    seen=set(); n=0
    for i in range(m):
        if i in seen or cnt[i][part[i]]!=2: continue
        c=X.component(i,part,adj); seen|=c
        if X.is_odd_cycle(c,part,adj): n+=1
    return n

def run(G, rng, K, max_rounds=20000):
    X.K = K
    E, adj = X.conflict_adj(G); m=len(E)
    part=[rng.randrange(K) for _ in range(m)]
    cnt=[[0]*K for _ in range(m)]
    for i in range(m):
        for w in adj[i]: cnt[i][part[w]]+=1
    def move(i,q):
        p=part[i]
        for w in adj[i]: cnt[w][p]-=1; cnt[w][q]+=1
        part[i]=q
    def descend():
        ch=True
        while ch:
            ch=False
            for i in range(m):
                q=min(range(K),key=lambda c:(cnt[i][c],rng.random()))
                if cnt[i][q]<cnt[i][part[i]]: move(i,q); ch=True
    descend()
    first=odd_cycles(part,cnt,adj,m); rounds=0; drifts=0
    while rounds<max_rounds:
        odd=[]; seen=set()
        for i in range(m):
            if i in seen or cnt[i][part[i]]!=2: continue
            c=X.component(i,part,adj); seen|=c
            if X.is_odd_cycle(c,part,adj): odd.append(c)
        if not odd: return dict(ok=True, odd_after_descent=first, rounds=rounds, drifts=drifts, maxdeg=max(cnt[i][part[i]] for i in range(m)))
        rounds+=1
        comp=list(rng.choice(odd)); rng.shuffle(comp); done=False
        for i in comp:
            opts=[q for q in range(K) if q!=part[i] and cnt[i][q]<=cnt[i][part[i]]]; rng.shuffle(opts)
            for q in opts:
                old=part[i]; move(i,q); c2=X.component(i,part,adj)
                if max(cnt[w][q] for w in c2)<=2 and not X.is_odd_cycle(c2,part,adj): done=True; break
                move(i,old)
            if done: break
        if not done:
            i=comp[0]; opts=[q for q in range(K) if q!=part[i] and cnt[i][q]<=cnt[i][part[i]]]
            if opts: move(i,rng.choice(opts))
            drifts+=1
        descend()
    return dict(ok=False, odd_after_descent=first, rounds=rounds, drifts=drifts)

rng=random.Random(11)
tests=[("C5[2]",blowup_cycle(5)),("C11(1,3)",nx.circulant_graph(11,[1,3])),("C7[2]",blowup_cycle(7))]
tests+=[(f"rand{n}",nx.random_regular_graph(4,n,seed=rng.randrange(10**9))) for n in (50,500,2000)]
for K in (10,9):
    print(f"--- {K} classes ({2*K} colours)")
    for name,G in tests:
        for trial in range(3):
            r=run(G,rng,K, max_rounds=3000)
            print(f"{name:10s} trial{trial}: {r}", flush=True)
