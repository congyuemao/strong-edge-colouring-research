"""Experiment 4: Lovasz-style local search for property Q on L^2(G).

Potential = (#conflicts inside classes, #odd cycles inside classes).  Phase 1 moves an edge
to a class with strictly fewer conflicts (any local minimum has inside-degree <= 2, since
10*2 < 24 < 10*3).  Phase 2 picks an edge on an odd cycle and moves it to a class where its
inside degree stays 2 (zero-cost move), preferring moves that do not close a new odd cycle.
We record whether the search reaches Q and how many moves it needed."""
import random
import sys
import time

import networkx as nx

from sec import blowup_cycle, norm

K = 10


def conflict_adj(G):
    E = [norm(e) for e in G.edges()]
    idx = {e: i for i, e in enumerate(E)}
    inc = {v: [idx[norm((v, u))] for u in G[v]] for v in G}
    adj = [set() for _ in E]
    for i, (a, b) in enumerate(E):
        ends = {a, b}
        near = set(ends)
        for x in ends:
            near |= set(G[x])
        for w in near:
            for j in inc[w]:
                if j != i:
                    adj[i].add(j)
    return E, [list(s) for s in adj]


def component(i, part, adj):
    p = part[i]
    seen = {i}
    stack = [i]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if part[w] == p and w not in seen:
                seen.add(w)
                stack.append(w)
    return seen


def is_odd_cycle(comp, part, adj):
    if len(comp) % 2 == 0:
        return False
    return all(sum(1 for w in adj[v] if part[w] == part[v]) == 2 for v in comp)


def run(G, rng, max_moves=200000):
    E, adj = conflict_adj(G)
    m = len(E)
    part = [rng.randrange(K) for _ in range(m)]
    cnt = [[0] * K for _ in range(m)]
    for i in range(m):
        for w in adj[i]:
            cnt[i][part[w]] += 1

    def move(i, q):
        p = part[i]
        for w in adj[i]:
            cnt[w][p] -= 1
            cnt[w][q] += 1
        part[i] = q

    moves = 0

    def descend():
        nonlocal moves
        changed = True
        while changed:
            changed = False
            for i in range(m):
                p = part[i]
                q = min(range(K), key=lambda c: (cnt[i][c], rng.random()))
                if cnt[i][q] < cnt[i][p]:
                    move(i, q)
                    moves += 1
                    changed = True

    descend()
    while moves < max_moves:
        odd = []
        seen = set()
        for i in range(m):
            if i in seen or cnt[i][part[i]] != 2:
                continue
            comp = component(i, part, adj)
            seen |= comp
            if is_odd_cycle(comp, part, adj):
                odd.append(comp)
        if not odd:
            assert max(cnt[i][part[i]] for i in range(m)) <= 2
            return True, moves
        comp = list(rng.choice(odd))
        rng.shuffle(comp)
        done = False
        for i in comp:
            opts = [q for q in range(K) if q != part[i] and cnt[i][q] <= 2]
            rng.shuffle(opts)
            for q in opts:
                old = part[i]
                move(i, q)
                c2 = component(i, part, adj)
                bad = max(cnt[w][q] for w in c2) > 2 or is_odd_cycle(c2, part, adj)
                if not bad:
                    moves += 1
                    done = True
                    break
                move(i, old)
            if done:
                break
        if not done:
            # random zero-cost move then re-descend (Kempe-like drift)
            i = comp[0]
            opts = [q for q in range(K) if q != part[i] and cnt[i][q] <= 2]
            move(i, rng.choice(opts))
            moves += 1
        descend()
    return False, moves


def families(rng):
    yield "C5[2]", blowup_cycle(5)
    yield "C11(1,3)", nx.circulant_graph(11, [1, 3])
    for k in (7, 9, 15, 51):
        yield f"C{k}[2]", blowup_cycle(k)
    for n in (20, 50, 100, 200, 500, 1000, 2000):
        for _ in range(5):
            yield f"rand{n}", nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
    # many disjoint-ish copies of C5[2] minus an edge glued in a ring (dense, near-tight)
    for r in (3, 10, 40):
        G = nx.Graph()
        a, b = next(iter(blowup_cycle(5).edges()))
        for t in range(r):
            H = nx.relabel_nodes(blowup_cycle(5), lambda v: (t, v))
            G.add_edges_from(H.edges())
            G.remove_edge((t, a), (t, b))
        for t in range(r):
            G.add_edge((t, b), ((t + 1) % r, a))
        yield f"ring{r}xC5[2]-e", G


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    for name, G in families(rng):
        assert max(d for _, d in G.degree()) <= 4
        t0 = time.time()
        ok, mv = run(G, rng)
        print(f"{name:18s} m={G.number_of_edges():5d}  Q reached={ok}  moves={mv}  [{time.time()-t0:.1f}s]", flush=True)
