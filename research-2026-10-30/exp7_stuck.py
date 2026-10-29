"""Experiment 7: look for 'stuck' states of the route-Q potential argument.

State: a partition of E(G) into K classes that is a local minimum of
Phi1 = #conflicting pairs inside classes.  Phi2 = #odd-cycle components.
Improving moves tried (each must keep every inside-degree <= 2):
  M1  move one edge (Phi1 not increased) so that (Phi1, Phi2) drops lexicographically;
  M2  move x out of class j, then move an odd-cycle edge e into j (two-move Kempe step).
A state with odd cycles and no M1/M2 improvement is 'stuck'; we record its local shape."""
import json
import random
import sys
import time
from collections import Counter

import networkx as nx

from exp4_local_search import conflict_adj
from graphs_hg import gq33_incidence, pg23_incidence, random_girth
from sec import blowup_cycle


class State:
    def __init__(self, E, adj, K, rng):
        self.E, self.adj, self.K, self.rng = E, adj, K, rng
        m = len(E)
        self.m = m
        self.part = [rng.randrange(K) for _ in range(m)]
        self.cnt = [[0] * K for _ in range(m)]
        for i in range(m):
            for w in adj[i]:
                self.cnt[i][self.part[w]] += 1

    def move(self, i, q):
        p = self.part[i]
        for w in self.adj[i]:
            self.cnt[w][p] -= 1
            self.cnt[w][q] += 1
        self.part[i] = q

    def own(self, i):
        return self.cnt[i][self.part[i]]

    def phi1(self):
        return sum(self.own(i) for i in range(self.m)) // 2

    def descend(self):
        ch = True
        while ch:
            ch = False
            for i in range(self.m):
                q = min(range(self.K), key=lambda c: (self.cnt[i][c], self.rng.random()))
                if self.cnt[i][q] < self.own(i):
                    self.move(i, q)
                    ch = True

    def comp(self, i):
        p = self.part[i]
        seen, st = {i}, [i]
        while st:
            v = st.pop()
            for w in self.adj[v]:
                if self.part[w] == p and w not in seen:
                    seen.add(w)
                    st.append(w)
        return seen

    def odd_cycles(self):
        seen, out = set(), []
        for i in range(self.m):
            if i in seen:
                continue
            c = self.comp(i)
            seen |= c
            if len(c) % 2 and all(self.own(v) == 2 for v in c):
                out.append(c)
        return out

    def maxdeg_ok(self, verts):
        return all(self.own(v) <= 2 for v in verts)


def touched(S, idxs):
    out = set(idxs)
    for i in idxs:
        out |= set(S.adj[i])
    return out


def try_improve(S):
    odd = S.odd_cycles()
    if not odd:
        return "done"
    base = (S.phi1(), len(odd))
    oddverts = [v for c in odd for v in c]
    S.rng.shuffle(oddverts)
    # M1
    for e in oddverts:
        p = S.part[e]
        for q in range(S.K):
            if q == p or S.cnt[e][q] > S.own(e):
                continue
            S.move(e, q)
            if S.maxdeg_ok(touched(S, [e])):
                new = (S.phi1(), len(S.odd_cycles()))
                if new < base:
                    return "M1"
            S.move(e, p)
    # M2
    for e in oddverts:
        p = S.part[e]
        for j in range(S.K):
            if j == p:
                continue
            xs = [x for x in S.adj[e] if S.part[x] == j]
            if len(xs) > 3:
                continue
            for x in xs:
                for k in range(S.K):
                    if k == j:
                        continue
                    S.move(x, k)
                    S.move(e, j)
                    if S.maxdeg_ok(touched(S, [e, x])):
                        new = (S.phi1(), len(S.odd_cycles()))
                        if new < base:
                            return "M2"
                    S.move(e, p)
                    S.move(x, j)
    return "stuck"


def describe(S, c, G):
    """Shape of a stuck odd cycle: length, original-graph span, zero-cost classes and their paths."""
    E = S.E
    edges = [E[v] for v in c]
    verts = set(x for e in edges for x in e)
    info = {"len": len(c), "G_vertices": len(verts), "G_edges_spanned": G.subgraph(verts).number_of_edges()}
    if len(c) == 3:
        common = set(edges[0]) & set(edges[1]) & set(edges[2])
        H = nx.Graph(edges)
        info["triangle_shape"] = "star" if common else ("path" if nx.is_connected(H) and max(dict(H.degree()).values()) == 2 and len(H) == 4 else
                                                         "other(" + ",".join(sorted(str(d) for _, d in H.degree())) + ")")
    zinfo = []
    for e in c:
        Z = [j for j in range(S.K) if j != S.part[e] and S.cnt[e][j] == 2]
        lens = []
        for j in Z:
            xs = [x for x in S.adj[e] if S.part[x] == j]
            comp = S.comp(xs[0])
            lens.append(len(comp) if xs[1] in comp else -1)
        zinfo.append({"Z": len(Z), "path_lengths": sorted(lens)})
    info["per_vertex"] = zinfo
    return info


def run(name, G, K, restarts, rng, max_rounds=400):
    E, adj = conflict_adj(G)
    stats = Counter()
    shapes = []
    for _ in range(restarts):
        S = State(E, adj, K, rng)
        S.descend()
        if not S.odd_cycles():
            stats["no_odd_after_descent"] += 1
            continue
        stuck_seen = False
        for r in range(max_rounds):
            res = try_improve(S)
            if res == "done":
                stats["solved_after_moves"] += 1
                break
            if res == "stuck":
                if not stuck_seen:
                    stuck_seen = True
                    stats["hit_stuck_state"] += 1
                    for c in S.odd_cycles():
                        shapes.append(describe(S, c, G))
                # random zero-cost drift
                e = rng.choice([v for c in S.odd_cycles() for v in c])
                opts = [q for q in range(K) if q != S.part[e] and S.cnt[e][q] <= S.own(e)]
                S.move(e, rng.choice(opts))
                S.descend()
        else:
            stats["failed"] += 1
    return stats, shapes


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    graphs = [("PG(2,3)-inc g6", pg23_incidence()), ("W(3)-inc g8", gq33_incidence()),
              ("rand30 g5", random_girth(30, 5, 1)), ("rand60 g6", random_girth(60, 6, 1)),
              ("C5[2] g4", blowup_cycle(5)), ("C11(1,3) g4", nx.circulant_graph(11, [1, 3]))]
    out = {}
    for K in (10, 9):
        for name, G in graphs:
            t0 = time.time()
            stats, shapes = run(name, G, K, restarts=30, rng=rng)
            print(f"K={K:2d} {name:16s} m={G.number_of_edges():4d} {dict(stats)}  [{time.time()-t0:.0f}s]", flush=True)
            sc = Counter((s["len"], s.get("triangle_shape", "")) for s in shapes)
            if sc:
                print("     stuck odd cycles (len, shape):", dict(sc))
                zc = Counter(tuple(sorted(pv["Z"] for pv in s["per_vertex"])) for s in shapes)
                print("     |Z| profiles:", dict(zc.most_common(5)))
                pc = Counter(l for s in shapes for pv in s["per_vertex"] for l in pv["path_lengths"])
                print("     path sizes in zero-cost classes:", dict(pc))
            out[f"{K}:{name}"] = {"stats": dict(stats), "shapes": shapes[:50]}
    json.dump(out, open("exp7_results.json", "w"), indent=1)
