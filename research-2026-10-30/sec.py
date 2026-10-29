"""Shared helpers: strong conflict graphs, SAT colouring, 2-factorizations."""
import itertools
import random

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153


def norm(e):
    u, v = e
    return (u, v) if u <= v else (v, u)


def conflict_graph(G, F):
    """Conflict graph on edge set F, conflicts judged in the full graph G."""
    F = [norm(e) for e in F]
    H = nx.Graph()
    H.add_nodes_from(F)
    for e, f in itertools.combinations(F, 2):
        a, b = e
        c, d = f
        if {a, b} & {c, d}:
            H.add_edge(e, f)
        elif any(G.has_edge(x, y) for x in (a, b) for y in (c, d)):
            H.add_edge(e, f)
    return H


def greedy_clique(H):
    best = []
    for v in sorted(H, key=H.degree, reverse=True)[:40]:
        C = [v]
        cand = set(H[v])
        while cand:
            w = max(cand, key=lambda x: len(cand & set(H[x])))
            C.append(w)
            cand &= set(H[w])
        if len(C) > len(best):
            best = C
    return best


def colourable(H, k, clique=None, extra=None):
    """SAT test of proper k-colouring of H. Returns colouring dict or None."""
    nodes = list(H)
    if k <= 0:
        return None if nodes else {}
    idx = {v: i for i, v in enumerate(nodes)}
    var = lambda v, c: idx[v] * k + c + 1
    s = Cadical153()
    for v in nodes:
        s.add_clause([var(v, c) for c in range(k)])
    for u, v in H.edges():
        for c in range(k):
            s.add_clause([-var(u, c), -var(v, c)])
    if clique is None:
        clique = greedy_clique(H)
    if len(clique) > k:
        s.delete()
        return None
    for c, v in enumerate(clique):
        s.add_clause([var(v, c)])
    ok = s.solve()
    col = None
    if ok:
        m = set(l for l in s.get_model() if l > 0)
        col = {v: next(c for c in range(k) if var(v, c) in m) for v in nodes}
    s.delete()
    return col


def chromatic(H, lo=None, hi=None):
    clique = greedy_clique(H)
    k = max(lo or 0, len(clique))
    while True:
        if hi is not None and k > hi:
            return None
        if colourable(H, k, clique):
            return k
        k += 1


def random_two_factorization(G, rng):
    """Alternate colours along a random Euler circuit of a connected 4-regular G."""
    start = rng.choice(list(G))
    # randomized Hierholzer
    rem = {v: list(G[v]) for v in G}
    for v in rem:
        rng.shuffle(rem[v])
    usedE = set()
    path = [start]
    circuit = []
    while path:
        v = path[-1]
        while rem[v] and norm((v, rem[v][-1])) in usedE:
            rem[v].pop()
        if rem[v]:
            u = rem[v].pop()
            usedE.add(norm((v, u)))
            path.append(u)
        else:
            circuit.append(path.pop())
    edges = [norm((circuit[i], circuit[i + 1])) for i in range(len(circuit) - 1)]
    assert len(edges) == G.number_of_edges()
    F1 = edges[0::2]
    F2 = edges[1::2]
    return F1, F2


def balanced_strong_colouring(G, k1=10, k2=10, timeout=None):
    """Strong (k1+k2)-colouring where colours < k1 form a 2-factor (2 per vertex)."""
    E = [norm(e) for e in G.edges()]
    H = conflict_graph(G, E)
    k = k1 + k2
    pool = IDPool()
    var = lambda e, c: pool.id(("x", e, c))
    s = Cadical153()
    for e in E:
        s.add_clause([var(e, c) for c in range(k)])
    for e, f in H.edges():
        for c in range(k):
            s.add_clause([-var(e, c), -var(f, c)])
    # red indicator r_e <-> colour < k1
    r = lambda e: pool.id(("r", e))
    for e in E:
        for c in range(k):
            s.add_clause([-var(e, c), r(e)] if c < k1 else [-var(e, c), -r(e)])
    top = pool.top  # all x/r variables exist by now
    for v in G:
        lits = [r(norm((v, u))) for u in G[v]]
        cnf = CardEnc.equals(lits=lits, bound=2, top_id=top, encoding=EncType.seqcounter)
        top = max(top, cnf.nv)
        for cl in cnf.clauses:
            s.add_clause(cl)
    ok = s.solve()
    res = None
    if ok:
        m = set(l for l in s.get_model() if l > 0)
        res = {e: next(c for c in range(k) if var(e, c) in m) for e in E}
    s.delete()
    return res


def blowup_cycle(k):
    """C_k[2]: vertices (i, s), (i,s)~(i+1,t)."""
    G = nx.Graph()
    for i in range(k):
        for s_ in range(2):
            for t in range(2):
                G.add_edge((i, s_), ((i + 1) % k, t))
    return nx.convert_node_labels_to_integers(G)
