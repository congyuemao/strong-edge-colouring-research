"""exp74: complete SAT search for a state in which every pair of colours fails (NEW_DIRECTIONS 11.28).
Variables: col(e, c) for e != h; M_Y(v) for each pair Y: a set containing h, avoiding colours of Y, each member tangled on Y and with at least
tau_Y(v) = 2(K - 2) - deg(v) + d_Y(v) neighbours in the set.  Such a set exists iff h is in the core C_Y.
Tangling needs connectivity, so it is handled lazily (CEGAR): the base formula only asks for an a- and a b-neighbour; when a model has a member that is not tangled, take
U = the (a, b) components of its a-neighbours and add the valid clause
   M_Y(v) -> some edge adjacent to U (outside U) is coloured from Y, or a neighbour of v outside U is coloured a, or a neighbour of v inside U is coloured b.
SAT with no violated member: a real counterexample, printed and saved.  UNSAT: no such state on this graph (and edge h).
mode "stuck": only ask that all pairs are tangled at h (M_Y = {h}, no core condition).
Usage: exp74_sat_core.py K mode seconds out.json files.json ..."""
import itertools, json, sys, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def l2(edges):
    inc, nb = {}, {}
    for i, (p, q) in enumerate(edges):
        inc.setdefault(p, set()).add(i); inc.setdefault(q, set()).add(i)
        nb.setdefault(p, set()).add(q); nb.setdefault(q, set()).add(p)
    adj = []
    for i, (p, q) in enumerate(edges):
        s = set(inc[p]) | set(inc[q])
        for w in nb[p] | nb[q]:
            s |= inc[w]
        s.discard(i); adj.append(s)
    return adj


def run(x, K, mode, secs, outfn):
    edges = [tuple(e) for e in x["edges"]]; h = x["e"]; adj = l2(edges); m = len(edges); t0 = time.time()
    pool = IDPool()
    C = lambda e, c: pool.id(("c", e, c))
    M = lambda Y, v: pool.id(("m", Y, v))
    s = Cadical153()
    cl = 0
    def add(c):
        nonlocal cl
        s.add_clause(c); cl += 1
    vs = [v for v in range(m) if v != h]
    for v in vs:
        add([C(v, c) for c in range(K)])
        for c, d in itertools.combinations(range(K), 2):
            add([-C(v, c), -C(v, d)])
        for y in adj[v]:
            if y > v and y != h:
                for c in range(K):
                    add([-C(v, c), -C(y, c)])
    # colour symmetry: a largest clique found greedily in N(h)
    clique = []
    for v in sorted(adj[h], key=lambda u: -len(adj[u] & adj[h])):
        if all(v in adj[u] for u in clique):
            clique.append(v)
    for i, v in enumerate(clique[:K]):
        add([C(v, i)])
    pairs = list(itertools.combinations(range(int(__import__("os").environ.get("SE_S", K))), 2))
    for Y in pairs:
        a, b = Y
        add([M(Y, h)])
        for v in range(m):
            if mode == "stuck" and v != h:
                continue
            mv = -M(Y, v)
            if v != h:
                add([mv, -C(v, a)]); add([mv, -C(v, b)])
            nv = [u for u in adj[v] if u != h]
            add([mv] + [C(u, a) for u in nv]); add([mv] + [C(u, b) for u in nv])
            if mode == "stuck":
                continue
            # sum_u M(u) - sum_u D(u) >= 2(K-2) - deg(v): use literals M(u) and not D(u), D(u) = col a or col b
            lits = []
            for u in adj[v]:
                lits.append(M(Y, u))
                if u == h:
                    lits.append(pool.id(("true",)))
                else:
                    d = pool.id(("d", Y, u))
                    add([-d, C(u, a), C(u, b)]); add([d, -C(u, a)]); add([d, -C(u, b)])
                    lits.append(-d)
            need = 2 * (K - 2) - len(adj[v]) + len(adj[v])
            enc = CardEnc.atleast(lits=lits, bound=need, vpool=pool, encoding=EncType.seqcounter)
            for c in enc.clauses:
                add(c + [mv])
    if ("true",) in pool.obj2id:
        add([pool.id(("true",))])
    print(f"{x.get('instance','?')}: m={m} deg h={len(adj[h])} clique {len(clique)} vars {pool.top} clauses {cl}", flush=True)
    rounds = lazy = 0
    while True:
        if time.time() - t0 > secs:
            print(f"   TIMEOUT rounds {rounds} lazy {lazy}", flush=True); s.delete(); return "timeout"
        if not s.solve():
            print(f"   UNSAT after {rounds} rounds, {lazy} lazy clauses, {time.time()-t0:.0f} s", flush=True); s.delete(); return "unsat"
        rounds += 1
        model = set(l for l in s.get_model() if l > 0)
        col = [-1] * m
        for v in vs:
            for c in range(K):
                if C(v, c) in model:
                    col[v] = c
        bad = 0
        for Y in pairs:
            a, b = Y
            comp = {}
            for t in range(m):
                if col[t] in Y and t not in comp:
                    comp[t] = t; st = [t]
                    while st:
                        u = st.pop()
                        for w in adj[u]:
                            if col[w] in Y and w not in comp:
                                comp[w] = t; st.append(w)
            for v in range(m):
                if not (v == h or (mode != "stuck" and M(Y, v) in model)):
                    continue
                A = [u for u in adj[v] if col[u] == a]; B = [u for u in adj[v] if col[u] == b]
                ca = {comp[u] for u in A}; cb = {comp[u] for u in B}
                if ca & cb:
                    continue
                bad += 1
                for (ours, oth, cs) in ((a, b, ca), (b, a, cb)):
                    U = {u for u in comp if comp[u] in cs}
                    bd = {w for u in U for w in adj[u]} - U - {h}
                    c = [-M(Y, v)]
                    for e in bd:
                        c += [C(e, a), C(e, b)]
                    for w in adj[v]:
                        if w == h:
                            continue
                        if w in U:
                            c.append(C(w, oth))
                        else:
                            c.append(C(w, ours))
                    add(c); lazy += 1
        if rounds % 50 == 0 or bad == 0:
            print(f"   round {rounds}: violated {bad}, lazy {lazy}, {time.time()-t0:.0f} s", flush=True)
        if bad == 0:
            y = {"edges": edges, "e": h, "colouring": col, "instance": x.get("instance", "?") + "_sat"}
            json.dump(y, open(outfn, "w"))
            print(f"   SAT: state written to {outfn}", flush=True); s.delete(); return "sat"


def main():
    K = int(sys.argv[1]); mode = sys.argv[2]; secs = float(sys.argv[3]); out = sys.argv[4]
    for i, fn in enumerate(sys.argv[5:]):
        data = json.load(open(fn))
        for j, x in enumerate(data if isinstance(data, list) else [data]):
            run(x, K, mode, secs, out.replace(".json", f"_{x.get('instance','s')}.json"))


main()
