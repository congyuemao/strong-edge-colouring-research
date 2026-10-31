"""exp40: independent check of the depth-1 stuck states found by exp38 (one-pair KIL counterexamples).

Everything is recomputed with networkx, without exp33's code: the conflict graph is the square of the line graph
(two edges conflict iff they are at distance <= 2 in L(G)); the colouring must be proper on it (e uncoloured),
e must be blocked (all 20 colours on its conflict set), and for every colour pair (a, b) some component of the
subgraph spanned by colours a, b must meet both the a- and the b-coloured conflicts of e.  The depth-2 repair
found by exp33's depth_two is then replayed: the first swap, then the swaps of the one-pair move, and the result
must be proper with a colour free at e.

Usage: exp40_verify_stuck.py <found.jsonl> <hunt outdir> [out.json]
"""
import json
import sys

import networkx as nx

from exp33_kempe import depth_two
from exp38_gpu_adversary import build_instances, parse_specs

K = 20


def check(edges, e, col):
    G = nx.Graph(edges)
    L2 = nx.power(nx.line_graph(G), 2)
    eid = {tuple(sorted(x)): i for i, x in enumerate(edges)}
    nbr = {i: set() for i in range(len(edges))}
    for x, y in L2.edges():
        i, j = eid[tuple(sorted(x))], eid[tuple(sorted(y))]
        nbr[i].add(j)
        nbr[j].add(i)
    info = {"vertices": G.number_of_nodes(), "edges": G.number_of_edges(),
            "degrees": sorted(set(dict(G.degree()).values())), "girth": nx.girth(G), "connected": nx.is_connected(G),
            "conflicts of e": len(nbr[e])}
    proper = all(col[i] != col[j] for i in nbr for j in nbr[i] if i != e and j != e)
    coloured = all(0 <= col[i] < K for i in range(len(edges)) if i != e) and col[e] == -1
    blocked = len({col[f] for f in nbr[e]}) == K
    separable = []
    for a in range(K):
        for b in range(a + 1, K):
            H = nx.Graph()
            H.add_nodes_from(i for i in nbr if i != e and col[i] in (a, b))
            H.add_edges_from((i, j) for i in H for j in nbr[i] if j in H)
            ok = True
            for comp in nx.connected_components(H):
                cs = {col[f] for f in comp if f in nbr[e]}
                if cs == {a, b}:
                    ok = False
                    break
            if ok:
                separable.append((a, b))
    info.update(proper=proper, all_coloured=coloured, blocked=blocked, separable_pairs=separable)
    return info, nbr


def replay(nbr, e, col, rep):
    (a, b, comp), (c, d, comps) = rep
    c1 = list(col)
    for x in comp:
        c1[x] = b if c1[x] == a else a
    for cc in comps:
        for x in cc:
            c1[x] = d if c1[x] == c else c
    proper = all(c1[i] != c1[j] for i in nbr for j in nbr[i] if i != e and j != e)
    free = sorted(set(range(K)) - {c1[f] for f in nbr[e]})
    return proper, free


if __name__ == "__main__":
    found, hunt = sys.argv[1], sys.argv[2]
    meta = json.load(open(f"{hunt}/meta.json", encoding="utf-8"))["meta"]
    insts = {x["name"]: x for x in build_instances(parse_specs(meta["spec"]))}
    out = []
    for line in open(found, encoding="utf-8"):
        r = json.loads(line)
        x = insts[r["instance"]]
        edges, e, col = x["edges"], x["e"], r["colouring"]
        info, nbr = check(edges, e, col)
        stuck = info["proper"] and info["all_coloured"] and info["blocked"] and not info["separable_pairs"]
        rep = depth_two([sorted(nbr[i]) for i in range(len(edges))], list(col), e)
        rp = replay(nbr, e, col, rep) if rep else None
        print(f"{r['instance']} chain {r['chain']}: {info}; depth-1 stuck: {stuck}; depth-2 repair: "
              + (f"swap {rep[0][:2]} on {len(rep[0][2])} edges, then pair {rep[1][:2]} -> proper {rp[0]}, "
                 f"free colours {rp[1]}" if rep else "none"))
        out.append({"instance": r["instance"], "spec": x["spec"], "edges": edges, "e": e, "colouring": col,
                    "check": {k: v for k, v in info.items() if k != "separable_pairs"}, "depth1_stuck": stuck,
                    "depth2_repair": None if not rep else {"first_swap": {"pair": rep[0][:2], "edges": rep[0][2]},
                                                           "then_pair": rep[1][:2], "swapped": rep[1][2],
                                                           "proper_after": rp[0], "free_at_e": rp[1]}})
    if len(sys.argv) > 3:
        json.dump(out, open(sys.argv[3], "w", encoding="utf-8"), indent=1)
