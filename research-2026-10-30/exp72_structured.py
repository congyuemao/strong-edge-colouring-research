"""exp72: structured cubic graphs for the Delta = 3 test (NEW_DIRECTIONS 11.28).  Writes .in/.json starting states as exp66_gen, one per edge orbit representative (sampled).
Families: generalized Petersen, Moebius ladders, prisms, honeycomb tori, cube-connected cycles, random lifts of small graphs.
Usage: exp72_structured.py outdir"""
import json, random, sys
import networkx as nx
from exp66_gen_lib import l2, tabu
K = 10
def gp(n, k):
    G = nx.Graph()
    for i in range(n):
        G.add_edge(('o', i), ('o', (i + 1) % n)); G.add_edge(('o', i), ('i', i)); G.add_edge(('i', i), ('i', (i + k) % n))
    return G
def moebius(n):
    G = nx.circulant_graph(2 * n, [1]); 
    for i in range(n): G.add_edge(i, i + n)
    return G
def torus_hex(a, b):
    G = nx.Graph()
    for i in range(a):
        for j in range(b):
            G.add_edge(('w', i, j), ('b', i, j)); G.add_edge(('w', i, j), ('b', (i + 1) % a, j)); G.add_edge(('w', i, j), ('b', i, (j + 1) % b))
    return G
def ccc(d):
    G = nx.Graph()
    for x in range(1 << d):
        for i in range(d):
            G.add_edge((x, i), (x, (i + 1) % d)); G.add_edge((x, i), (x ^ (1 << i), i))
    return G
def lift(B, r, rnd):
    G = nx.Graph()
    for u, v in B.edges():
        p = list(range(r)); rnd.shuffle(p)
        for i in range(r): G.add_edge((u, i), (v, p[i]))
    return G
def main():
    out = sys.argv[1]; rnd = random.Random(72); fam = {}
    for n, k in [(10, 2), (10, 3), (12, 5), (13, 5), (14, 3), (15, 4), (16, 3), (16, 7), (18, 5), (20, 7), (24, 5), (24, 7), (25, 7), (30, 7), (30, 11)]: fam[f"gp{n}_{k}"] = gp(n, k)
    for n in [10, 14, 20, 30]: fam[f"mob{n}"] = moebius(n)
    for n in [10, 15, 30]: fam[f"prism{n}"] = nx.circular_ladder_graph(n)
    for a, b in [(3, 5), (4, 5), (5, 5), (5, 6), (6, 6), (7, 7)]: fam[f"hex{a}_{b}"] = torus_hex(a, b)
    fam["ccc3"] = ccc(3); fam["ccc4"] = ccc(4); fam["ccc5"] = ccc(5)
    pet = nx.petersen_graph(); hw = nx.heawood_graph(); wag = nx.moebius_kantor_graph(); dod = nx.dodecahedral_graph(); tut = nx.tutte_graph() if False else nx.desargues_graph()
    for name, B in [("pet", pet), ("heawood", hw), ("mk", wag), ("dod", dod), ("des", tut), ("k33", nx.complete_bipartite_graph(3, 3)), ("k4", nx.complete_graph(4))]:
        fam[name] = B
        for r in [2, 3, 4]:
            for s in range(2):
                L = lift(B, r, rnd)
                if nx.is_connected(L): fam[f"{name}_l{r}_{s}"] = L
    for name, G in fam.items():
        if not nx.is_connected(G) or any(d != 3 for _, d in G.degree()): continue
        G = nx.convert_node_labels_to_integers(G)
        edges = [tuple(sorted(e)) for e in G.edges()]; adj = l2(edges)
        top = [v for v in range(len(edges)) if len(adj[v]) == max(map(len, adj))]
        for i in range(2):
            h = rnd.choice(top)
            col = None
            for _ in range(5):
                col = tabu(adj, h, rnd)
                if col: break
            if col is None: print(name, "no colouring"); break
            tag = f"{out}/{name}_h{i}"
            with open(tag + ".in", "w") as f:
                f.write(f"{len(edges)} {h} {len(edges)}\n" + " ".join(map(str, col)) + "\n" + " ".join(map(str, range(len(edges)))) + "\n")
                for r in adj: f.write(f"{len(r)} " + " ".join(map(str, sorted(r))) + "\n")
            json.dump({"edges": edges, "e": h, "colouring": col, "instance": f"{name}_h{i}"}, open(tag + ".json", "w"))
        print(name, "n", G.number_of_nodes(), "m", len(edges), "deg", len(adj[h]), "girth", nx.girth(G), flush=True)
main()
