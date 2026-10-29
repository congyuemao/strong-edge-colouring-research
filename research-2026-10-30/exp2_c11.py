import itertools, networkx as nx
from sec import *
G = nx.circulant_graph(11, [1, 3])
F = [(0, 3), (0, 8), (1, 4), (1, 9), (2, 5), (2, 10), (3, 6), (4, 7), (5, 6), (7, 8), (9, 10)]
H = conflict_graph(G, F)
print("F is 2-factor:", all(sum(v in e for e in F) == 2 for v in G), "cycles:", [len(c) for c in nx.connected_components(nx.Graph(F))])
print("H_F edges", H.number_of_edges(), "of", 11*10//2, "-> complete:", H.number_of_edges() == 55)
Fc = [norm(e) for e in G.edges() if norm(e) not in set(map(norm, F))]
Hc = conflict_graph(G, Fc); print("complement factor chi:", chromatic(Hc))
E = [norm(e) for e in G.edges()]
print("chi_s(C11(1,3)) =", chromatic(conflict_graph(G, E)))
# all 2-factors of G: enumerate subsets with degree 2 everywhere
fac = []
for S in itertools.combinations(E, 11):
    deg = [0]*11
    for u, v in S: deg[u] += 1; deg[v] += 1
    if all(d == 2 for d in deg): fac.append(S)
print("number of 2-factors:", len(fac))
from collections import Counter
chis = {frozenset(S): chromatic(conflict_graph(G, S)) for S in fac}
print("chi(H_F) distribution:", Counter(chis.values()))
good = [S for S in fac if chis[frozenset(S)] <= 10 and chis[frozenset(E) - frozenset(S)] <= 10]
print("2-factorizations with both sides <= 10:", len(good)//1)
print("balanced 10+10 strong colouring exists:", balanced_strong_colouring(G) is not None)
