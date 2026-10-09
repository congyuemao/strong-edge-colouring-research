"""Independent constructive verification of the derived 22-colour bound.

Standard library only.  Random experiments are tests, not a proof over
all graphs.  Every emitted colouring is checked against the original
endpoint definition by a separate verifier.
"""
from collections import Counter, deque
from itertools import combinations, product
from pathlib import Path
import json
import random


def edge(u, v):
    return (min(u, v), max(u, v))


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    assert max(map(len, adj), default=0) <= 4
    return adj


def conflicts(adj, edges):
    incident = [set() for _ in adj]
    for i, (u, v) in enumerate(edges):
        incident[u].add(i)
        incident[v].add(i)
    out = []
    for i, (u, v) in enumerate(edges):
        nearby = {u, v} | adj[u] | adj[v]
        out.append(set().union(*(incident[x] for x in nearby)) - {i})
    return out


def verify(adj, edges, colours):
    assert len(edges) == len(colours)
    assert all(isinstance(c, int) and c >= 0 for c in colours)
    for i, (u, v) in enumerate(edges):
        for j in range(i):
            x, y = edges[j]
            conflict = (bool({u, v} & {x, y}) or x in adj[u]
                        or y in adj[u] or x in adj[v] or y in adj[v])
            assert not conflict or colours[i] != colours[j], (i, j)


def four_count(adj, u, v):
    return sum(y in adj[x] for x in adj[u] - {v}
               for y in adj[v] - {u})


def constructive(adj):
    edges = sorted((u, v) for u in range(len(adj)) for v in adj[u] if u < v)
    conflict = conflicts(adj, edges)
    colours = [-1] * len(edges)
    modes = []
    unseen = set(range(len(adj)))
    while unseen:
        comp = {next(iter(unseen))}
        todo = list(comp)
        while todo:
            u = todo.pop()
            for v in adj[u] - comp:
                comp.add(v)
                todo.append(v)
        unseen -= comp
        ids = [i for i, (u, _) in enumerate(edges) if u in comp]
        if not ids:
            continue
        deficient = [u for u in comp if len(adj[u]) < 4]
        pre = ()
        if deficient:
            root, k, mode = min(deficient), 21, "nonregular"
        else:
            k = 22
            triangle = [u for u in comp if any(y in adj[x]
                        for x, y in combinations(adj[u], 2))]
            if triangle:
                root, mode = min(triangle), "triangle"
            else:
                counts = {i: four_count(adj, *edges[i]) for i in ids}
                many = [i for i in ids if counts[i] >= 2]
                one = [i for i in ids if counts[i] == 1]
                if many:
                    root = edges[many[0]][0]
                    size, mode = 2, "multiple_four_cycles"
                elif one:
                    root = edges[one[0]][0]
                    size, mode = 3, "linear_four_cycles"
                else:
                    root = min(comp)
                    size, mode = 4, "girth_at_least_five"
                boundary = [i for i in ids if root not in edges[i]
                            and any(u in adj[root] for u in edges[i])]
                pre = next((es for es in combinations(boundary, size)
                            if all(j not in conflict[i]
                                   for i, j in combinations(es, 2))), None)
                if pre is None and size == 2:
                    # The boundary is a clique.  The proved local lemma
                    # gives >=3 four-cycles through every root edge.
                    assert all(four_count(adj, root, u) >= 3 for u in adj[root])
                    pre = (boundary[0],)
                    mode = "boundary_clique"
                assert pre is not None, (mode, root, boundary)
        for i in pre:
            colours[i] = 0
        dist = {root: 0}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    queue.append(v)
        star = [i for i in ids if root in edges[i]]
        order = sorted((i for i in ids if i not in star and i not in pre),
                       key=lambda i: (-min(dist[u] for u in edges[i]), i))
        for i in order:
            forbidden = {colours[j] for j in conflict[i]} - {-1}
            available = set(range(k)) - forbidden
            assert available, (mode, edges[i], len(forbidden))
            colours[i] = min(available)

        def finish(remaining):
            if not remaining:
                return True
            lists = {i: set(range(k)) - {colours[j] for j in conflict[i]}
                     for i in remaining}
            i = min(remaining, key=lambda x: len(lists[x]))
            for c in sorted(lists[i]):
                colours[i] = c
                if finish([j for j in remaining if j != i]):
                    return True
            colours[i] = -1
            return False

        assert finish(star), (mode, root)
        modes.append(mode)
    verify(adj, edges, colours)
    return edges, colours, modes


def dsatur(adj, edges):
    conflict = conflicts(adj, edges)
    colours = [-1] * len(edges)
    seen = [set() for _ in edges]
    for _ in edges:
        i = max((i for i, c in enumerate(colours) if c < 0),
                key=lambda i: (len(seen[i]), len(conflict[i]), -i))
        c = 0
        while c in seen[i]:
            c += 1
        colours[i] = c
        for j in conflict[i]:
            seen[j].add(c)
    verify(adj, edges, colours)
    return colours


def regular(n, rng, bipartite=False):
    if bipartite:
        assert n % 2 == 0 and n >= 8
        half = n // 2
        es = {edge(i, half + (i + d) % half)
              for i in range(half) for d in range(4)}
    else:
        es = {edge(i, (i + d) % n) for i in range(n) for d in (1, 2)}
    for _ in range(30 * n):
        a, b = rng.sample(sorted(es), 2)
        u, v = a
        x, y = b
        if not bipartite and rng.randrange(2):
            x, y = y, x
        if len({u, v, x, y}) < 4:
            continue
        c, d = edge(u, y), edge(x, v)
        if c in es or d in es:
            continue
        es.remove(a)
        es.remove(b)
        es.add(c)
        es.add(d)
    return graph(n, es)


def blowup5():
    return graph(10, {edge(2 * i + x, 2 * ((i + 1) % 5) + y)
                      for i in range(5) for x in range(2) for y in range(2)})


def finite_plane():
    # Normalised nonzero triples over F_3; dot product gives incidence.
    vectors = [v for v in product(range(3), repeat=3)
               if any(v) and next(x for x in v if x) == 1]
    assert len(vectors) == 13
    return graph(26, {(i, 13 + j) for i, p in enumerate(vectors)
                      for j, line in enumerate(vectors)
                      if sum(a * b for a, b in zip(p, line)) % 3 == 0})


def cycle_medial(adj):
    # One vertex per old edge; the four incidences at each old vertex
    # become a four-cycle.  A base of girth >=5 introduces no other C4.
    es = sorted((u, v) for u in range(len(adj)) for v in adj[u] if u < v)
    new_edges = set()
    for v in range(len(adj)):
        ids = [i for i, e in enumerate(es) if v in e]
        assert len(ids) == 4
        new_edges.update(edge(ids[i], ids[(i + 1) % 4]) for i in range(4))
    return graph(len(es), new_edges)


def join_copies_with_square(adj):
    # Four disjoint copies, cut one edge in each, and connect its two
    # endpoints to one new square vertex.  Every degree stays four.
    # Each new root is in just that square; the two remaining ports
    # enter the same distant copy and cannot create a short cycle.
    n = len(adj)
    es = {(u, v) for u in range(n) for v in adj[u] if u < v}
    cut = min(es)
    es.remove(cut)
    out = set()
    for i in range(4):
        out.update((u + n * i, v + n * i) for u, v in es)
        out.update(edge(x + n * i, 4 * n + i) for x in cut)
        out.add(edge(4 * n + i, 4 * n + (i + 1) % 4))
    return graph(4 * n + 4, out)


def main():
    rng = random.Random(20261008)
    plane = finite_plane()
    samples = [blowup5(), plane, cycle_medial(plane), join_copies_with_square(plane)]
    for n in (5, 6, 7, 8, 10, 11, 12, 16, 20, 30, 50, 80):
        samples.extend(regular(n, rng) for _ in range(20))
    for n in (8, 10, 12, 16, 20, 30, 50, 80):
        samples.extend(regular(n, rng, True) for _ in range(20))
    # Delete vertices, not just edges: keep original conflict semantics
    # exactly for the new graph, and test the nonregular ordering.
    for _ in range(50):
        adj = regular(30, rng)
        for u in list(adj[0]):
            adj[u].remove(0)
        adj[0].clear()
        samples.append(adj)
    mode_counts = Counter()
    used_counts = Counter()
    greedy_counts = Counter()
    certificates = []
    for index, adj in enumerate(samples):
        es, cs, modes = constructive(adj)
        greedy = dsatur(adj, es)
        mode_counts.update(modes)
        used_counts[max(cs, default=-1) + 1] += 1
        greedy_counts[max(greedy, default=-1) + 1] += 1
        certificates.append({"sample": index, "n": len(adj), "edges": es,
                             "bound22_colours": cs, "dsatur_colours": greedy})
    tight = samples[0]
    tight_edges = certificates[0]["edges"]
    assert len(tight_edges) == 20
    assert all(len(x) == 19 for x in conflicts(tight, tight_edges))
    summary = {"seed": 20261008, "samples": len(samples),
               "construction_modes": dict(mode_counts),
               "constructive_colour_histogram": dict(sorted(used_counts.items())),
               "dsatur_colour_histogram": dict(sorted(greedy_counts.items())),
               "tight_example_edges": 20,
               "all_certificates_independently_checked": True}
    folder = Path(__file__).parent
    (folder / "colouring_experiments.json").write_text(
        json.dumps(summary, indent=2), encoding="utf-8")
    (folder / "colouring_certificates.json").write_text(
        json.dumps(certificates, separators=(",", ":")), encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
