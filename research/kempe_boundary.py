"""A tight three-edge extension obstruction with all T edges individually frozen.

This is a tree and is NOT a counterexample to 20 colors.  The fixed coloring
after deleting its degree-three root cannot be extended without recoloring.
No network access or third-party packages are used.
"""


def build():
    edges = []
    colors = []
    t_edges = []
    root_edges = []

    def add(u, v, color):
        edges.append((u, v))
        colors.append(color)
        return len(edges) - 1

    palette = set(range(1, 21))
    for i in range(3):
        u = ("u", i)
        root_edges.append(add(("v",), u, None))
        s_branch = set(range(3 * i + 1, 3 * i + 4))
        for j in range(3):
            w = ("w", i, j)
            add(u, w, 3 * i + j + 1)
            t_local = set(range(10 + 3 * j, 13 + 3 * j))
            missing = sorted(palette - s_branch - t_local)
            l_colors, r_colors = missing[:9], missing[9:]
            assert len(l_colors) == 9 and len(r_colors) == 5
            for k in range(3):
                z = ("z", i, j, k)
                t_edges.append(add(w, z, 10 + 3 * j + k))
                for ell in range(3):
                    q = ("q", i, j, k, ell)
                    add(z, q, l_colors[3 * k + ell])
                    for r in range(3):
                        leaf = ("leaf", i, j, k, ell, r)
                        add(q, leaf, r_colors[(3 * ell + r) % 5])
    return edges, colors, t_edges, root_edges


def verify():
    edges, colors, t_edges, root_edges = build()
    adjacency = {}
    for u, v in edges:
        adjacency.setdefault(u, set()).add(v)
        adjacency.setdefault(v, set()).add(u)

    def conflict(i, j):
        return any(u == v or v in adjacency[u]
                   for u in edges[i] for v in edges[j])

    neighbors = [set() for _ in edges]
    for i in range(len(edges)):
        for j in range(i):
            if conflict(i, j):
                neighbors[i].add(j)
                neighbors[j].add(i)
                assert colors[i] is None or colors[j] is None or colors[i] != colors[j]

    palette = set(range(1, 21))
    for e in root_edges:
        seen = {colors[f] for f in neighbors[e] if colors[f] is not None}
        assert palette - seen == {19, 20}
    for e in t_edges:
        seen = {colors[f] for f in neighbors[e] if colors[f] is not None}
        assert seen == palette - {colors[e]}

    # An explicit repair: interchange 10 and 19 in the component of the
    # first T edge.  It stays in the first branch of this tree.
    repaired = list(colors)
    component = {t_edges[0]}
    stack = [t_edges[0]]
    while stack:
        e = stack.pop()
        for f in neighbors[e]:
            if repaired[f] in {10, 19} and f not in component:
                component.add(f)
                stack.append(f)
    for e in component:
        repaired[e] = 29 - repaired[e]
    for e, c in zip(root_edges, [10, 19, 20]):
        assert c not in {repaired[f] for f in neighbors[e]}
        repaired[e] = c
    for e, ns in enumerate(neighbors):
        assert all(repaired[e] != repaired[f] for f in ns)

    print("vertices:", len(adjacency))
    print("edges:", len(edges))
    print("maximum degree:", max(map(len, adjacency.values())))
    print("proper partial strong coloring: verified")
    print("root lists: {19,20} on each of three pairwise-conflicting edges")
    print("individually frozen T edges:", len(t_edges))
    print("Kempe component size:", len(component))
    print("explicit complete 20-color repair: verified")
    print("This is a tree, not a counterexample.")


if __name__ == "__main__":
    verify()
