"""Construct and independently verify a one-Kempe-stable extension obstruction.

This searches for an obstruction to a LOCAL METHOD, not to 20-colorability.
Only the Python standard library is used. No network access.
"""
from collections import deque
from itertools import combinations, product
import json
from pathlib import Path


class ColoredGraph:
    def __init__(self):
        self.edges = []
        self.colors = []
        self.adj = []
        self.inc = []
        self.protected = set()

    def vertex(self):
        self.adj.append(set())
        self.inc.append(set())
        return len(self.adj) - 1

    def legal(self, u, v, color):
        if u in self.protected or v in self.protected:
            return False
        if u == v or v in self.adj[u] or len(self.adj[u]) >= 4 or len(self.adj[v]) >= 4:
            return False
        if any(self.colors[e] is not None and self.colors[e] == self.colors[f]
               for e in self.inc[u] for f in self.inc[v]):
            return False
        if color is not None:
            for x in {u, v} | self.adj[u] | self.adj[v]:
                if any(self.colors[e] == color for e in self.inc[x]):
                    return False
        return True

    def add(self, u, v, color):
        assert self.legal(u, v, color), (u, v, color)
        e = len(self.edges)
        self.edges.append((u, v))
        self.colors.append(color)
        self.adj[u].add(v)
        self.adj[v].add(u)
        self.inc[u].add(e)
        self.inc[v].add(e)
        return e

    def conflicts(self, e):
        u, v = self.edges[e]
        result = set()
        for x in {u, v} | self.adj[u] | self.adj[v]:
            result.update(self.inc[x])
        result.discard(e)
        return result

    def components(self, pair):
        remaining = {e for e, c in enumerate(self.colors) if c in pair}
        parts = []
        where = {}
        while remaining:
            start = min(remaining)
            todo = [start]
            remaining.remove(start)
            part = {start}
            while todo:
                e = todo.pop()
                for f in self.conflicts(e) & remaining:
                    if self.colors[f] in pair:
                        remaining.remove(f)
                        part.add(f)
                        todo.append(f)
            index = len(parts)
            for e in part:
                where[e] = index
            parts.append(part)
        return parts, where


def initial_graph():
    g = ColoredGraph()
    v = g.vertex()
    roots = []
    spokes = {}
    t_edges = {}
    terminal_records = []
    palette = set(range(1, 21))
    for i in range(3):
        u = g.vertex()
        roots.append(g.add(v, u, None))
        s_branch = set(range(3 * i + 1, 3 * i + 4))
        for j in range(3):
            w = g.vertex()
            s = 3 * i + j + 1
            spokes[s] = g.add(u, w, s)
            t_local = set(range(10 + 3 * j, 13 + 3 * j))
            missing = sorted(palette - s_branch - t_local)
            l_colors, rest = missing[:9], missing[9:]
            for k in range(3):
                z = g.vertex()
                t = 10 + 3 * j + k
                t_edges[i, t] = g.add(w, z, t)
                # Four deliberately repeated colors give each local bichromatic
                # pair access to outward leaves: all three spoke colors, plus
                # one of the other two T colors, in a cyclic pattern.
                r_colors = rest + sorted(s_branch) + [10 + 3 * j + (k + 1) % 3]
                assert len(set(r_colors)) == 9
                for ell in range(3):
                    q = g.vertex()
                    g.add(z, q, l_colors[3 * k + ell])
                    for r in range(3):
                        leaf = g.vertex()
                        g.add(q, leaf, r_colors[3 * ell + r])
                        terminal_records.append((leaf, q, t, sorted(t_local),
                                                 l_colors[3 * k:3 * k + 3]))

    # Supply color-pair-specific outward ports before any bridges can consume
    # the original leaves.  Every terminal sees at most one of the three
    # local T colors at its parent, so at least two direct branches fit.
    for leaf, q, own_t, local_ts, local_ls in terminal_records:
        parent_colors = {g.colors[e] for e in g.inc[q]}
        ports = {}
        for t in local_ts:
            if t not in parent_colors:
                x = g.vertex()
                g.add(leaf, x, t)
                ports[t] = x
        fan_t = next(t for t in ports if t != own_t)
        for c in local_ls:
            y = g.vertex()
            g.add(ports[fan_t], y, c)
    g.protected.add(v)
    return g, roots, spokes, t_edges


def obtain_leaf_port(g, component, pair):
    """Return (edge, leaf) in the selected bichromatic component.

    Prefer an existing leaf. Otherwise extend from a low-degree vertex in
    the component's physical neighborhood; every addition is checked.
    """
    for e in sorted(component):
        for x in g.edges[e]:
            if len(g.adj[x]) == 1:
                # Clone a fresh port rather than consuming the old leaf in a
                # bridge.  The old endpoint keeps spare capacity for other
                # color pairs, which is essential to this construction.
                opposite = next(c for c in pair if c != g.colors[e])
                a, b = g.vertex(), g.vertex()
                side = next(c for c in range(1, 21)
                            if c not in pair and g.legal(x, a, c))
                g.add(x, a, side)
                fresh = g.add(a, b, opposite)
                return fresh, b
    candidates = set()
    for e in component:
        for x in g.edges[e]:
            candidates.add(x)
            candidates.update(g.adj[x])
    for x in sorted(candidates):
        if len(g.adj[x]) >= 4:
            continue
        new = g.vertex()
        for c in sorted(pair):
            if g.legal(x, new, c):
                visible = set()
                for y in {x} | g.adj[x]:
                    visible.update(g.inc[y])
                if any(e in visible and g.colors[e] != c for e in component):
                    edge = g.add(x, new, c)
                    return edge, new
        # Leave no unused isolated vertex in the construction.
        g.adj.pop()
        g.inc.pop()
    # A two-edge extension can reach a component edge from its endpoint.
    for e in sorted(component):
        target = next(c for c in pair if c != g.colors[e])
        for x in g.edges[e]:
            if len(g.adj[x]) >= 4 or any(g.colors[f] == target for f in g.inc[x]):
                continue
            a = g.vertex()
            b = g.vertex()
            for side in range(1, 21):
                if side in pair or not g.legal(x, a, side):
                    continue
                g.add(x, a, side)
                edge = g.add(a, b, target)
                return edge, b
            g.adj.pop()
            g.inc.pop()
            g.adj.pop()
            g.inc.pop()
    return None


def join_ports(g, first, second, pair):
    e, x = first
    f, y = second
    c, d = g.colors[e], g.colors[f]
    assert len(g.adj[x]) == len(g.adj[y]) == 1
    assert x != y
    if c == d:
        opposite = next(t for t in pair if t != c)
        a, b = g.vertex(), g.vertex()
        left = next(t for t in range(1, 21) if t not in pair and g.legal(x, a, t))
        g.add(x, a, left)
        g.add(a, b, opposite)
        right = next(t for t in range(1, 21) if t not in pair and g.legal(b, y, t))
        g.add(b, y, right)
    else:
        a, b, h = g.vertex(), g.vertex(), g.vertex()
        left = next(t for t in range(1, 21) if t not in pair and g.legal(x, a, t))
        g.add(x, a, left)
        g.add(a, b, d)
        g.add(b, h, c)
        right = next(t for t in range(1, 21) if t not in pair and g.legal(h, y, t))
        g.add(h, y, right)


def construct():
    g, roots, spokes, ts = initial_graph()
    requirements = []
    for c, d in combinations(range(1, 19), 2):
        targets = set()
        for i in range(3):
            targets.add(spokes[c] if c <= 9 else ts[i, c])
            targets.add(spokes[d] if d <= 9 else ts[i, d])
        requirements.append(((c, d), targets))
    for t in range(10, 19):
        for missing in (19, 20):
            requirements.append(((t, missing), {ts[i, t] for i in range(3)}))

    requirements.sort(key=lambda item: (sum(c <= 9 for c in item[0]), item[0]))

    joins = 0
    for pair, targets in requirements:
        while True:
            parts, where = g.components(pair)
            component_ids = sorted({where[e] for e in targets})
            if len(component_ids) == 1:
                break
            first = obtain_leaf_port(g, parts[component_ids[0]], pair)
            second = obtain_leaf_port(g, parts[component_ids[1]], pair)
            if first is None or second is None:
                print("PORT FAILURE", pair, len(g.edges),
                      [(len(parts[i]), sum(len(g.adj[x]) < 4
                                          for e in parts[i] for x in g.edges[e]))
                       for i in component_ids])
                return g, roots, spokes, ts, False
            join_ports(g, first, second, pair)
            joins += 1
    print("joins:", joins)
    return g, roots, spokes, ts, True


def has_sdr(lists):
    return any(len(set(choice)) == 3 for choice in product(*lists))


def verify(g, roots, spokes, ts):
    assert max(map(len, g.adj)) <= 4
    assert len(set(tuple(sorted(e)) for e in g.edges)) == len(g.edges)
    for e, color in enumerate(g.colors):
        if color is not None:
            assert all(g.colors[f] != color for f in g.conflicts(e))
    palette = set(range(1, 21))
    root_neighborhoods = [g.conflicts(e) - set(roots) for e in roots]
    assert len(g.adj[0]) == 3
    assert all(len(ns) == 18 for ns in root_neighborhoods)
    initial_lists = [palette - {g.colors[f] for f in ns} for ns in root_neighborhoods]
    assert initial_lists == [{19, 20}] * 3

    relevant_swaps = 0
    all_stable = True
    for pair in combinations(range(1, 21), 2):
        parts, where = g.components(pair)
        relevant = set()
        for ns in root_neighborhoods:
            relevant.update(where[e] for e in ns if g.colors[e] in pair)
        for component in relevant:
            relevant_swaps += 1
            lists = []
            for ns in root_neighborhoods:
                seen = set()
                for e in ns:
                    c = g.colors[e]
                    if c in pair and where[e] == component:
                        c = sum(pair) - c
                    seen.add(c)
                lists.append(palette - seen)
            if has_sdr(lists):
                all_stable = False
    print("vertices:", len(g.adj))
    print("edges:", len(g.edges))
    print("colored edges:", sum(c is not None for c in g.colors))
    print("maximum degree:", max(map(len, g.adj)))
    print("proper strong partial coloring: verified")
    print("initial three lists:", initial_lists)
    print("relevant single Kempe swaps checked:", relevant_swaps)
    print("one-Kempe stable:", all_stable)
    return all_stable


if __name__ == "__main__":
    graph, roots, spokes, ts, complete = construct()
    stable = verify(graph, roots, spokes, ts)
    if complete and stable:
        output = Path(__file__).with_suffix(".json")
        output.write_text(json.dumps({"edges": graph.edges, "colors": graph.colors,
                                      "root_edges": roots}, separators=(",", ":")))
        print("saved:", output.name)
        print("This certifies failure of one-step recoloring, NOT failure of 20 coloring.")
