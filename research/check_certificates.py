"""Read-only checker of saved colourings, directly from the problem definition."""
import json
from itertools import combinations
from pathlib import Path


def main():
    path = Path(__file__).with_name("colouring_certificates.json")
    data = json.loads(path.read_text(encoding="utf-8"))
    checked = 0
    for item in data:
        edges = [tuple(e) for e in item["edges"]]
        n = item["n"]
        assert len(set(edges)) == len(edges)
        adj = [set() for _ in range(n)]
        for a, b in edges:
            assert 0 <= a < b < n
            adj[a].add(b)
            adj[b].add(a)
        assert all(len(ns) <= 4 for ns in adj)
        for key, limit in (("bound22_colours", 22), ("dsatur_colours", 20)):
            cs = item[key]
            assert len(cs) == len(edges)
            assert all(type(c) is int and 0 <= c < limit for c in cs)
            for i, j in combinations(range(len(edges)), 2):
                if cs[i] != cs[j]:
                    continue
                a, b = edges[i]
                x, y = edges[j]
                assert len({a, b, x, y}) == 4
                assert x not in adj[a] and y not in adj[a]
                assert x not in adj[b] and y not in adj[b]
            checked += 1
    print(f"Verified {checked} colourings for {len(data)} graphs.")


if __name__ == "__main__":
    main()
