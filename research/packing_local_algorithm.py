"""Construct induced matchings by the private-clique local improvements.

The original graph remains present when restricting to a subset of its edges.
Experiments support the mathematical proof, not the reverse implication to
20-colorability.  No maximum independent set oracle is used.
"""
import json
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parent


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def conflict_masks(edges, selected):
    neighbors = {}
    for u, v in edges:
        neighbors.setdefault(u, set()).add(v)
        neighbors.setdefault(v, set()).add(u)
    closed = [1 << i for i in range(len(selected))]
    for i, original_i in enumerate(selected):
        u, v = edges[original_i]
        reach = {u, v} | neighbors[u] | neighbors[v]
        for j in range(i):
            x, y = edges[selected[j]]
            if x in reach or y in reach:
                closed[i] |= 1 << j
                closed[j] |= 1 << i
    return closed


def local_matching(closed):
    count = len(closed)
    degrees = [mask.bit_count()-1 for mask in closed]
    assert max(degrees, default=0) <= 24
    chosen = 0
    moves = [0, 0, 0]
    while True:
        cover = [mask & chosen for mask in closed]
        uncovered = [i for i, value in enumerate(cover) if not value]
        if uncovered:
            vertex = min(uncovered, key=lambda i: (degrees[i], i))
            chosen |= 1 << vertex
            moves[0] += 1
            continue
        private = {e: 0 for e in bits(chosen)}
        for vertex, owners in enumerate(cover):
            if owners and not owners & (owners-1):
                private[owners.bit_length()-1] |= 1 << vertex
        improved = False
        for e, mask in private.items():
            for f in bits(mask):
                choices = mask & ~closed[f]
                if choices:
                    g = next(bits(choices))
                    chosen = (chosen & ~(1 << e)) | (1 << f) | (1 << g)
                    moves[1] += 1
                    improved = True
                    break
            if improved:
                break
        if improved:
            continue
        for e, mask in private.items():
            f = min(bits(mask), key=lambda i: (degrees[i], i))
            if degrees[f] < degrees[e]:
                chosen = (chosen & ~(1 << e)) | (1 << f)
                moves[2] += 1
                improved = True
                break
        if not improved:
            break
    # Check the local terminal certificate, independently of the move history.
    for e in bits(chosen):
        assert closed[e] & chosen == 1 << e
    for e, mask in private.items():
        for f in bits(mask):
            assert mask & ~closed[f] == 0
            assert degrees[f] >= degrees[e]
    upper_sum = sum(degrees[e]+1+mask.bit_count()
                    for e, mask in private.items())
    assert 2*count <= upper_sum
    assert all(degrees[e]+1+mask.bit_count() <= 40
               for e, mask in private.items())
    assert 20*chosen.bit_count() >= count
    return list(bits(chosen)), moves


def main():
    graphs = json.loads((ROOT/'colouring_certificates.json').read_text())
    rng = Random(20261009)
    certificates = []
    total_moves = [0, 0, 0]
    for graph in graphs:
        edges = graph['edges']
        subsets = [list(range(len(edges))),
                   [i for i in range(len(edges)) if rng.randrange(2)],
                   [i for i in range(len(edges)) if i % 3 != 1]]
        for kind, selected in enumerate(subsets):
            local_indices, moves = local_matching(conflict_masks(edges, selected))
            certificates.append(dict(sample=graph['sample'], kind=kind,
                                     selected=selected,
                                     matching=[selected[i] for i in local_indices],
                                     moves=moves))
            total_moves = [x+y for x, y in zip(total_moves, moves)]
    out = ROOT/'packing_certificates.json'
    out.write_text(json.dumps(certificates, separators=(',', ':')), encoding='utf-8')
    print('Local terminal certificates:', len(certificates))
    print('Move totals (add, split, lower degree):', total_moves)
    print('All terminal private-clique sums and 20-packing inequalities passed.')


if __name__ == '__main__':
    main()
