"""Exact strict-bad-K4 variant of the tower potential experiment."""
import json
from itertools import product
from pathlib import Path
import numpy as np
from factor_partition_tower import STATES, COUNTS, UNARY, PAIR, PSI, LOOKUP, solve, build_and_verify


def main():
    source = json.loads(Path(__file__).with_name('factor_partition_tower.json')
                        .read_text(encoding='utf-8'))
    outer = [LOOKUP[s] for s in product((0, 1), repeat=5)]
    inverse = np.argsort(PSI)
    boundary = []
    for singleton in range(5):
        for other in (0, 1):
            root = [2]*5
            root[singleton] = other
            root = LOOKUP[tuple(root)]
            for first in outer:
                for last in outer:
                    valid = True
                    for j in range(5):
                        if j == singleton:
                            continue
                        counts = COUNTS[root]+COUNTS[first]+COUNTS[last]
                        counts = counts.copy()
                        counts[2] -= 1
                        counts[STATES[first, PSI[j]]] -= 1
                        counts[STATES[last, inverse[j]]] -= 1
                        if tuple(counts) != (5, 4, 3):
                            valid = False
                            break
                    if valid:
                        boundary.append((root, first, last))
    results = []
    for record in source:
        layers = record['layers']
        distance = {}
        for first in outer:
            dp = np.full(len(STATES), 10000, dtype=np.int32)
            dp[first] = UNARY[first]
            for _ in range(layers-2):
                dp = (dp[:, None]+PAIR).min(axis=0)+UNARY
            distance[first] = dp
        best_value, best_args = 10000, None
        for root, first, last in boundary:
            value = int(UNARY[root]+PAIR[root, first]+distance[first][last]+PAIR[last, root])
            if value < best_value:
                best_value, best_args = value, (root, first, last)
        value, path = solve(layers, *best_args, reconstruct=True)
        assert value == best_value
        certificate = build_and_verify(layers, path)
        assert certificate['potential_verified'] == value
        root_clique = [j for j in range(5) if certificate['partition'][j] == 2]
        assert len(root_clique) == 4
        assert all(certificate['part_neighbor_counts'][j] == [5, 4, 3]
                   for j in root_clique)
        result = {'layers': layers, 'strict_boundary_configurations': len(boundary),
                  'global_minimum': record['global_minimum'],
                  'minimum_with_strict_bad_K4': value,
                  'gap': value-record['global_minimum'], 'certificate': certificate}
        results.append(result)
        print(json.dumps({k: v for k, v in result.items() if k != 'certificate'}), flush=True)
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(results, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
