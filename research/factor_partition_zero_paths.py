"""Breadth-first search of zero-potential single-vertex moves.

Input is a certified strict bad-K5 partition of a real factor conflict graph.
An escape is a sequence of zero-cost moves followed by a negative-cost move.
The node cap is explicit; a capped search is not a nonexistence certificate.
"""
from collections import deque
import json
from pathlib import Path


def main():
    source = Path(__file__).with_name('factor_partition_tower.json')
    records = json.loads(source.read_text(encoding='utf-8'))
    output = []
    for record in records:
        certificate = record['strict_certificate']
        red, blue = certificate['red_edges'], certificate['blue_edges']
        n = certificate['vertices']
        adjacent = [set() for _ in range(n)]
        for u, v in red + blue:
            adjacent[u].add(v)
            adjacent[v].add(u)
        conflict = [set() for _ in red]
        for i, e in enumerate(red):
            for j, f in enumerate(red[:i]):
                if set(e) & set(f) or any(y in adjacent[x] for x in e for y in f):
                    conflict[i].add(j)
                    conflict[j].add(i)
        target = [4, 3, 3]
        start = tuple(certificate['partition'])
        parent = {start: None}
        queue = deque([start])
        escape = None
        while queue and len(parent) < 200000 and escape is None:
            state = queue.popleft()
            for v, old in enumerate(state):
                counts = [sum(state[w] == c for w in conflict[v]) for c in range(3)]
                for new in range(3):
                    if new == old:
                        continue
                    delta = counts[new]-counts[old]+target[old]-target[new]
                    if delta > 0:
                        continue
                    nxt = state[:v]+(new,)+state[v+1:]
                    if delta < 0:
                        path = [[v, old, new, delta]]
                        current = state
                        while parent[current] is not None:
                            previous, move = parent[current]
                            path.append(move)
                            current = previous
                        path.reverse()
                        escape = {'moves': path, 'final_partition': list(nxt),
                                  'potential_change': sum(m[3] for m in path)}
                        break
                    if nxt not in parent:
                        parent[nxt] = (state, [v, old, new, 0])
                        queue.append(nxt)
                if escape is not None:
                    break
        result = {'layers': record['layers'], 'visited_states': len(parent),
                  'queue_remaining': len(queue),
                  'exhausted': not queue and escape is None,
                  'cap_reached': len(parent) >= 200000, 'escape': escape}
        output.append(result)
        print(json.dumps(result), flush=True)
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(output, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
