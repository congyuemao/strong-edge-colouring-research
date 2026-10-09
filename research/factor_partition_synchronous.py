"""Find a verified simultaneous-swap escape from the strict local minimum."""
from collections import deque
import json
from pathlib import Path


def main():
    data = json.loads(Path(__file__).with_name('factor_partition_k4.json')
                      .read_text(encoding='utf-8'))[0]['certificate']
    red, blue = data['red_edges'], data['blue_edges']
    adjacency = [set() for _ in range(data['vertices'])]
    for u, v in red + blue:
        adjacency[u].add(v)
        adjacency[v].add(u)
    H = [set() for _ in red]
    for i, e in enumerate(red):
        for j, f in enumerate(red[:i]):
            if set(e) & set(f) or any(y in adjacency[x] for x in e for y in f):
                H[i].add(j)
                H[j].add(i)
    capacities = [4, 3, 3]
    start = tuple(data['partition'])
    def potential(state):
        return sum(state[u] == state[v] for u, nb in enumerate(H) for v in nb)//2 \
            - sum(capacities[c] for c in state)
    initial = potential(start)
    parents = {start: None}
    queue = deque([start])
    found = None
    while queue and len(parents) < 100000:
        state = queue.popleft()
        counts = [[sum(state[w] == c for w in nb) for c in range(3)] for nb in H]
        delta = [[counts[v][c]-counts[v][state[v]]
                  +capacities[state[v]]-capacities[c] for c in range(3)]
                 for v in range(len(H))]
        candidates = []
        for v, old in enumerate(state):
            for new in range(3):
                if new != old and delta[v][new] <= 0:
                    nxt = state[:v]+(new,)+state[v+1:]
                    candidates.append((nxt, {'type': 'single', 'vertex': v,
                                            'old': old, 'new': new,
                                            'delta': delta[v][new]}))
        for v in range(len(H)):
            for w in range(v):
                if state[v] == state[w]:
                    continue
                change = delta[v][state[w]]+delta[w][state[v]]-2*(w in H[v])
                if change <= 0:
                    raw = list(state)
                    raw[v], raw[w] = raw[w], raw[v]
                    candidates.append((tuple(raw), {'type': 'swap', 'vertices': [v, w],
                                                     'delta': change}))
        for nxt, action in candidates:
            assert potential(nxt)-potential(state) == action['delta']
            if action['delta'] < 0:
                path = [action]
                current = state
                while parents[current] is not None:
                    current, old_action = parents[current]
                    path.append(old_action)
                path.reverse()
                found = {'actions': path, 'final_partition': list(nxt),
                         'final_potential': potential(nxt)}
                break
            if nxt not in parents:
                parents[nxt] = (state, action)
                queue.append(nxt)
        if found is not None:
            break
    assert found is not None
    result = {'initial_potential': initial, 'visited_states': len(parents),
              'escape': found}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
