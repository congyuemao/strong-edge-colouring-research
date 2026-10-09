"""Find a second two-factor making every edge of a given first factor conflict.

The finite backtracking handles coverage clauses and exact degree two.
No solver library or network needed.
"""
from itertools import combinations
from pathlib import Path
import json
import time
from structural_factors import edge, conflicts


def solve(parts, budget=30):
    n = sum(parts)
    first = []
    start = 0
    for length in parts:
        first += [edge(start + i, start + (i+1) % length) for i in range(length)]
        start += length
    first = sorted(first)
    firstset = set(first)
    variables = [e for e in combinations(range(n), 2) if e not in firstset]
    number = {e: i for i, e in enumerate(variables)}
    incidence = [sum(1 << i for i, e in enumerate(variables) if v in e)
                 for v in range(n)]
    fadj = [set() for _ in range(n)]
    for u, v in first:
        fadj[u].add(v)
        fadj[v].add(u)
    clauses = []
    for a, b in combinations(first, 2):
        if set(a) & set(b) or any(v in fadj[u] for u in a for v in b):
            continue
        clauses.append(sum(1 << number[edge(u, v)] for u in a for v in b))
    allbits = (1 << len(variables)) - 1
    started = time.monotonic()
    nodes = 0

    def search(yes, no):
        nonlocal nodes
        nodes += 1
        if nodes % 4096 == 0 and time.monotonic() - started > budget:
            raise TimeoutError
        while True:
            before = (yes, no)
            for inc in incidence:
                # Earlier vertices in this pass may already have forced an
                # edge. Recompute availability to avoid treating it as free.
                free = allbits ^ (yes | no)
                have = (inc & yes).bit_count()
                avail = inc & free
                need = 2 - have
                if need < 0 or avail.bit_count() < need:
                    return None
                if need == 0:
                    no |= avail
                elif avail.bit_count() == need:
                    yes |= avail
            if yes & no:
                return None
            free = allbits ^ (yes | no)
            remaining = []
            for clause in clauses:
                if clause & yes:
                    continue
                choices = clause & free
                if not choices:
                    return None
                if choices.bit_count() == 1:
                    yes |= choices
                remaining.append(choices)
            if yes & no:
                return None
            if (yes, no) == before:
                break
        free = allbits ^ (yes | no)
        if not remaining:
            unfinished = [inc & free for inc in incidence
                          if (inc & yes).bit_count() < 2]
            if not unfinished:
                return [variables[i] for i in range(len(variables)) if yes & (1 << i)]
            choice = min(unfinished, key=int.bit_count)
        else:
            # Each still-required edge can cover at most four clauses.
            if len(remaining) > 4 * (n - yes.bit_count()):
                return None
            choice = min(remaining, key=int.bit_count)
        candidates = []
        while choice:
            bit = choice & -choice
            choice -= bit
            coverage = sum(bool(clause & bit) for clause in remaining)
            candidates.append((coverage, bit))
        for _, bit in sorted(candidates, reverse=True):
            found = search(yes | bit, no)
            if found is not None:
                return found
            no |= bit
        return None

    try:
        second = search(0, 0)
        state = 'sat' if second is not None else 'unsat'
    except TimeoutError:
        second, state = None, 'timeout'
    if second is not None:
        adj = conflicts(n, first + second, first)
        assert all(a.bit_count() == n-1 for a in adj)
        assert all(sum(v in e for e in second) == 2 for v in range(n))
    return dict(parts=parts, state=state, nodes=nodes,
                seconds=time.monotonic()-started, first=first, second=second)


if __name__ == '__main__':
    rows = []
    for parts in ([11], [12], [4, 8], [5, 7], [6, 6], [4, 4, 4],
                  [13], [5, 8], [6, 7]):
        row = solve(parts, 30)
        rows.append(row)
        print({k: row[k] for k in ('parts', 'state', 'nodes', 'seconds')}, flush=True)
        Path(__file__).with_suffix('.json').write_text(
            json.dumps(rows, indent=2), encoding='utf-8')
