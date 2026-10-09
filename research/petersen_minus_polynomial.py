"""Finite interpolation coefficient search for the Petersen-minus-edge core.

This computes exact modular coefficients of a graph polynomial, not a random
list-coloring experiment.  A separate proof must justify any use for lists.
"""
from math import factorial, comb, prod
from pathlib import Path
import json


def inverse_grid(t, prime):
    return [pow(((-1)**(t-c)*factorial(c)*factorial(t-c)) % prime,
                prime-2, prime) for c in range(t+1)]


def coefficient(exponents, prime=None):
    assert sum(exponents) == 74
    reduce = (lambda value: value % prime) if prime else (lambda value: value)
    inv = ([inverse_grid(t, prime) for t in exponents] if prime else
           [[(-1)**(t-c)*comb(t, c) for c in range(t+1)] for t in exponents])
    normal_bounds = [(exponents[4+2*i], exponents[5+2*i]) for i in range(5)]
    totals = [0, 0, 0]
    assigned = []

    def finish(weight):
        totals[1] += 1
        moments = []
        for i in range(4):
            s0 = s1 = 0
            for color in range(exponents[i]+1):
                value = inv[i][color]
                for part, pair in enumerate(assigned):
                    if part != i:
                        for x in pair:
                            value = reduce(value * (color-x))
                s0 = reduce(s0+value)
                s1 = reduce(s1+color*value)
            moments.append((s0, s1))
        left = reduce(moments[0][1]*moments[1][0]
                      - moments[0][0]*moments[1][1])
        right = reduce(moments[2][1]*moments[3][0]
                       - moments[2][0]*moments[3][1])
        value = reduce(weight*left*right)
        totals[0] = reduce(totals[0]+value)
        totals[2] += bool(value)

    def visit(part, used, weight):
        if part == 5:
            finish(weight)
            return
        t1, t2 = normal_bounds[part]
        first, second = 4+2*part, 5+2*part
        for a in range(t1+1):
            if a in used:
                continue
            for b in range(t2+1):
                if b in used:
                    continue
                # Equal bounds give two interchangeable independent twins.
                if t1 == t2 and b < a:
                    continue
                factor = reduce(inv[first][a]*inv[second][b])
                if t1 == t2 and a != b:
                    factor = reduce(factor*2)
                for old in assigned:
                    for x in old:
                        factor = reduce(factor*(x-a)*(x-b))
                assigned.append((a, b))
                visit(part+1, used | {a, b}, reduce(weight*factor))
                assigned.pop()

    visit(0, set(), 1)
    if prime is None:
        denominator = prod(factorial(t) for t in exponents)
        assert totals[0] % denominator == 0
        totals[0] //= denominator
    return {"prime": prime, "coefficient": totals[0],
            "normal_assignments": totals[1], "nonzero_contributions": totals[2]}


def core_graph():
    # Four three-point parts: special i and its normal pair. Last part is 12,13.
    parts = [[i, 4+2*i, 5+2*i] for i in range(4)] + [[12, 13]]
    block = {v: p for p, part in enumerate(parts) for v in part}
    absent = {(i, j) for i in (0, 1) for j in (2, 3)}
    edges = [(i, j) for i in range(14) for j in range(i+1, 14)
             if block[i] != block[j] and (i, j) not in absent]
    assert len(edges) == 74
    degrees = [sum(v in e for e in edges) for v in range(14)]
    assert degrees == [9]*4 + [11]*8 + [12]*2
    return edges


def main():
    exponents = [4]*4 + [5, 6, 6, 6, 5, 6, 6, 6] + [6, 6]
    result = {"exponents": exponents, "edges": core_graph(),
              "results": [coefficient(exponents, prime)
                          for prime in (None, 1000003, 1000033)]}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2),
                                                  encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'edges'}))


if __name__ == '__main__':
    main()
