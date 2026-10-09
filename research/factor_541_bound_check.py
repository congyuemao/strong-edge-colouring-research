"""Check only the integer tables in factor_541_two_representatives.md.

This is not graph enumeration and does not establish graph realizability.
"""
from itertools import product
import json
from pathlib import Path


def run():
    results = []
    for eps in ((0, 0), (0, 1), (1, 1)):
        row = []
        records = []
        for t in range(7):
            values = []
            for s1, s2 in product(range(4), repeat=2):
                if any(s + t > 5 + e for s, e in zip((s1, s2), eps)):
                    continue
                if max(s1, s2) == 3 and t > 2:
                    continue
                h = sum(eps) + s1 + s2 + t
                if h == 0:
                    continue
                m = sum(s * (s - 1) // 2 + e * (s + t)
                        for s, e in zip((s1, s2), eps))
                z = sum(e == 0 and s + t == 5
                        for s, e in zip((s1, s2), eps))
                bound = (29 * h - 8 * m - 12 - 15 * z) // 5
                bound -= (bound - h) % 2
                values.append(bound)
                records.append(dict(s1=s1, s2=s2, t=t, h=h, m_lower=m,
                                    isolated_low_representatives=z,
                                    bound=bound))
            row.append(max(values) if values else None)
        best = max(v for v in row if v is not None)
        results.append(dict(eps=eps, maxima_by_t=row, maximum=best,
                            maximizers=[r for r in records if r['bound'] == best]))
    expected = [[22, 27, 28, 29, 26, 19, None],
                [23, 28, 29, 28, 28, 25, None],
                [24, 27, 30, 29, 32, 29, 24]]
    assert [r['maxima_by_t'] for r in results] == expected
    data = dict(scope='Integer arithmetic only; not graph enumeration.', results=results)
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(data, indent=2), encoding='utf-8')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    run()
