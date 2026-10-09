"""Check only the finite integer equations in dense_complement41.md.

The graph-theoretic reduction and exclusions have separate mathematical proofs.
This script is not an enumeration of all 41-vertex graphs.
"""
from itertools import product


def cyclic_images(a):
    a = tuple(a)
    return {a[i:] + a[:i] for i in range(5)} | {
        a[::-1][i:] + a[::-1][:i] for i in range(5)
    }


def solutions(total, b):
    result = []
    for prefix in product(range(1, total-3), repeat=4):
        last = total-sum(prefix)
        if last < 1:
            continue
        a = prefix+(last,)
        p = tuple(a[(i-1) % 5]+a[(i+1) % 5] for i in range(5))
        if all(p[i]+b[i] >= 16 for i in range(5)):
            result.append((a, p))
    return result


def main():
    main_cases = solutions(41, (0,)*5)
    expected = set().union(*(cyclic_images(a) for a in (
        (8, 8, 8, 8, 9), (9, 9, 7, 7, 9), (9, 9, 8, 7, 8)
    )))
    assert {a for a, _ in main_cases} == expected
    for a, p in main_cases:
        assert any(a[i] >= 8 and p[i] == 16 for i in range(5))
        q = tuple(x-16 for x in p)
        assert all(2*(a[i]-8) == q[i]+q[(i-1) % 5]+q[(i+1) % 5]
                   -q[(i-2) % 5]-q[(i+2) % 5] for i in range(5))
    exceptional_counts = []
    for total, b in (
        (40, (0, 0, 0, 0, 0)),
        (40, (1, 0, 0, 0, 0)),
        (39, (2, 0, 0, 0, 0)),
        (39, (1, 1, 0, 0, 0)),
        (39, (1, 0, 1, 0, 0)),
    ):
        found = solutions(total, b)
        assert found
        assert all(7 <= x <= 9 for a, _ in found for x in a)
        exceptional_counts.append(len(found))
    print('Final size vectors:', len(main_cases), '; three types verified.')
    print('Exceptional equation counts:', exceptional_counts)
    print('Inverse formula and >=8-vertex, degree-16 class verified.')


if __name__ == '__main__':
    main()
