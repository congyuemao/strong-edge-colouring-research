"""Targeted exact checks of maximum-cut intermediate conjectures.

Original-graph conflicts are retained. This investigates proposed lemmas;
it is not a proof of the all-graphs statement.
"""
from pathlib import Path
import json
from structural_factors import edge, conflicts, exact_colouring


def examine(name, n, edges):
    scores = []
    best = -1
    masks = []
    for mask in range(1 << (n-1)):
        value = sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges)
        if value > best:
            best, masks = value, [mask]
        elif value == best:
            masks.append(mask)
    for mask in masks:
        internal = [e for e in edges if not (((mask >> e[0]) ^ (mask >> e[1])) & 1)]
        cross = [e for e in edges if e not in internal]
        ch_int, ci, _ = exact_colouring(conflicts(n, edges, internal))
        ch_cross, cc, _ = exact_colouring(conflicts(n, edges, cross))
        scores.append(dict(mask=mask, internal=internal, chi_internal=ch_int,
                           cross=cross, chi_cross=ch_cross,
                           colour_internal=ci, colour_cross=cc,
                           sum=ch_int+ch_cross))
    return dict(name=name, n=n, edges=edges, maxcut=best,
                maxcut_count=len(masks),
                internal_min=min(r['chi_internal'] for r in scores),
                internal_max=max(r['chi_internal'] for r in scores),
                sum_min=min(r['sum'] for r in scores),
                sum_max=max(r['sum'] for r in scores),
                best=min(scores, key=lambda r: r['sum']),
                worst=max(scores, key=lambda r: r['chi_internal']))


if __name__ == '__main__':
    cases = [('K5', 5, [(u,v) for u in range(5) for v in range(u+1,5)]),
             ('C5_double', 10, sorted({edge(2*i+a,2*((i+1)%5)+b)
                                      for i in range(5) for a in range(2) for b in range(2)})),
             ('C11_steps_1_4', 11, sorted({edge(i,(i+s)%11) for i in range(11) for s in (1,4)}))]
    found = json.loads(Path(__file__).with_name('structural_factor_clique.json').read_text())
    for i, row in enumerate(found):
        if row['state'] == 'sat':
            cases.append(('factor_clique_' + str(row['parts']), sum(row['parts']),
                          sorted(tuple(e) for e in row['first'] + row['second'])))
    out = []
    for args in cases:
        row = examine(*args)
        out.append(row)
        print({k:row[k] for k in ('name','maxcut','maxcut_count','internal_min',
                                 'internal_max','sum_min','sum_max')}, flush=True)
        Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
