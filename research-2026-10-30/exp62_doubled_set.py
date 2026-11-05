"""exp62: the natural colour set Y0 = colours on at least two members of N(h) (NEW_DIRECTIONS 11.27).  Then every colour outside Y0 is single at h, tau_{Y0}(h) = 2(20-k) - deg + d_Y = number of singles when all 20 colours are seen.
So h stays in C_{Y0} only if every single member lies in C_{Y0}.  Also tests each subset of Y0 of size >= 2.  Usage: exp62_doubled_set.py files.json"""
import itertools, json, sys
from collections import Counter
from exp33_kempe import K, l2_adj
from importlib import util
spec = util.spec_from_file_location("e60", "exp60_core_lib.py")
m60 = util.module_from_spec(spec); spec.loader.exec_module(m60)
tot = 0; bad = 0
for fn in sys.argv[1:]:
    data = json.load(open(fn, encoding="utf-8"))
    for x in (data if isinstance(data, list) else [data]):
        edges = [tuple(e) for e in x["edges"]]; h = x["e"]; col = list(x["colouring"]); col[h] = -1
        for g in x.get("U", []): col[g] = -1
        adj = l2_adj(edges)
        for g in x.get("U", []):
            adj[g] = []; adj = [[y for y in r if y != g] for r in adj]
        adjs = [set(r) for r in adj]
        T = m60.tangled_sets(adj, col)
        c = Counter(col[y] for y in adj[h])
        Y0 = sorted(a for a, n in c.items() if n >= 2)
        res = {}
        for k in range(2, len(Y0) + 1):
            for Y in itertools.combinations(Y0, k):
                cur, rank, S = m60.core(adj, adjs, col, T, Y)
                res[Y] = (h not in cur, h in S)
        tot += 1
        full = tuple(Y0)
        ok = res.get(full, (None, None))
        nf = sum(1 for v in res.values() if not v[0])
        bad += (ok[0] is False)
        print(f"{x.get('instance', '?')[:26]}: deg {len(adj[h])} |Y0|={len(Y0)} tauh Y0 good={ok[0]} h tangled={ok[1]}; subsets failing {nf}/{len(res)}", flush=True)
print("states", tot, "Y0 fails on", bad)
