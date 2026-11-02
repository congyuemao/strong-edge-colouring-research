"""exp42: which KIL2 first moves are bad?  Shapes of first moves in depth-1 stuck states, and class M.

A first move swaps one (a, b)-component C meeting N(e).  Its shape: mult_a, mult_b = how often a, b occur on N(e);
ka, kb = how many of those a-, b-members lie in C; size = |C|; near = how many members of N(e) in C share an endpoint
with e; opened = how many colour pairs are separable at e after the swap (0 = bad move).

Class M: a is a singleton on N(e) (one member f_a), b has >= 2 members, and the (a, b)-component of f_a holds some but
not all b-members.  exp38's KIL_GPU_GMODE=9 / 10 attack "every class-M move is good" / "some class-M move is good".

Usage (run from this directory):
  exp42_first_move_shapes.py mine <out.jsonl> <workers> <source> ...     every first move with its shape
  exp42_first_move_shapes.py table <moves.jsonl> ...                    good / bad counts per shape
  exp42_first_move_shapes.py mclass <out.jsonl> <workers> <source> ...  class-M moves with the pairs they open
  exp42_first_move_shapes.py archive <found.jsonl> <spec> <out.json> all|some|nonsibling
      re-check exp38 GMODE 9 / 10 / 11 states with exp40's networkx code (class-M moves recomputed on its conflict
      sets) and write them one per line; nonsibling: some class-M move whose component holds no b-member sharing an
      endpoint with f_a is bad
Sources: repo (the archived stuck states of this directory), hunt:<exp38 outdir>:<sample size>, npz:<exp38 outdir>
(the best stuck state of every edge of a run).
"""
import hashlib
import json
import os
import random
import sys
from collections import Counter, defaultdict
from multiprocessing import Pool

import numpy as np

from exp33_kempe import K, component, l2_adj, separable, swap
from exp38_gpu_adversary import build_instances, from_bits, good_first_moves, parse_specs

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_STATES = ["weak_single_form_counterexamples_n200", "doubled_colour_lemma_counterexample_n100",
               "kil2_extreme_states", "kil_depth1_counterexamples_n100"]


def states(sources, rng):
    for s in sources:
        kind, _, rest = s.partition(":")
        if kind == "repo":
            for name in REPO_STATES:
                for i, x in enumerate(json.load(open(os.path.join(HERE, name + ".json"), encoding="utf-8"))):
                    yield f"{name}#{i}", x["edges"], x["e"], x["colouring"]
        elif kind == "hunt":
            d, k = rest.rsplit(":", 1)
            xs = {x["name"]: x for x in build_instances(parse_specs(
                json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]["spec"]))}
            rows = [json.loads(l) for l in open(f"{d}/found.jsonl", encoding="utf-8")]
            for r in rng.sample(rows, min(int(k), len(rows))):
                key = hashlib.sha1((r["instance"] + json.dumps(r["colouring"])).encode()).hexdigest()[:12]
                x = xs[r["instance"]]
                yield f"{os.path.basename(d)}:{key}", x["edges"], x["e"], r["colouring"]
        elif kind == "npz":
            meta = json.load(open(f"{rest}/meta.json", encoding="utf-8"))["meta"]
            xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
            with np.load(f"{rest}/state.npz") as st:
                b, bc = st["bestEs"], st["bcls"]
                for i, x in enumerate(xs):
                    c = i * per + int(np.argmin(b[i * per:(i + 1) * per]))
                    if b[c] < meta.get("gcap", 0):                 # stuck states only
                        yield (f"{os.path.basename(rest)}:{x['name']}:E{int(b[c])}", x["edges"], x["e"],
                               from_bits(bc[c], len(x["adj"])))
        else:
            raise SystemExit(f"unknown source {s}")


def opened_pairs(adj, col, e, a, b):
    return [(c, d) for c in range(K) for d in range(c + 1, K)
            if (c in (a, b) or d in (a, b)) and separable(adj, col, e, c, d) is not None]


def moves(job):
    src, edges, e, col = job
    adj, col, ends = l2_adj(edges), list(col), set(edges[e])
    Ne = adj[e]
    mult = Counter(col[f] for f in Ne)
    out = []
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for f in Ne:
                if col[f] not in (a, b) or f in done:
                    continue
                comp = component(adj, col, f, a, b)
                done.update(comp)
                mem = [g for g in Ne if g in set(comp)]
                swap(col, comp, a, b)
                ok = opened_pairs(adj, col, e, a, b)
                swap(col, comp, a, b)
                out.append({"src": src, "a": a, "b": b, "mult_a": mult[a], "mult_b": mult[b],
                            "ka": sum(col[g] == a for g in mem), "kb": sum(col[g] == b for g in mem),
                            "size": len(comp), "near": sum(bool(ends & set(edges[g])) for g in mem),
                            "opened": len(ok)})
    return out


def mclass(job):
    """Class-M moves; near_a = f_a shares an endpoint with e, near_b = how many of the b-members in C do, sibling =
    some b-member in C shares an endpoint with f_a."""
    src, edges, e, col = job
    adj, col, ends = l2_adj(edges), list(col), set(edges[e])
    Ne = adj[e]
    mult = Counter(col[f] for f in Ne)
    out = []
    for a in [c for c in range(K) if mult[c] == 1]:
        fa = next(f for f in Ne if col[f] == a)
        for b in [c for c in range(K) if mult[c] >= 2]:
            comp = component(adj, col, fa, a, b)
            fb = [g for g in Ne if col[g] == b and g in set(comp)]
            if not 0 < len(fb) < mult[b]:
                continue
            swap(col, comp, a, b)
            ok = opened_pairs(adj, col, e, a, b)
            swap(col, comp, a, b)
            out.append({"src": src, "a": a, "b": b, "mult_b": mult[b], "kb": len(fb), "size": len(comp),
                        "near_a": bool(ends & set(edges[fa])), "near_b": sum(bool(ends & set(edges[g])) for g in fb),
                        "sibling": any(set(edges[fa]) & set(edges[g]) for g in fb), "opened": len(ok), "pairs": ok})
    return out


def run_pool(fn, out, workers, sources):
    jobs = list(states(sources, random.Random(1)))
    print(len(jobs), "states", flush=True)
    lo = []
    with Pool(workers) as pool, open(out, "w", encoding="utf-8") as fh:
        for res in pool.imap_unordered(fn, jobs):
            for r in res:
                fh.write(json.dumps(r) + "\n")
            lo.append(min((r["opened"] for r in res), default=None))
    print("states without a move:", lo.count(None), "; fewest pairs opened by a move, per state:",
          sorted(Counter(v for v in lo if v is not None).items()))


def table(files):
    R = [json.loads(l) for f in files for l in open(f, encoding="utf-8")]
    print(len(R), "moves,", len({r["src"] for r in R}), "states,", sum(r["opened"] == 0 for r in R), "bad")
    c = defaultdict(lambda: [0, 0, 0])
    for r in R:
        t = c[tuple(sorted([(r["mult_a"], r["ka"]), (r["mult_b"], r["kb"])]))]
        t[0] += 1
        t[1] += r["opened"] == 0
        t[2] += r["opened"]
    print("shape ((mult, members in C), (mult, members in C)): moves, bad, mean pairs opened")
    for k in sorted(c, key=lambda k: (-c[k][1], -c[k][0])):
        print(f"  {k}  {c[k][0]}  {c[k][1]}  {c[k][2] / c[k][0]:.1f}")


def comp_nx(nbr, col, f, a, b):
    seen, st = {f}, [f]
    while st:
        x = st.pop()
        for y in nbr[x]:
            if y not in seen and col[y] in (a, b):
                seen.add(y)
                st.append(y)
    return seen


def sep_nx(nbr, col, e, a, b):
    done = set()
    for f in nbr[e]:
        if col[f] in (a, b) and f not in done:
            c = comp_nx(nbr, col, f, a, b)
            done |= c
            if {col[g] for g in c if g in nbr[e]} == {a, b}:
                return False
    return True


def first_moves(adj, col, e):
    n = 0
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for f in adj[e]:
                if col[f] in (a, b) and f not in done:
                    done.update(component(adj, col, f, a, b))
                    n += 1
    return n


def archive(found, spec, out, form):
    from exp40_verify_stuck import check
    insts = {x["name"]: x for x in build_instances(parse_specs(spec))}
    res = []
    for line in open(found, encoding="utf-8"):
        r = json.loads(line)
        x = insts[r["instance"]]
        col, e, edges = list(r["colouring"]), x["e"], x["edges"]
        info, nbr = check(edges, e, col)
        stuck = info["proper"] and info["all_coloured"] and info["blocked"] and not info["separable_pairs"]
        Ne, ends = nbr[e], set(edges[e])
        mult = Counter(col[f] for f in Ne)
        ms = []
        for a in [c for c in range(K) if mult[c] == 1]:
            fa = next(f for f in Ne if col[f] == a)
            for b in [c for c in range(K) if mult[c] >= 2]:
                C = comp_nx(nbr, col, fa, a, b)
                kb = sum(col[g] == b and g in C for g in Ne)
                if not 0 < kb < mult[b]:
                    continue
                for h in C:
                    col[h] = a + b - col[h]
                op = [[min(p, q), max(p, q)] for p in (a, b) for q in range(K)
                      if q != p and not (p == b and q == a) and sep_nx(nbr, col, e, min(p, q), max(p, q))]
                for h in C:
                    col[h] = a + b - col[h]
                sib = any(col[g] == b and set(edges[g]) & set(edges[fa]) for g in C if g in Ne)
                ms.append({"a": a, "b": b, "f_a": fa, "f_a_near": bool(ends & set(edges[fa])), "mult_b": mult[b],
                           "kb": kb, "sibling": sib, "component": sorted(C),
                           "component_in_N(e)": sorted(g for g in C if g in Ne), "opened": op})
        bad = [m for m in ms if not m["opened"] and (form != "nonsibling" or not m["sibling"])]
        ok = stuck and (len(bad) == len(ms) > 0 if form == "some" else bool(bad))
        res.append({"instance": r["instance"], "spec": x["spec"], "edges": [list(p) for p in edges], "e": e,
                    "colouring": col, "depth1_stuck_networkx": stuck,
                    "multiplicities_on_N(e)": dict(sorted(Counter(mult.values()).items())),
                    "class_m_moves": len(ms), "bad_class_m_moves": len(bad) if form == "some" else bad,
                    f"class_m_{form}_form_counterexample": ok, "first_moves": first_moves(x["adj"], col, e),
                    "good_first_moves": good_first_moves(x["adj"], list(col), e), "depth2": r["depth2"]})
        print(r["instance"], "stuck", stuck, "class M", len(ms), "bad", len(bad), "counterexample", ok,
              "first moves", res[-1]["first_moves"], "good", res[-1]["good_first_moves"], flush=True)
    with open(out, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("[\n" + ",\n".join(json.dumps(s) for s in res) + "\n]\n")
    print(len(res), "states,", sum(s[f"class_m_{form}_form_counterexample"] for s in res), "counterexamples")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd in ("mine", "mclass"):
        run_pool(moves if cmd == "mine" else mclass, sys.argv[2], int(sys.argv[3]), sys.argv[4:])
    elif cmd == "table":
        table(sys.argv[2:])
    elif cmd == "archive":
        archive(*sys.argv[2:6])
    else:
        raise SystemExit(__doc__)
