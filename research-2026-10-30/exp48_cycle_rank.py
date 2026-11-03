"""exp48: the cycle rank of the two-coloured subgraphs as a potential for hole moves (NEW_DIRECTIONS 11.19).

beta(phi) = sum over the 190 colour pairs (a, b) of the cycle rank E - V + C of the (a, b)-subgraph of L^2 (V = edges
coloured a or b, E = conflicts between them, C = components).  A hole move h -> f_p (h gets p, the only p-member f_p
of N(h) is uncoloured) changes only the 19 subgraphs (p, x).  If every depth-1 stuck state had a hole move that
raises beta, a reachable state of largest beta could not be stuck, and a minimal counterexample could not exist.

For the end states of exp38 runs (the best state of every edge; e is depth-1 stuck there) this prints, per state, the
change of beta for every hole move to a singleton member, and checks the formula
  delta beta = sum_x (k_x - j_x) + sum_x (|M_x| - d_x)
(k_x pieces of the (p, x)-component of f_p without f_p, j_x components met by the x-members M_x of N(h) after
removing f_p, d_x the x-coloured conflicts of f_p) against a direct recount.
Mode attack: simulated annealing from those states (free recolourings and Kempe swaps within L2-distance 3 of e, as
exp33b) on the energy 4 * (exp33b energy) + max(0, largest delta beta); energy 0 is a depth-1 stuck state where no
hole move raises beta.  Found states are re-checked with the direct recount and appended to exp48_found.jsonl.
Usage (run from this directory): exp48_cycle_rank.py <exp38 outdir> ...
                                 exp48_cycle_rank.py attack <steps> <exp38 outdir> ...
"""
import json
import math
import random
import sys
from collections import Counter
from multiprocessing import Pool

import numpy as np
from exp38_gpu_adversary import build_instances, parse_specs, from_bits, classify
from exp33_kempe import K, component, swap
from exp33b_adversary import energy, free


def pair_stats(adj, col, a, b):
    """(V, E, C) of the (a, b)-subgraph"""
    S = [h for h in range(len(adj)) if col[h] in (a, b)]
    Sset = set(S)
    E = sum(1 for h in S for g in adj[h] if g > h and g in Sset)
    seen, C = set(), 0
    for s in S:
        if s in seen:
            continue
        C += 1
        stack = [s]
        seen.add(s)
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y in Sset and y not in seen:
                    seen.add(y)
                    stack.append(y)
    return len(S), E, C


def comp_label(adj, col, a, b, skip):
    lab = {}
    for s in range(len(adj)):
        if s == skip or s in lab or col[s] not in (a, b):
            continue
        stack = [s]
        lab[s] = s
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y != skip and y not in lab and col[y] in (a, b):
                    lab[y] = s
                    stack.append(y)
    return lab


def beta_change(adj, col, h, fp, p):
    """direct recount and the formula; also sum_x (k_x - j_x)"""
    moved = list(col)
    moved[h], moved[fp] = p, -1
    direct = formula = kj = 0
    for x in range(K):
        if x == p:
            continue
        a, b = min(p, x), max(p, x)
        V0, E0, C0 = pair_stats(adj, col, a, b)
        V1, E1, C1 = pair_stats(adj, moved, a, b)
        direct += (E1 - V1 + C1) - (E0 - V0 + C0)
        lab = comp_label(adj, col, a, b, fp)                     # phi without f_p
        nbx = [g for g in adj[fp] if col[g] == x]
        k = len({lab[g] for g in nbx})                           # pieces of f_p's component (each holds an x-nbr)
        Mx = [g for g in adj[h] if col[g] == x]
        j = len({lab[g] for g in Mx})
        kj += k - j
        formula += (k - j) + (len(Mx) - len(nbx))
    return direct, formula, kj



def delta_beta(adj, col, h, fp, p):
    """the formula, with components grown only from the edges that matter (f_p removed)"""
    tot = 0
    for x in range(K):
        if x == p:
            continue
        sf = [g for g in adj[fp] if col[g] == x]
        sh = [g for g in adj[h] if col[g] == x]
        lab = {}
        for s0 in sf + sh:
            if s0 in lab:
                continue
            lab[s0] = s0
            stack = [s0]
            while stack:
                y = stack.pop()
                for z in adj[y]:
                    if z != fp and z not in lab and col[z] in (p, x):
                        lab[z] = s0
                        stack.append(z)
        tot += (len(sh) - len({lab[g] for g in sh})) - (len(sf) - len({lab[g] for g in sf}))
    return tot


def max_delta(adj, col, e):
    mult = Counter(col[f] for f in adj[e])
    return max((delta_beta(adj, col, e, next(f for f in adj[e] if col[f] == p), p)
                for p in range(K) if mult[p] == 1), default=-99)


def score(adj, col, e):
    E0 = energy(adj, col, e)
    return 4 * E0 + (max(0, max_delta(adj, col, e)) if E0 == 0 else 4)


def attack(job):
    name, adj, e, col, steps, seed = job
    rng = random.Random(seed)
    region = set(adj[e])
    for _ in range(2):
        for f in list(region):
            region.update(adj[f])
    region.discard(e)
    region = sorted(region)
    E = best = score(adj, col, e)
    start = E
    for t in range(steps):
        T = 1.0 * (1 - t / steps) + 0.05
        f = rng.choice(region)
        old = list(col)
        if rng.random() < 0.5:
            fr = [c for c in free(adj, col, f) if c != col[f]]
            if not fr:
                continue
            col[f] = rng.choice(fr)
        else:
            c = rng.randrange(K)
            if c == col[f]:
                continue
            swap(col, component(adj, col, f, col[f], c), col[f], c)
        E2 = score(adj, col, e)
        if E2 <= E or rng.random() < math.exp((E - E2) / T):
            E = E2
            best = min(best, E)
            if E == 0:
                break
        else:
            col[:] = old
    out = {"name": name, "start": start, "best": best, "steps": t + 1}
    if E == 0:
        mult = Counter(col[f] for f in adj[e])
        ch = [beta_change(adj, col, e, next(f for f in adj[e] if col[f] == p), p)[0] for p in range(K) if mult[p] == 1]
        out.update(stuck=sum(classify(adj, col, e)) == 0 and len(mult) == K, recount=sorted(ch), col=col)
    return out


def end_states(dirs):
    for d in dirs:
        meta = json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]
        xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
        with np.load(f"{d}/state.npz") as st:
            bE, bc = st["bestEs"], st["bcls"]
        for i, x in enumerate(xs):
            c = i * per + int(np.argmin(bE[i * per:(i + 1) * per]))
            yield x, list(from_bits(bc[c], len(x["adj"])))


if __name__ == "__main__" and sys.argv[1] == "attack":
    steps = int(sys.argv[2])
    jobs = [(x["name"], x["adj"], x["e"], col, steps, i) for i, (x, col) in enumerate(end_states(sys.argv[3:]))]
    with Pool(min(22, len(jobs))) as pool:
        for r in pool.imap_unordered(attack, jobs):
            col = r.pop("col", None)
            print(json.dumps(r), flush=True)
            if col is not None:
                with open("exp48_found.jsonl", "a", encoding="utf-8") as fh:
                    fh.write(json.dumps({**r, "col": col}) + "\n")
elif __name__ == "__main__":
    tot = Counter()
    for d in sys.argv[1:]:
        meta = json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]
        xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
        with np.load(f"{d}/state.npz") as st:
            bE, bc = st["bestEs"], st["bcls"]
        for i, x in enumerate(xs):
            adj, e = x["adj"], x["e"]
            c = i * per + int(np.argmin(bE[i * per:(i + 1) * per]))
            col = list(from_bits(bc[c], len(adj)))
            assert sum(classify(adj, col, e)) == 0 and len({col[f] for f in adj[e]}) == K, "not stuck at e"
            mult = Counter(col[f] for f in adj[e])
            ch = []
            for p in (q for q in range(K) if mult[q] == 1):
                fp = next(f for f in adj[e] if col[f] == p)
                direct, formula, kj = beta_change(adj, col, e, fp, p)
                tot["formula mismatches"] += direct != formula
                ch.append(direct)
            tot["states"] += 1
            tot["states with a beta-raising move"] += max(ch) > 0
            tot["states with a beta-lowering move"] += min(ch) < 0
            print(f"{x['name']}: delta beta over the {len(ch)} hole moves {sorted(ch)}", flush=True)
    print(dict(tot))
