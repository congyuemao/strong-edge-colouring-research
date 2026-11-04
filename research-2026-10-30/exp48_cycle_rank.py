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
Mode swaps: for each end state (and each state of a found.jsonl) the change of beta for every Kempe swap anywhere in
the graph; beta = const + total number of two-coloured components, since the totals of V and E are fixed.
Mode climb: from each end state and from random colourings of G - e, raise the number of two-coloured components
by Kempe swaps (first improvement, e stays uncoloured) until no swap raises it; report e at the local maximum.
Mode stuckclimb: the same ascent, but only through swaps that keep e depth-1 stuck; at the end, count the swaps that
still raise the number of components.  None left would be a stuck local maximum (appended to exp48_found.jsonl).
Mode blockedclimb: the same ascent through swaps that keep e blocked (fast local gains, kempe_gain); a swap can
unblock e only if its component holds members of N(e), so the raising swaps left all free a colour at e.  None
left would be a local maximum with e blocked, against the strong form (a local maximum never blocks e).
Mode hop: basin hopping on the number of raising swaps left by the ascent of blockedclimb (see hop_job).
Mode raising: after stuckclimb, simulated annealing on the number of raising swaps, through swaps of components
within L2-distance 3 of e that keep e depth-1 stuck (each step recounts every swap).
Mode small: every connected 4-regular graph on n vertices (graphs_n<n>.txt), every edge h, reps random colourings of
G - h, each climbed to a local maximum; counts the local maxima where h is blocked / depth-1 stuck.
Mode girth: the climb of mode climb from random colourings on random graphs of a given girth.
Usage (run from this directory): exp48_cycle_rank.py <exp38 outdir> ...
                                 exp48_cycle_rank.py attack <steps> <exp38 outdir> ...
                                 exp48_cycle_rank.py swaps <exp38 outdir> ... [found.jsonl]
                                 exp48_cycle_rank.py climb <random starts> <exp38 outdir> ...
                                 exp48_cycle_rank.py stuckclimb <exp38 outdir> ...
                                 exp48_cycle_rank.py blockedclimb <exp38 outdir> ...
                                 exp48_cycle_rank.py hop <hops> <workers> <exp38 outdir> ...
                                 exp48_cycle_rank.py raising <steps> <exp38 outdir> ...
                                 exp48_cycle_rank.py small <reps> <n,n,...>
                                 exp48_cycle_rank.py girth <climbs per graph> <n:girth:seeds> ...
"""
import json
import math
import os
import random
import sys
from collections import Counter
from multiprocessing import Pool

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")  # otherwise each worker commits 773 MiB on importing numpy
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


def swap_gains(adj, col):
    """the change of the total number of two-coloured components (= the change of beta) for every Kempe swap of
    the colouring (every (a, b)-component, a < b); a swap only changes the subgraphs (a, x) and (b, x)"""
    m = len(adj)

    def comps(c1, c2):
        S = [i for i in range(m) if col[i] in (c1, c2)]
        seen, C = set(), 0
        for s0 in S:
            if s0 in seen:
                continue
            C += 1
            seen.add(s0)
            stack = [s0]
            while stack:
                y = stack.pop()
                for z in adj[y]:
                    if z not in seen and col[z] in (c1, c2):
                        seen.add(z)
                        stack.append(z)
        return C

    base = {(a, b): comps(a, b) for a in range(K) for b in range(a + 1, K)}
    out = []
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for s0 in range(m):
                if s0 in done or col[s0] not in (a, b):
                    continue
                Kc = component(adj, col, s0, a, b)
                done.update(Kc)
                aff = [tuple(sorted((c, x))) for c in (a, b) for x in range(K) if x not in (a, b)]
                swap(col, Kc, a, b)
                gain = sum(comps(*q) for q in aff) - sum(base[q] for q in aff)
                swap(col, Kc, a, b)
                out.append(gain)
    return out


def kempe_gain(adj, col, Kc, a, b):
    """the gain of swap_gains for one (a, b)-component Kc, grown only from Kc: in each subgraph (c, x) the edges of
    Kc coloured c leave and those coloured o (the other one of a, b) join; every component that changes holds an edge
    of Kc or an x-coloured neighbour of one"""
    Kset = set(Kc)
    tot = 0
    for c, o in ((a, b), (b, a)):
        lc = [g for g in Kc if col[g] == c]
        lo = [g for g in Kc if col[g] == o]
        for x in range(K):
            if x == a or x == b:
                continue
            xc = [z for g in lc for z in adj[g] if col[z] == x]
            xo = [z for g in lo for z in adj[g] if col[z] == x]
            if not xc and not xo:
                tot += len(lo) - len(lc)
                continue
            for after, seeds in ((False, lc + xo), (True, lo + xc + xo)):
                seen, C = set(), 0
                for s0 in seeds:
                    if s0 in seen:
                        continue
                    C += 1
                    seen.add(s0)
                    stack = [s0]
                    while stack:
                        y = stack.pop()
                        for z in adj[y]:
                            if z in seen:
                                continue
                            cz = col[z]
                            if cz == x or (cz == c and z not in Kset) or (z in Kset and cz == (o if after else c)):
                                seen.add(z)
                                stack.append(z)
                tot += C if after else -C
    return tot


def all_gains(adj, col):
    """kempe_gain for every (a, b)-component, a < b, in the order of swap_gains"""
    out = []
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for s0 in range(len(adj)):
                if s0 in done or col[s0] not in (a, b):
                    continue
                Kc = component(adj, col, s0, a, b)
                done.update(Kc)
                out.append(kempe_gain(adj, col, Kc, a, b))
    return out


def swaps_job(job):
    name, adj, e, col = job
    g = swap_gains(adj, list(col))
    return {"name": name, "components": len(g), "raising": sum(v > 0 for v in g), "max": max(g),
            "hole max": max_delta(adj, col, e)}


def climb_job(job):
    """first-improvement ascent of the number of two-coloured components by Kempe swaps (the hole stays at e), from
    the given colouring; returns what e looks like at the local maximum"""
    name, adj, e, col, seed = job
    rng = random.Random(seed)
    col = list(col)
    m, steps = len(adj), 0
    pairs = [(a, b) for a in range(K) for b in range(a + 1, K)]

    def gain(Kc, a, b):
        aff = [tuple(sorted((c, x))) for c in (a, b) for x in range(K) if x not in (a, b)]
        before = sum(ncomp(adj, col, q) for q in aff)
        swap(col, Kc, a, b)
        after = sum(ncomp(adj, col, q) for q in aff)
        return after - before                                  # the swap is left applied

    while True:
        improved = False
        order = [(s0, a, b) for (a, b) in pairs for s0 in range(m) if col[s0] in (a, b)]
        rng.shuffle(order)
        seen = set()
        for s0, a, b in order:
            if (s0, a, b) in seen or col[s0] not in (a, b):
                continue
            Kc = component(adj, col, s0, a, b)
            seen.update((g, a, b) for g in Kc)
            if gain(Kc, a, b) > 0:
                improved, steps = True, steps + 1
            else:
                swap(col, Kc, a, b)                            # undo
        if not improved:
            break
    nt, nn = classify(adj, col, e)
    colours = len({col[f] for f in adj[e]})
    seen = Counter(len({col[g] for g in adj[f] if col[g] >= 0}) for f in range(m) if f != e)
    return {"name": name, "seed": seed, "steps": steps, "colours on N(e)": colours, "trivial": nt,
            "non-trivial": nn, "stuck": colours == K and nt + nn == 0,
            "colours seen by the other edges": dict(sorted(seen.items()))}


def stuck_climb_job(job):
    """the adversary for the fragmentation question: raise the number of two-coloured components by Kempe swaps that
    keep e depth-1 stuck, until none is left; then count the swaps that still raise it (they all unstick e)"""
    name, adj, e, col, seed = job
    rng = random.Random(seed)
    col = list(col)
    m, steps, gained = len(adj), 0, 0
    pairs = [(a, b) for a in range(K) for b in range(a + 1, K)]
    while True:
        improved = False
        order = [(s0, a, b) for (a, b) in pairs for s0 in range(m) if col[s0] in (a, b)]
        rng.shuffle(order)
        seen = set()
        for s0, a, b in order:
            if (s0, a, b) in seen or col[s0] not in (a, b):
                continue
            Kc = component(adj, col, s0, a, b)
            seen.update((g, a, b) for g in Kc)
            aff = [tuple(sorted((c, x))) for c in (a, b) for x in range(K) if x not in (a, b)]
            before = sum(ncomp(adj, col, q) for q in aff)
            swap(col, Kc, a, b)
            g = sum(ncomp(adj, col, q) for q in aff) - before
            if g > 0 and len({col[f] for f in adj[e]}) == K and sum(classify(adj, col, e)) == 0:
                improved, steps, gained = True, steps + 1, gained + g
            else:
                swap(col, Kc, a, b)
        if not improved:
            break
    gains = swap_gains(adj, list(col))
    return {"name": name, "steps": steps, "gained": gained, "stuck": sum(classify(adj, col, e)) == 0,
            "raising swaps left": sum(v > 0 for v in gains), "largest gain left": max(gains),
            "hole max": max_delta(adj, col, e), "col": col}


def blocked_ascent(adj, col, e, rng):
    """raise the number of two-coloured components by Kempe swaps that keep e blocked, until none is left (col is
    changed in place); returns the swaps made, their total gain, and (gain, size, members of N(e)) for every raising
    swap left.  The last pass applies nothing, so what it rejected is exactly the raising swaps left"""
    m, steps, gained = len(adj), 0, 0
    pairs = [(a, b) for a in range(K) for b in range(a + 1, K)]
    Ne = set(adj[e])
    while True:
        improved, left = False, []
        order = [(s0, a, b) for (a, b) in pairs for s0 in range(m) if col[s0] in (a, b)]
        rng.shuffle(order)
        seen = set()
        for s0, a, b in order:
            if (s0, a, b) in seen or col[s0] not in (a, b):
                continue
            Kc = component(adj, col, s0, a, b)
            seen.update((g, a, b) for g in Kc)
            g = kempe_gain(adj, col, Kc, a, b)
            if g <= 0:
                continue
            swap(col, Kc, a, b)
            if Ne.isdisjoint(Kc) or len({col[f] for f in Ne}) == K:
                improved, steps, gained = True, steps + 1, gained + g
            else:
                swap(col, Kc, a, b)
                left.append((g, len(Kc), len(Ne.intersection(Kc))))
        if not improved:
            return steps, gained, left


def blocked_climb_job(job):
    """the adversary for the strong form (a local maximum never blocks e): blocked_ascent from one state.  A swap can
    unblock e only if its component holds members of N(e), so every raising swap left frees a colour at e; none left
    would be a local maximum with e blocked.  Reports the raising swaps left and whether e is still depth-1 stuck"""
    name, adj, e, col, seed = job
    rng = random.Random(seed)
    col = list(col)
    Ne = set(adj[e])
    steps, gained, left = blocked_ascent(adj, col, e, rng)
    return {"name": name, "steps": steps, "gained": gained, "blocked": len({col[f] for f in Ne}) == K,
            "stuck": sum(classify(adj, col, e)) == 0, "raising swaps left": len(left),
            "largest gain left": max((x[0] for x in left), default=0),
            "sizes of the raising components": sorted(x[1] for x in left)[:12],
            "members of N(e) in them": dict(Counter(x[2] for x in left)), "col": col}


def hop_job(job):
    """basin hopping on the number of raising swaps blocked_ascent leaves: a few random swaps within L2-distance 3 of
    e that keep e blocked, then the ascent again, accepted by simulated annealing on that number.  Zero is a local
    maximum with e blocked; it is re-checked with the full recount swap_gains and written to exp48_found.jsonl"""
    name, adj, e, col, seed, hops = job
    rng = random.Random(seed)
    col = list(col)
    Ne = set(adj[e])
    region = set(adj[e])
    for _ in range(2):
        for f in list(region):
            region.update(adj[f])
    region.discard(e)
    region = sorted(region)
    E = best = start = len(blocked_ascent(adj, col, e, rng)[2])
    accepted = t = 0
    for t in range(hops):
        if E == 0:
            break
        T = 1.5 * (1 - t / hops) + 0.1
        old = list(col)
        for _ in range(rng.randint(1, 4)):
            f = rng.choice(region)
            c = rng.randrange(K)
            a = col[f]
            if c == a:
                continue
            Kc = component(adj, col, f, a, c)
            swap(col, Kc, a, c)
            if len({col[g] for g in Ne}) < K:
                swap(col, Kc, a, c)
        E2 = len(blocked_ascent(adj, col, e, rng)[2])
        if E2 <= E or rng.random() < math.exp((E - E2) / T):
            E, accepted = E2, accepted + 1
            if E < best:
                best = E
                print(f"{name}: hop {t + 1}, {E} raising swaps left", flush=True)
        else:
            col[:] = old
    out = {"name": name, "start": start, "best": best, "end": E, "hops": t + 1, "accepted": accepted}
    if E == 0:
        gains = swap_gains(adj, list(col))
        out.update(checked_blocked=len({col[f] for f in Ne}) == K, checked_max_gain=max(gains),
                   stuck=sum(classify(adj, col, e)) == 0)
        with open("exp48_found.jsonl", "a", encoding="utf-8") as fh:
            fh.write(json.dumps({**out, "e": e, "col": col}) + "\n")
    return out


def raising_anneal_job(job):
    """after stuck_climb_job: simulated annealing on the number of raising swaps, through swaps of components within
    L2-distance 3 of e that keep e depth-1 stuck; 0 would be a stuck local maximum"""
    name, adj, e, col, seed, steps = job
    r0 = stuck_climb_job((name, adj, e, col, seed))
    col = r0["col"]
    rng = random.Random(seed)
    region = set(adj[e])
    for _ in range(2):
        for f in list(region):
            region.update(adj[f])
    region.discard(e)
    region = sorted(region)
    E = best = sum(v > 0 for v in swap_gains(adj, list(col)))
    start, accepted = E, 0
    for t in range(steps):
        T = 8.0 * (1 - t / steps) + 0.5
        f = rng.choice(region)
        c = rng.randrange(K)
        if c == col[f]:
            continue
        a = col[f]
        Kc = component(adj, col, f, a, c)
        swap(col, Kc, a, c)
        if len({col[g] for g in adj[e]}) < K or sum(classify(adj, col, e)) > 0:
            swap(col, Kc, a, c)
            continue
        E2 = sum(v > 0 for v in swap_gains(adj, list(col)))
        if E2 <= E or rng.random() < math.exp((E - E2) / T):
            E, accepted = E2, accepted + 1
            best = min(best, E)
            if E == 0:
                break
        else:
            swap(col, Kc, a, c)
    return {"name": name, "after stuck climb": start, "best": best, "end": E, "accepted": accepted,
            "steps": t + 1, "col": col}


def small_job(job):
    """every edge h of one small graph, reps random colourings of G - h each, climbed to a local maximum"""
    from exp33_kempe import l2_adj
    from exp33b_adversary import colour_all_but
    gi, edges, reps = job
    adj = l2_adj(edges)
    out = Counter()
    bad = []
    for h in range(len(edges)):
        for r in range(reps):
            rc, tries = None, 0
            while rc is None and tries < 50:
                rc, tries = colour_all_but(adj, h, random.Random(100000 * gi + 1000 * h + 50 * r + tries)), tries + 1
            if rc is None:
                out["no colouring found"] += 1
                continue
            res = climb_job(("", adj, h, rc, r))
            out["local maxima"] += 1
            out["h blocked"] += res["colours on N(e)"] == K
            out["h stuck"] += res["stuck"]
            if res["stuck"]:
                bad.append((gi, h, r))
    return gi, dict(out), bad


def ncomp(adj, col, q):
    c1, c2 = q
    seen, C = set(), 0
    for s0 in range(len(adj)):
        if s0 in seen or col[s0] not in (c1, c2):
            continue
        C += 1
        seen.add(s0)
        stack = [s0]
        while stack:
            y = stack.pop()
            for z in adj[y]:
                if z not in seen and col[z] in (c1, c2):
                    seen.add(z)
                    stack.append(z)
    return C


def end_states(dirs):
    for d in dirs:
        meta = json.load(open(f"{d}/meta.json", encoding="utf-8"))["meta"]
        xs, per = build_instances(parse_specs(meta["spec"])), meta["per"]
        with np.load(f"{d}/state.npz") as st:
            bE, bc = st["bestEs"], st["bcls"]
        for i, x in enumerate(xs):
            c = i * per + int(np.argmin(bE[i * per:(i + 1) * per]))
            yield x, list(from_bits(bc[c], len(x["adj"])))


if __name__ == "__main__" and sys.argv[1] == "girth":
    from exp33_kempe import l2_adj
    from exp33b_adversary import colour_all_but
    from graphs_hg import random_girth
    jobs = []
    for spec in sys.argv[3:]:
        nn, g, seeds = map(int, spec.split(":"))
        for sd in range(seeds):
            G = random_girth(nn, g, sd)
            if G is None:
                continue
            edges = [tuple(x) for x in G.edges()]
            adj = l2_adj(edges)
            for r in range(int(sys.argv[2])):
                e = random.Random(sd * 100 + r).randrange(len(edges))
                rc = None
                while rc is None:
                    rc = colour_all_but(adj, e, random.Random(sd * 1000 + r))
                jobs.append((f"n={nn} girth={g} seed={sd} edge {e} from a random colouring", adj, e, rc, r))
    with Pool(min(22, len(jobs))) as pool:
        for r in pool.imap_unordered(climb_job, jobs):
            print(json.dumps(r), flush=True)
elif __name__ == "__main__" and sys.argv[1] == "small":
    from exp33_kempe import load
    reps = int(sys.argv[2])
    for nn in map(int, sys.argv[3].split(",")):
        jobs = [(gi, edges, reps) for gi, edges in enumerate(load(nn))]
        tot, bads = Counter(), []
        with Pool(22) as pool:
            for gi, out, bad in pool.imap_unordered(small_job, jobs):
                tot.update(out)
                bads += bad
        print(f"n = {nn}: {len(jobs)} graphs; {dict(tot)}; stuck at a local maximum: {bads[:20]}", flush=True)
elif __name__ == "__main__" and sys.argv[1] == "raising":
    steps = int(sys.argv[2])
    jobs = [(x["name"], x["adj"], x["e"], col, i, steps) for i, (x, col) in enumerate(end_states(sys.argv[3:]))]
    with Pool(22) as pool:
        for r in pool.imap_unordered(raising_anneal_job, jobs):
            col = r.pop("col")
            print(json.dumps(r), flush=True)
            if r["end"] == 0:
                with open("exp48_found.jsonl", "a", encoding="utf-8") as fh:
                    fh.write(json.dumps({**r, "col": col}) + "\n")
elif __name__ == "__main__" and sys.argv[1] == "hop":
    hops, workers = int(sys.argv[2]), int(sys.argv[3])
    jobs = [(x["name"], x["adj"], x["e"], col, i, hops) for i, (x, col) in enumerate(end_states(sys.argv[4:]))]
    with Pool(min(workers, len(jobs))) as pool:
        for r in pool.imap_unordered(hop_job, jobs):
            print(json.dumps(r), flush=True)
elif __name__ == "__main__" and sys.argv[1] == "blockedclimb":
    jobs = [(x["name"], x["adj"], x["e"], col, i) for i, (x, col) in enumerate(end_states(sys.argv[2:]))]
    with Pool(min(22, len(jobs))) as pool:
        for r in pool.imap_unordered(blocked_climb_job, jobs):
            col = r.pop("col")
            print(json.dumps(r), flush=True)
            if r["raising swaps left"] == 0:
                with open("exp48_found.jsonl", "a", encoding="utf-8") as fh:
                    fh.write(json.dumps({**r, "col": col}) + "\n")
elif __name__ == "__main__" and sys.argv[1] == "stuckclimb":
    jobs = [(x["name"], x["adj"], x["e"], col, i) for i, (x, col) in enumerate(end_states(sys.argv[2:]))]
    with Pool(22) as pool:
        for r in pool.imap_unordered(stuck_climb_job, jobs):
            col = r.pop("col")
            print(json.dumps(r), flush=True)
            if r["raising swaps left"] == 0:
                with open("exp48_found.jsonl", "a", encoding="utf-8") as fh:
                    fh.write(json.dumps({**r, "col": col}) + "\n")
elif __name__ == "__main__" and sys.argv[1] == "climb":
    from exp33b_adversary import colour_all_but
    reps = int(sys.argv[2])
    jobs = []
    for i, (x, col) in enumerate(end_states(sys.argv[3:])):
        jobs.append((x["name"] + " from the stuck state", x["adj"], x["e"], col, i))
        for r in range(reps):
            rc = None
            while rc is None:
                rc = colour_all_but(x["adj"], x["e"], random.Random(1000 * i + r))
            jobs.append((x["name"] + " from a random colouring", x["adj"], x["e"], rc, 1000 * i + r))
    with Pool(22) as pool:
        for r in pool.imap_unordered(climb_job, jobs):
            print(json.dumps(r), flush=True)
elif __name__ == "__main__" and sys.argv[1] == "swaps":
    jobs = [(x["name"], x["adj"], x["e"], col) for x, col in end_states(sys.argv[2:])]
    found = [json.loads(l) for l in open(sys.argv[-1], encoding="utf-8")] if sys.argv[-1].endswith(".jsonl") else []
    if found:
        jobs = [(x["name"], x["adj"], x["e"], col) for x, col in end_states(sys.argv[2:-1])]
        inst = {j[0]: j for j in jobs}
        jobs += [(r["name"] + " (no beta-raising hole move)", inst[r["name"]][1], inst[r["name"]][2], r["col"])
                 for r in found]
    with Pool(min(22, len(jobs))) as pool:
        for r in pool.imap_unordered(swaps_job, jobs):
            print(json.dumps(r), flush=True)
elif __name__ == "__main__" and sys.argv[1] == "attack":
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
