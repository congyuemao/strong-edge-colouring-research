"""exp38: exp33b's adversary (search for Kempe-stuck blocked edges) on the GPU, tens of thousands of chains at once.

Same search as exp33b: for a graph G and an edge e, a strong 20-colouring of G - e is annealed on
    energy = 10 * (#colours missing from N(e)) + 190   if some colour is missing,
             #separable colour pairs at e              otherwise,
with the moves "recolour an edge within L^2-distance 2 of e to a free colour" and "Kempe swap at such an edge"
(each with probability 1/2) and temperature 2 (1 - t/L) + 0.05 over a run of L steps.  Energy 0 = depth-1 stuck.

GPU side (OpenCL through gpu_cl.py): one work-item per chain.  A colouring is stored as 20 bitsets over the edges
(W 32-bit words each) and L^2 as one bitset row per edge, so a component search is word operations:
    frontier node x:  new = adj[x] & (class a | class b) & ~visited;  meets B iff new & N(e) & class b != 0.
A move changes colours p, q only, so only the 37 pairs containing p or q are re-tested (marked dirty, re-tested once
no colour is missing).  Chains reheat (t = 0) after every run and keep their best state.  A chain that reaches
energy 0 stops; the host re-checks the state with exp33b's CPU code (energy, depth 2, swap sequences up to depth 3),
logs it to found.jsonl and restarts the chain from another chain's colouring.

Parallel tempering (KIL_GPU_PT = R rungs): instead of cooling schedules, the chains of each edge form ladders of
R fixed temperatures, geometric from KIL_GPU_TMIN (0.05) to KIL_GPU_TMAX (2.0).  After every launch the host
proposes swaps between neighbouring rungs (even and odd pairs alternately), accepted with probability
min(1, exp((1/T_a - 1/T_b)(E_a - E_b))); a swap exchanges the two chains' temperatures, not their colourings.

Weighted energy (KIL_GPU_WT, KIL_GPU_WN, default 1 and 1): energy = wT * #trivial + wN * #non-trivial separable
pairs, where a separable pair (a, b) is trivial if the a-members or the b-members of N(e) see no edge of the other
colour (so the swap only recolours members of N(e)).  With wT >> wN the hunt minimises the non-trivial pairs among
states without trivial ones, and the other way round; the defaults give the plain count.

KIL2-single mode (KIL_GPU_GCAP = G > 0): energy += min(#good single recolourings, G) at depth-1 stuck states and
+= G elsewhere, where a single recolouring changes one edge f of N(e) to a colour free at f, and is good if some pair
is then separable at e.  Energy 0 = stuck and no single recolouring followed by one pair swap frees a colour.
With KIL_GPU_GMODE=2 the term counts all good first moves (Kempe swaps of an (a, b)-component meeting N(e), after
which some pair is separable); energy 0 is then a KIL2 counterexample.

Output directory: log lines on stdout, best.json (best energy per edge), found.jsonl, state.npz + meta.json
(checkpoint every 2 minutes and at the end; a restart with the same arguments resumes).  At every checkpoint the
best state of each edge is re-checked on the CPU.

Usage: exp38_gpu_adversary.py run <outdir> <spec,...> [chains_per_edge] [minutes]
       exp38_gpu_adversary.py selftest                  GPU energies and pair bits vs the CPU code
       exp38_gpu_adversary.py bench <spec>              steps per second, GPU vs exp33b on the CPU
  spec  r:n:girth:seeds:edges   random graphs (exp33b's random mode), seeds 0..seeds-1, that many edges each
        s:n:i1/i2/..:edges      graphs number i1, i2, .. of graphs_n<n>.txt
        e:n:girth:seed:e1/e2..  given edges of one random graph (as exp37 builds it)
Run lengths L cycle through KIL_GPU_L (default "60000,480000,4000000") over the chains.
"""
import json
import os
import random
import sys
import time

import networkx as nx
import numpy as np

from exp33_kempe import K, l2_adj, depth_two, load, separable, component, swap
from exp33b_adversary import colour_all_but, energy, deep_search, anneal as cpu_anneal
from gpu_cl import GPU

NW = 6                                                         # 32-bit words for the 190 pair bits
SRC = r"""
#define K 20
#define NPAIR 190
#define FORW for (int w = 0; w < W; w++)
#ifndef GCAP
#define GCAP 0
#endif
#ifndef GMODE
#define GMODE 1
#endif

inline uint rnd(ulong *s) {
    ulong x = *s;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    *s = x;
    return (uint)((x * 0x2545F4914F6CDD1DUL) >> 32);
}

inline float rndf(ulong *s) { return (float)(rnd(s) >> 8) * (1.0f / 16777216.0f); }

inline int low_bit(uint v) { return 31 - clz(v & (0u - v)); }

/* 0 if some (a,b)-component meets both the a- and the b-coloured members of N(e); otherwise 2 if the pair is
   trivial (the a-members or the b-members see no edge of the other colour), else 1 */
int separable(__global const uint *adj, const uint *Nm, const uint *cls, int a, int b) {
    uint S[W], vis[W], fr[W], Bm[W];
    FORW {
        uint ca = cls[a * W + w], cb = cls[b * W + w];
        S[w] = ca | cb;
        Bm[w] = Nm[w] & cb;
        vis[w] = fr[w] = Nm[w] & ca;
    }
    for (;;) {
        int x = -1;
        FORW if (fr[w]) { x = 32 * w + low_bit(fr[w]); fr[w] &= fr[w] - 1; break; }
        if (x < 0) break;
        __global const uint *row = adj + x * W;
        FORW {
            uint nb = row[w] & S[w] & ~vis[w];
            if (nb & Bm[w]) return 0;
            vis[w] |= nb;
            fr[w] |= nb;
        }
    }
    int ta = 1, tb = 1;
    FORW {
        uint Am = Nm[w] & cls[a * W + w], Bq = Nm[w] & cls[b * W + w];
        while (Am) {
            __global const uint *row = adj + (32 * w + low_bit(Am)) * W;
            Am &= Am - 1;
            for (int v = 0; v < W; v++) if (row[v] & cls[b * W + v]) ta = 0;
        }
        while (Bq) {
            __global const uint *row = adj + (32 * w + low_bit(Bq)) * W;
            Bq &= Bq - 1;
            for (int v = 0; v < W; v++) if (row[v] & cls[a * W + v]) tb = 0;
        }
    }
    return (ta || tb) ? 2 : 1;
}

/* the (p,q)-component of edge f, as a bitset */
void kcomp(__global const uint *adj, const uint *cls, int f, int p, int q, uint *comp) {
    uint S[W], fr[W];
    FORW { S[w] = cls[p * W + w] | cls[q * W + w]; comp[w] = fr[w] = 0; }
    comp[f >> 5] = fr[f >> 5] = 1u << (f & 31);
    for (;;) {
        int x = -1;
        FORW if (fr[w]) { x = 32 * w + low_bit(fr[w]); fr[w] &= fr[w] - 1; break; }
        if (x < 0) return;
        __global const uint *row = adj + x * W;
        FORW {
            uint nb = row[w] & S[w] & ~comp[w];
            comp[w] |= nb;
            fr[w] |= nb;
        }
    }
}

int count_in_N(const uint *Nm, const uint *cls, int c) {
    int s = 0;
    FORW s += popcount(cls[c * W + w] & Nm[w]);
    return s;
}

/* KIL2-single: the number of recolourings f -> q (f in N(e), q free at f) after which some pair containing the old
   colour p or q is separable at e; cls is restored */
int good_singles(__global const uint *adj, const uint *Nm, uint *cls) {
    int g = 0;
    for (int w = 0; w < W; w++) {
        uint bits = Nm[w];
        while (bits) {
            int f = 32 * w + low_bit(bits);
            bits &= bits - 1;
            uint fb = 1u << (f & 31);
            int p = 0;
            while (!(cls[p * W + w] & fb)) p++;
            __global const uint *row = adj + f * W;
            uint used = 0;
            for (int cc = 0; cc < K; cc++) {
                uint any = 0;
                for (int v = 0; v < W; v++) any |= row[v] & cls[cc * W + v];
                if (any) used |= 1u << cc;
            }
            uint fr = ~used & 0xFFFFFu & ~(1u << p);
            while (fr) {
                int q = low_bit(fr);
                fr &= fr - 1;
                cls[p * W + w] &= ~fb;
                cls[q * W + w] |= fb;
                int ok = 0;
                for (int x = 0; x < K && !ok; x++) {
                    if (x != p) ok = separable(adj, Nm, cls, min(p, x), max(p, x)) != 0;
                    if (!ok && x != p && x != q) ok = separable(adj, Nm, cls, min(q, x), max(q, x)) != 0;
                }
                cls[q * W + w] &= ~fb;
                cls[p * W + w] |= fb;
                g += ok;
            }
        }
    }
    return g;
}

/* KIL2: the number of first moves (Kempe swaps of an (a,b)-component meeting N(e)) after which some pair containing
   a or b is separable at e; cls is restored */
int good_first_moves(__global const uint *adj, const uint *Nm, uint *cls) {
    int g = 0;
    for (int a = 0; a < K; a++)
        for (int b = a + 1; b < K; b++) {
            uint done[W], comp[W];
            FORW done[w] = 0;
            for (;;) {
                int f = -1;
                FORW {
                    uint cand = Nm[w] & (cls[a * W + w] | cls[b * W + w]) & ~done[w];
                    if (cand) { f = 32 * w + low_bit(cand); break; }
                }
                if (f < 0) break;
                kcomp(adj, cls, f, a, b, comp);
                FORW {
                    done[w] |= comp[w];
                    uint x = (cls[a * W + w] & comp[w]) ^ (cls[b * W + w] & comp[w]);
                    cls[a * W + w] ^= x;
                    cls[b * W + w] ^= x;
                }
                int ok = 0;
                for (int x = 0; x < K && !ok; x++) {
                    if (x != a) ok = separable(adj, Nm, cls, min(a, x), max(a, x)) != 0;
                    if (!ok && x != a && x != b) ok = separable(adj, Nm, cls, min(b, x), max(b, x)) != 0;
                }
                FORW {
                    uint x = (cls[a * W + w] & comp[w]) ^ (cls[b * W + w] & comp[w]);
                    cls[a * W + w] ^= x;
                    cls[b * W + w] ^= x;
                }
                g += ok;
            }
        }
    return g;
}

int energy(__global const uint *adj, const uint *Nm, uint *cls, const uchar *cnt, uint *sep, uint *tr,
           uint *dirty, int wT, int wN) {
    int miss = 0;
    for (int c = 0; c < K; c++) miss += (cnt[c] == 0);
    if (miss) return (10 * miss + NPAIR) * max(wT, wN) + GCAP;
    if (*dirty) {
        int k = 0;
        for (int a = 0; a < K; a++)
            for (int b = a + 1; b < K; b++, k++)
                if (((*dirty >> a) | (*dirty >> b)) & 1u) {
                    int r = separable(adj, Nm, cls, a, b);
                    if (r) sep[k >> 5] |= 1u << (k & 31);
                    else sep[k >> 5] &= ~(1u << (k & 31));
                    if (r == 2) tr[k >> 5] |= 1u << (k & 31);
                    else tr[k >> 5] &= ~(1u << (k & 31));
                }
        *dirty = 0;
    }
    int ns = 0, nt = 0;
    for (int i = 0; i < 6; i++) {
        ns += popcount(sep[i]);
        nt += popcount(tr[i]);
    }
    int E1 = wN * (ns - nt) + wT * nt;
    if (GCAP == 0) return E1;
    return E1 + (E1 ? GCAP : min(GMODE == 2 ? good_first_moves(adj, Nm, cls) : good_singles(adj, Nm, cls), GCAP));
}

/* inst: 8 ints per instance: m, e, adjacency base (words), N(e) mask base (words), region base, |region|, -, - */
#define ARGS                                                                        \
    __global const int *inst, __global const uint *adj_all, __global const uint *Nm_all, \
    __global const ushort *R_all, __global const int *cinst, __global uint *cls_all, __global uint *bcls_all, \
    __global uint *seps, __global uint *trivs, __global uint *dirtys, __global int *Es, __global int *bestEs, \
    __global uint *ts, __global const uint *Ls, __global const float *Tfix, __global ulong *rngs,         \
    __global int *found, int nch

#define SETUP                                                                       \
    int c = get_global_id(0);                                                       \
    if (c >= nch) return;                                                           \
    __global const int *I = inst + 8 * cinst[c];                                    \
    __global const uint *adj = adj_all + I[2];                                      \
    __global const ushort *R = R_all + I[4];                                        \
    int nR = I[5];                                                                  \
    uint Nm[W];                                                                     \
    FORW Nm[w] = Nm_all[I[3] + w];                                                  \
    __global uint *gcls = cls_all + (long)c * K * W;                                \
    __global uint *gbcls = bcls_all + (long)c * K * W;                              \
    uint cls[K * W];                                                                \
    for (int i = 0; i < K * W; i++) cls[i] = gcls[i];                               \
    uchar cnt[K];                                                                   \
    for (int j = 0; j < K; j++) cnt[j] = (uchar)count_in_N(Nm, cls, j);

/* only_flagged: (re)start just the chains with found == 2 */
__kernel void init(ARGS, int only_flagged, int wT, int wN) {
    SETUP
    if (only_flagged && found[c] != 2) return;
    uint sep[6] = {0, 0, 0, 0, 0, 0}, tr[6] = {0, 0, 0, 0, 0, 0};
    uint dirty = 0xFFFFFu;
    int E = energy(adj, Nm, cls, cnt, sep, tr, &dirty, wT, wN);
    for (int i = 0; i < 6; i++) {
        seps[6 * c + i] = sep[i];
        trivs[6 * c + i] = tr[i];
    }
    dirtys[c] = dirty;
    Es[c] = E;
    bestEs[c] = E;
    for (int i = 0; i < K * W; i++) gbcls[i] = cls[i];
    ts[c] = 0;
    found[c] = (E == 0);
}

/* from-scratch energy and pair bits, for checking the incremental state */
__kernel void evaluate(ARGS, __global int *outE, __global uint *outsep, int wT, int wN) {
    SETUP
    uint sep[6] = {0, 0, 0, 0, 0, 0}, tr[6] = {0, 0, 0, 0, 0, 0};
    uint dirty = 0xFFFFFu;
    outE[c] = energy(adj, Nm, cls, cnt, sep, tr, &dirty, wT, wN);
    for (int i = 0; i < 6; i++) outsep[6 * c + i] = dirty ? 0xFFFFFFFFu : sep[i];
}

__kernel void anneal(ARGS, int steps, float T0, float T1, int wT, int wN) {
    SETUP
    if (found[c]) return;
    ulong rng = rngs[c];
    int E = Es[c], bestE = bestEs[c];
    uint t = ts[c], L = Ls[c], dirty = dirtys[c];
    float Tc = Tfix[c];                                   /* used when L == 0 (parallel tempering) */
    uint sep[6], tr[6];
    for (int i = 0; i < 6; i++) {
        sep[i] = seps[6 * c + i];
        tr[i] = trivs[6 * c + i];
    }
    for (int s = 0; s < steps; s++) {
        float T = Tc;
        if (L) {
            T = T0 * (1.0f - (float)t / (float)L) + T1;
            if (++t >= L) t = 0;
        }
        int f = R[rnd(&rng) % (uint)nR];
        int fw = f >> 5;
        uint fb = 1u << (f & 31);
        int p = 0;
        while (!(cls[p * W + fw] & fb)) p++;
        int kind = rnd(&rng) & 1, q;
        if (kind == 0) {                                   /* recolour f to a free colour */
            __global const uint *row = adj + f * W;
            uint used = 0;
            for (int cc = 0; cc < K; cc++) {
                uint any = 0;
                FORW any |= row[w] & cls[cc * W + w];
                if (any) used |= 1u << cc;
            }
            uint fr = ~used & 0xFFFFFu & ~(1u << p);
            if (!fr) continue;
            int r = rnd(&rng) % (uint)popcount(fr);
            for (q = 0; q < K; q++)
                if ((fr >> q) & 1u) {
                    if (r == 0) break;
                    r--;
                }
        } else {
            q = rnd(&rng) % K;
            if (q == p) continue;
        }
        uint oP[W], oQ[W], osep[6], otr[6], odirty = dirty;
        uchar ocp = cnt[p], ocq = cnt[q];
        FORW { oP[w] = cls[p * W + w]; oQ[w] = cls[q * W + w]; }
        for (int i = 0; i < 6; i++) {
            osep[i] = sep[i];
            otr[i] = tr[i];
        }
        if (kind == 0) {
            cls[p * W + fw] &= ~fb;
            cls[q * W + fw] |= fb;
        } else {                                           /* Kempe swap of the (p,q)-component at f */
            uint comp[W];
            kcomp(adj, cls, f, p, q, comp);
            FORW {
                uint x = (cls[p * W + w] & comp[w]) ^ (cls[q * W + w] & comp[w]);
                cls[p * W + w] ^= x;
                cls[q * W + w] ^= x;
            }
        }
        cnt[p] = (uchar)count_in_N(Nm, cls, p);
        cnt[q] = (uchar)count_in_N(Nm, cls, q);
        dirty |= (1u << p) | (1u << q);
        int E2 = energy(adj, Nm, cls, cnt, sep, tr, &dirty, wT, wN);
        if (E2 <= E || rndf(&rng) < native_exp((float)(E - E2) / T)) {
            E = E2;
            if (E < bestE) {
                bestE = E;
                for (int i = 0; i < K * W; i++) gbcls[i] = cls[i];
                if (E == 0) { found[c] = 1; break; }
            }
        } else {
            FORW { cls[p * W + w] = oP[w]; cls[q * W + w] = oQ[w]; }
            cnt[p] = ocp;
            cnt[q] = ocq;
            for (int i = 0; i < 6; i++) {
                sep[i] = osep[i];
                tr[i] = otr[i];
            }
            dirty = odirty;
        }
    }
    for (int i = 0; i < K * W; i++) gcls[i] = cls[i];
    rngs[c] = rng;
    Es[c] = E;
    bestEs[c] = bestE;
    ts[c] = t;
    dirtys[c] = dirty;
    for (int i = 0; i < 6; i++) {
        seps[6 * c + i] = sep[i];
        trivs[6 * c + i] = tr[i];
    }
}
"""


def parse_specs(text):
    out = []
    for spec in text.split(","):
        kind, *f = spec.split(":")
        if kind == "r":
            n, g, seeds, ne = map(int, f)
            out += [("r", n, g, s, ne) for s in range(seeds)]
        elif kind == "s":
            out += [("s", int(f[0]), 0, int(i), int(f[2])) for i in f[1].split("/")]
        elif kind == "e":
            out += [("r", int(f[0]), int(f[1]), int(f[2]), [int(e) for e in f[3].split("/")])]
        else:
            raise ValueError(spec)
    return out


def build_instances(specs):
    from graphs_hg import random_girth
    insts, small = [], {}
    for kind, n, g, s, ne in specs:
        if kind == "r":
            G = random_girth(n, g, s) if g > 3 else nx.random_regular_graph(4, n, seed=s)
            if G is None:
                continue
            edges, name = [tuple(x) for x in G.edges()], f"n={n} girth={nx.girth(G)} seed={s}"
        else:
            if n not in small:
                small[n] = list(load(n))
            edges, name = small[n][s], f"n={n} #{s}"
        adj = l2_adj(edges)
        cand = [e for e in range(len(adj)) if len(adj[e]) >= K]
        random.Random(1000 * n + s).shuffle(cand)
        for e in (ne if isinstance(ne, list) else cand[:ne]):
            insts.append({"name": f"{name} edge {e}", "edges": edges, "adj": adj, "e": e,
                          "spec": f"e:{n}:{g}:{s}:{e}" if kind == "r" else None})
    return insts


def to_bits(col, W):
    out = np.zeros((K, W), np.uint32)
    for h, c in enumerate(col):
        if c >= 0:
            out[c, h >> 5] |= np.uint32(1 << (h & 31))
    return out


def from_bits(bits, m):
    col = [-1] * m
    for c in range(K):
        for w, v in enumerate(bits[c].tolist()):
            while v:
                b = v & -v
                col[32 * w + b.bit_length() - 1] = c
                v ^= b
    return col


class Hunt:
    def __init__(self, insts, per, Ls, seed=1, gpu=None, rungs=0, Tmin=0.05, Tmax=2.0, wT=1, wN=1, gcap=0, gmode=1):
        self.insts, self.per, self.rungs, self.gcap, self.gmode = insts, per, rungs, gcap, gmode
        self.w = (np.int32(wT), np.int32(wN))
        self.g = gpu or GPU()
        self.W = W = (max(len(x["adj"]) for x in insts) + 31) // 32
        inst, adj_all, Nm_all, R = [], [], [], []
        for x in insts:
            adj, e, m = x["adj"], x["e"], len(x["adj"])
            region = set(adj[e])
            for f in list(region):
                region.update(adj[f])
            region.discard(e)
            x["region"] = sorted(region)
            inst += [m, e, len(adj_all), len(Nm_all), len(R), len(region), 0, 0]
            for h in range(m):
                adj_all += to_bits([0 if g in adj[h] else -1 for g in range(m)], W)[0].tolist()
            Nm_all += to_bits([0 if g in adj[e] else -1 for g in range(m)], W)[0].tolist()
            R += x["region"]
        self.nch = nch = per * len(insts)
        rng = random.Random(seed)
        cls = np.zeros((nch, K, W), np.uint32)
        for i, x in enumerate(insts):
            starts = []
            while len(starts) < min(per, 16):
                c0 = colour_all_but(x["adj"], x["e"], rng)
                if c0 is not None:
                    starts.append(to_bits(c0, W))
            cls[i * per:(i + 1) * per] = np.array(starts)[np.arange(per) % len(starts)]
        a = lambda v, t: np.array(v, dtype=t)
        self.static = [self.g.buffer(a(inst, np.int32)), self.g.buffer(a(adj_all, np.uint32)),
                       self.g.buffer(a(Nm_all, np.uint32)), self.g.buffer(a(R, np.uint16))]
        self.h = {
            "cinst": np.repeat(np.arange(len(insts), dtype=np.int32), per),
            "cls": cls, "bcls": cls.copy(), "seps": np.zeros(NW * nch, np.uint32),
            "trivs": np.zeros(NW * nch, np.uint32),
            "dirtys": np.zeros(nch, np.uint32), "Es": np.zeros(nch, np.int32), "bestEs": np.zeros(nch, np.int32),
            "ts": np.zeros(nch, np.uint32), "Ls": np.array([Ls[j % len(Ls)] for j in range(nch)], np.uint32),
            "Tfix": np.zeros(nch, np.float32),
            "rngs": np.random.default_rng(seed).integers(1, 2 ** 63, nch, dtype=np.uint64),
            "found": np.zeros(nch, np.int32)}
        if rungs:
            assert per % rungs == 0
            ladder = Tmin * (Tmax / Tmin) ** (np.arange(rungs) / (rungs - 1))
            self.h["Ls"][:] = 0
            self.h["Tfix"][:] = np.tile(ladder, nch // rungs).astype(np.float32)
            self.swaps = [0, 0]
        self.names = list(self.h)
        self.b = {k: self.g.buffer(v) for k, v in self.h.items()}
        prog = self.g.build(SRC, f"-D W={W} -D GCAP={gcap} -D GMODE={gmode}")
        self.k_init, self.k_eval, self.k_anneal = prog.kernel("init"), prog.kernel("evaluate"), prog.kernel("anneal")
        self.k_init(nch, *self.args(), np.int32(0), *self.w)

    def args(self):
        return self.static + [self.b[k] for k in self.names] + [np.int32(self.nch)]

    def get(self, *keys):
        return [self.g.read(self.b[k], self.h[k]) for k in keys]

    def put(self, *keys):
        for k in keys:
            self.g.write(self.b[k], self.h[k])

    def step(self, steps):
        self.k_anneal(self.nch, *self.args(), np.int32(steps), np.float32(2.0), np.float32(0.05), *self.w)

    def exchange(self, parity):
        """One round of replica-exchange proposals between neighbouring rungs of every ladder."""
        E, T = self.get("Es", "Tfix")
        R = self.rungs
        Tl = T.reshape(-1, R)
        order = np.argsort(Tl, axis=1)                                 # chains of each ladder, coldest first
        base = (np.arange(Tl.shape[0]) * R)[:, None]
        a, b = (base + order[:, parity:R - 1:2]).ravel(), (base + order[:, parity + 1:R:2]).ravel()
        Ea, Eb = E[a].astype(np.float64), E[b].astype(np.float64)
        x = np.clip((1 / T[a] - 1 / T[b]) * (Ea - Eb), -50, 50)
        acc = np.random.random(len(a)) < np.exp(x)
        T[a[acc]], T[b[acc]] = T[b[acc]], T[a[acc]].copy()
        self.swaps[0] += int(acc.sum())
        self.swaps[1] += len(a)
        self.put("Tfix")

    def evaluate(self):
        E, S = np.zeros(self.nch, np.int32), np.zeros(NW * self.nch, np.uint32)
        bE, bS = self.g.buffer(E), self.g.buffer(S)
        self.k_eval(self.nch, *self.args(), bE, bS, *self.w)
        return self.g.read(bE, E), self.g.read(bS, S)

    def cpu_col(self, c, best=True):
        x = self.insts[self.h["cinst"][c]]
        return x, from_bits((self.h["bcls"] if best else self.h["cls"])[c], len(x["adj"]))

    def save(self, path):
        self.get(*self.names)
        np.savez(path + ".tmp.npz", **self.h)
        os.replace(path + ".tmp.npz", path)

    def load(self, path):
        with np.load(path) as d:
            for k in d.files:
                self.h[k][...] = d[k]
        self.put(*self.names)


def proper(adj, col, e):
    return all(col[h] >= 0 and col[h] != col[g] for h in range(len(adj)) if h != e for g in adj[h] if g != e)


def classify(adj, col, e):
    """(#trivial, #non-trivial) separable pairs at e; trivial = the a-members or the b-members of N(e) see no
    edge of the other colour."""
    nt = nn = 0
    for a in range(K):
        for b in range(a + 1, K):
            if separable(adj, col, e, a, b) is None:
                continue
            ta = all(col[g] != b for f in adj[e] if col[f] == a for g in adj[f])
            tb = all(col[g] != a for f in adj[e] if col[f] == b for g in adj[f])
            if ta or tb:
                nt += 1
            else:
                nn += 1
    return nt, nn


def check_stuck(x, col):
    adj, e = x["adj"], x["e"]
    if not (proper(adj, col, e) and energy(adj, col, e) == 0):
        return {"verified": False}
    d2 = depth_two(adj, list(col), e)
    dd = None if d2 else deep_search_capped(adj, list(col), e, 3, cap=200_000)
    return {"verified": True, "depth2": "repaired" if d2 else "fails",
            "deep": None if d2 else (dd if isinstance(dd, str) else f"repaired at depth {dd}" if dd
                                     else "none up to depth 3")}


def good_singles(adj, col, e):
    """CPU version of the kernel's good_singles (KIL2-single): recolourings f -> q of one edge f of N(e) to a colour q
    free at f, after which some pair containing col[f] or q is separable at e."""
    g = 0
    for f in adj[e]:
        p = col[f]
        used = {col[h] for h in adj[f]}
        for q in range(K):
            if q == p or q in used:
                continue
            col[f] = q
            g += any(separable(adj, col, e, min(x, y), max(x, y)) is not None
                     for x in (p, q) for y in range(K) if y not in (p, q) or (x, y) == (p, q))
            col[f] = p
    return g


def good_first_moves(adj, col, e):
    """CPU version of the kernel's good_first_moves (KIL2): Kempe swaps of an (a, b)-component meeting N(e) after which
    some pair containing a or b is separable at e."""
    g = 0
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for f in adj[e]:
                if col[f] not in (a, b) or f in done:
                    continue
                comp = component(adj, col, f, a, b)
                done.update(comp)
                swap(col, comp, a, b)
                g += any(separable(adj, col, e, min(x, y), max(x, y)) is not None
                         for x in (a, b) for y in range(K) if y not in (a, b) or (x, y) == (a, b))
                swap(col, comp, a, b)
    return g


def g_term(adj, col, e, gmode):
    return good_first_moves(adj, col, e) if gmode == 2 else good_singles(adj, col, e)


def deep_search_capped(adj, col, e, depth, cap):
    """exp33b's deep_search (swap sequences at N(e), then a free colour) with at most `cap` states expanded, so a
    depth-2 failure cannot stall the hunt; returns the depth, None, or a string when the cap is hit."""
    frontier, seen, n = [list(col)], {tuple(col[f] for f in adj[e])}, 0
    for d in range(depth):
        nxt = []
        for c0 in frontier:
            present = sorted({c0[f] for f in adj[e]})
            for i, a in enumerate(present):
                for b in present[i + 1:]:
                    done = set()
                    for f in adj[e]:
                        if c0[f] not in (a, b) or f in done:
                            continue
                        n += 1
                        if n > cap:
                            return f"undecided at depth {d + 1} ({cap} states)"
                        comp = component(adj, c0, f, a, b)
                        done.update(comp)
                        c1 = list(c0)
                        swap(c1, comp, a, b)
                        if len({c1[g] for g in adj[e]}) < K:
                            return d + 1
                        key = tuple(c1[g] for g in adj[e])
                        if key not in seen:
                            seen.add(key)
                            nxt.append(c1)
        frontier = nxt
        if not frontier:
            break
    return None


def run(out, spec, per=1024, minutes=0):
    os.makedirs(out, exist_ok=True)
    Ls = [int(v) for v in os.environ.get("KIL_GPU_L", "60000,480000,4000000").split(",")]
    rungs = int(os.environ.get("KIL_GPU_PT", 0))
    Tmin, Tmax = float(os.environ.get("KIL_GPU_TMIN", 0.05)), float(os.environ.get("KIL_GPU_TMAX", 2.0))
    wT, wN = int(os.environ.get("KIL_GPU_WT", 1)), int(os.environ.get("KIL_GPU_WN", 1))
    gcap, gmode = int(os.environ.get("KIL_GPU_GCAP", 0)), int(os.environ.get("KIL_GPU_GMODE", 1))
    insts = build_instances(parse_specs(spec))
    meta = {"spec": spec, "per": per, "Ls": Ls, "instances": [x["name"] for x in insts]}
    if rungs:
        meta.update(pt=rungs, Tmin=Tmin, Tmax=Tmax)
        del meta["Ls"]
    if (wT, wN) != (1, 1):
        meta.update(wT=wT, wN=wN)
    if gcap:
        meta.update(gcap=gcap, **({"gmode": gmode} if gmode != 1 else {}))
    H = Hunt(insts, per, Ls, rungs=rungs, Tmin=Tmin, Tmax=Tmax, wT=wT, wN=wN, gcap=gcap, gmode=gmode)
    ck, mpath = os.path.join(out, "state.npz"), os.path.join(out, "meta.json")
    done_steps = 0
    if os.path.exists(ck) and os.path.exists(mpath) and json.load(open(mpath, encoding="utf-8"))["meta"] == meta:
        H.load(ck)
        done_steps = json.load(open(mpath, encoding="utf-8"))["steps"]
        print(f"resumed from {ck} ({done_steps:.3g} steps so far)", flush=True)
    elif os.environ.get("KIL_GPU_WARM"):        # warm start: tile the chains of the same edges from another hunt
        src = os.environ["KIL_GPU_WARM"]
        wm = json.load(open(os.path.join(src, "meta.json"), encoding="utf-8"))["meta"]
        with np.load(os.path.join(src, "state.npz")) as z:     # closed at once: an open file blocks the source's
            wd = {k: z[k] for k in ("cls", "Tfix")}            # checkpoint replace on Windows
        wper, wnames = wm["per"], wm["instances"]
        assert per % wper == 0 and wd["cls"].shape[1:] == H.h["cls"].shape[1:]
        for i, x in enumerate(insts):
            if x["name"] in wnames:
                j = wnames.index(x["name"])
                for k in ("cls", "Tfix"):
                    H.h[k][i * per:(i + 1) * per] = np.tile(wd[k][j * wper:(j + 1) * wper],
                                                           (per // wper,) + (1,) * (wd[k].ndim - 1))
        H.put("cls", "Tfix")
        H.k_init(H.nch, *H.args(), np.int32(0), *H.w)
        print(f"warm start from {src}", flush=True)
    mode = f"parallel tempering, {rungs} rungs {Tmin}-{Tmax}" if rungs else f"run lengths {Ls}"
    print(f"{H.g.name}: {len(insts)} edges x {per} chains = {H.nch} chains, W = {H.W}, {mode}", flush=True)
    t0 = last_log = last_ck = time.time()
    S, steps0, launches = 8, done_steps, 0
    while True:
        active = int(H.nch - np.count_nonzero(H.get("found")[0]))
        ts = time.time()
        H.step(S)
        dt = time.time() - ts
        done_steps += S * active
        S = int(min(max(S * min(max(0.15 / max(dt, 1e-4), 0.05), 2.0), 2), 1 << 16))
        launches += 1
        if rungs:
            H.exchange(launches % 2)
        found, bestE = H.get("found", "bestEs")
        if (found == 1).any():
            H.get("bcls", "cls", "rngs")
            for c in np.flatnonzero(found == 1):
                x, col = H.cpu_col(c)
                res = {"instance": x["name"], "chain": int(c), **check_stuck(x, col), "colouring": col,
                       **({"good_singles": good_singles(x["adj"], list(col), x["e"])} if gcap else {}),
                       **({"good_first_moves": good_first_moves(x["adj"], list(col), x["e"])} if gmode == 2 else {}),
                       "time": time.strftime("%Y-%m-%d %H:%M:%S")}
                with open(os.path.join(out, "found.jsonl"), "a", encoding="utf-8") as fh:
                    fh.write(json.dumps(res) + "\n")
                print(f"STUCK {x['name']} chain {c}: verified={res['verified']} depth2={res.get('depth2')} "
                      f"deep={res.get('deep')}", flush=True)
                donor = c - c % per + (c + 1) % per                     # restart from another chain of this edge
                H.h["cls"][c] = H.h["cls"][donor]
                H.h["found"][c] = 2
                H.h["rngs"][c] ^= np.uint64(0x9E3779B97F4A7C15)
            H.put("cls", "found", "rngs")
            H.k_init(H.nch, *H.args(), np.int32(1), *H.w)
        now = time.time()
        if now - last_log > 30:
            last_log = now
            per_inst = bestE.reshape(len(insts), per).min(axis=1)
            order = np.argsort(per_inst, kind="stable")
            hist = dict(zip(*(v.tolist() for v in np.unique(per_inst, return_counts=True))))
            print(f"[{(now - t0) / 60:.1f} min] {done_steps:.3g} steps ({(done_steps - steps0) / (now - t0):.3g}/s, "
                  f"{S} steps per launch, {dt * 1000:.0f} ms"
                  + (f", swap acceptance {H.swaps[0] / max(H.swaps[1], 1):.2f}" if rungs else "")
                  + f"); best per edge {hist}; lowest: "
                  + "; ".join(f"{insts[i]['name']}: {per_inst[i]}" for i in order[:3]), flush=True)
            with open(os.path.join(out, "best.json"), "w", encoding="utf-8") as fh:
                json.dump({"steps": done_steps, "best": {insts[i]["name"]: int(per_inst[i]) for i in order}}, fh,
                          indent=1)
        end = minutes and now - t0 > 60 * minutes
        if now - last_ck > 120 or end:
            last_ck = now
            H.save(ck)
            json.dump({"meta": meta, "steps": done_steps}, open(mpath, "w", encoding="utf-8"))
            bad, comp = 0, []
            for i in range(len(insts)):                                 # CPU re-check of each edge's best state
                c = i * per + int(np.argmin(H.h["bestEs"][i * per:(i + 1) * per]))
                x, col = H.cpu_col(c)
                nt, nn = classify(x["adj"], col, x["e"])
                ok = proper(x["adj"], col, x["e"]) and len({col[f] for f in x["adj"][x["e"]]}) == K
                E1 = wT * nt + wN * nn
                if gcap:
                    E1 += min(g_term(x["adj"], list(col), x["e"], gmode), gcap) if E1 == 0 else gcap
                bad += not (ok and E1 == H.h["bestEs"][c])
                comp.append(f"{nt}+{nn}")
            print(f"checkpoint saved; CPU re-check of {len(insts)} best states: {bad} mismatches; "
                  f"best states as trivial+non-trivial: {' '.join(comp)}", flush=True)
            if end:
                print(f"stopped after {minutes} minutes", flush=True)
                return


def selftest():
    insts = build_instances(parse_specs("r:24:3:2:2,r:24:5:2:2,r:40:5:2:2,r:60:6:1:2,r:200:6:1:1"))
    H = Hunt(insts, 64, [3000, 20000])
    rng = random.Random(3)
    for rnd_ in range(4):
        H.step(200 * (rnd_ + 1))
        H.get(*H.names)
        E_new, S_new = H.evaluate()
        Es, seps = H.h["Es"], H.h["seps"].reshape(-1, NW)
        S_new = S_new.reshape(-1, NW)
        live = H.h["found"] == 0
        bad_E = np.flatnonzero(live & (E_new != Es))
        bad_S = [c for c in range(H.nch) if live[c] and Es[c] < 190 and H.h["dirtys"][c] == 0
                 and (S_new[c] != seps[c]).any()]
        cpu_bad = 0
        for c in rng.sample(range(H.nch), 100):
            for best, ref in ((False, Es[c]), (True, H.h["bestEs"][c])):
                x, col = H.cpu_col(c, best)
                cpu_bad += not (proper(x["adj"], col, x["e"]) and energy(x["adj"], col, x["e"]) == ref)
        print(f"round {rnd_}: incremental vs scratch E mismatches {len(bad_E)}, pair-bit mismatches {len(bad_S)}; "
              f"CPU re-check of 100 current + 100 best states: {cpu_bad} mismatches; "
              f"energies now {np.percentile(Es, [0, 50, 100]).tolist()}", flush=True)
    H2 = Hunt(insts, 32, [3000], gpu=H.g, wT=7, wN=3)
    H2.step(1500)
    H2.get(*H2.names)
    E2, _ = H2.evaluate()
    bad_w = cpu_w = 0
    for c in range(H2.nch):
        bad_w += E2[c] != H2.h["Es"][c] and H2.h["found"][c] == 0
        x, col = H2.cpu_col(c, best=False)
        nt, nn = classify(x["adj"], col, x["e"])
        miss = K - len({col[f] for f in x["adj"][x["e"]]})
        cpu_w += H2.h["Es"][c] != ((10 * miss + 190) * 7 if miss else 7 * nt + 3 * nn)
    print(f"weighted energy (wT=7, wN=3), {H2.nch} chains: incremental vs scratch mismatches {bad_w}, "
          f"vs CPU classification {cpu_w}", flush=True)


def bench(spec):
    x = build_instances(parse_specs(spec))[0]
    rng = random.Random(5)
    col = colour_all_but(x["adj"], x["e"], rng)
    t = time.time()
    cpu_anneal(x["adj"], col, x["e"], 5000, rng)
    cpu = 5000 / (time.time() - t)
    g = GPU()
    print(f"{x['name']}: CPU exp33b {cpu:.0f} steps/s (one Python process)")
    for nch in [8192, 32768, 65536]:
        H = Hunt([x], nch, [480000], gpu=g)
        H.step(32)
        t, steps = time.time(), 0
        while time.time() - t < 8:
            H.step(128)
            steps += 128 * nch
        r = steps / (time.time() - t)
        print(f"  GPU {nch} chains: {r:.3g} steps/s ({r / nch:.0f} per chain), {r / cpu:.0f}x one CPU process",
              flush=True)
        del H


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "run":
        run(sys.argv[2], sys.argv[3], *(int(v) for v in sys.argv[4:6]))
    elif mode == "selftest":
        selftest()
    elif mode == "bench":
        bench(sys.argv[2])
