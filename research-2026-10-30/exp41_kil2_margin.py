"""exp41: how robust is the depth-2 repair (KIL2) on the depth-1 stuck states found by exp38?

For a stuck state (G, e, col) a first move is a Kempe swap of one (a, b)-component that meets N(e).  Since the state
is stuck, every such swap leaves e blocked; it is good if afterwards some colour pair is separable at e.  Only pairs
containing a or b can change, so 37 pairs are rechecked per first move.  The KIL2 margin of the state is the number
of good first moves (and of distinct good (a, b)), out of all first moves; opened_* count the pairs that a
first move makes separable; single counts the first moves that recolour one edge of N(e).

Each output line carries key = the first 12 hex digits of sha1(instance + colouring), the dedup key.

Usage: exp41_kil2_margin.py <out.jsonl> <workers> <hunt outdir> [...]   (reads <hunt outdir>/found.jsonl)
"""
import hashlib
import json
import sys
from multiprocessing import Pool

from exp33_kempe import K, component, l2_adj, separable, swap
from exp38_gpu_adversary import build_instances, parse_specs

INST = {}


def load_instances(hunt):
    meta = json.load(open(f"{hunt}/meta.json", encoding="utf-8"))["meta"]
    for x in build_instances(parse_specs(meta["spec"])):
        INST.setdefault(x["name"], (x["edges"], x["e"]))


def margin(job):
    name, col = job[:2]
    edges, e = INST[name]
    adj = l2_adj(edges)
    col = list(col)
    Ne = adj[e]
    moves, good, good_ab, sizes, seconds, opened = 0, 0, set(), [], set(), []
    single, single_good = 0, 0
    for a in range(K):
        for b in range(a + 1, K):
            done = set()
            for f in Ne:
                if col[f] not in (a, b) or f in done:
                    continue
                comp = component(adj, col, f, a, b)
                done.update(comp)
                moves += 1
                swap(col, comp, a, b)
                ok = [(c, d) for c in range(K) for d in range(c + 1, K)
                      if (c in (a, b) or d in (a, b)) and separable(adj, col, e, c, d) is not None]
                swap(col, comp, a, b)
                opened.append(len(ok))
                single += len(comp) == 1
                single_good += len(comp) == 1 and bool(ok)
                if ok:
                    good += 1
                    good_ab.add((a, b))
                    sizes.append(len(comp))
                    seconds.update(ok)
    return {"instance": name, **({"key": job[2]} if len(job) > 2 else {}), "moves": moves, "good": good, "good_pairs": len(good_ab),
            "min_good_size": min(sizes) if sizes else None, "second_pairs": len(seconds),
            "opened_min": min(opened), "opened_mean": round(sum(opened) / len(opened), 2),
            "single": single, "single_good": single_good}


def main():
    out, workers = sys.argv[1], int(sys.argv[2])
    jobs, seen = [], set()
    for hunt in sys.argv[3:]:
        load_instances(hunt)
        for line in open(f"{hunt}/found.jsonl", encoding="utf-8"):
            r = json.loads(line)
            key = hashlib.sha1((r["instance"] + json.dumps(r["colouring"])).encode()).hexdigest()
            if key in seen:
                continue
            seen.add(key)
            jobs.append((r["instance"], r["colouring"], key[:12]))
    print(f"{len(jobs)} distinct stuck states", flush=True)
    with Pool(workers, initializer=init, initargs=(sys.argv[3:],)) as pool, open(out, "w", encoding="utf-8") as fh:
        for i, res in enumerate(pool.imap_unordered(margin, jobs, chunksize=4)):
            fh.write(json.dumps(res) + "\n")
            if i % 100 == 0:
                fh.flush()
                print(i, res, flush=True)


def init(args):
    for hunt in args:
        load_instances(hunt)


if __name__ == "__main__":
    main()
