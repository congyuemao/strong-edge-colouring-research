# Brief: certify the fractional Erdős–Nešetřil bound at maximum degree 4

You are verifying a new result of a strong-edge-colouring research project. Be adversarial: the most valuable
outcome is finding an error. Work only in this directory, `E:\lean\se20-fractional`. Finish by writing `REPORT.md`
here (format at the end). Do not push anything anywhere, do not touch any other repository, and do not edit anything outside
this directory. Do not install anything on drive C.

## The claim

For a finite simple graph G, let L²(G) be the graph on E(G) in which two distinct edges are adjacent ("conflict") iff
they share an endpoint or some edge of G joins an endpoint of one to an endpoint of the other. χ_f is the fractional
chromatic number: the least total weight of a nonnegative weighting x of stable sets with Σ_{S∋v} x_S ≥ 1 for every
vertex v.

**Theorem F.** If Δ(G) ≤ 4 then χ_f(L²(G)) ≤ 20.

The proof has four parts.

**Lemma A (local fractional Reed; McDiarmid, known).** For every finite graph H,
χ_f(H) ≤ max_v ½(d(v) + 1 + ω(v)), where ω(v) is the largest clique containing v.

Proof to formalize. Take an induced subgraph with the same χ_f = k and fewest vertices; rename it H. Take an optimal
primal x and an optimal dual w (w ≥ 0, w(S) ≤ 1 for every stable S, w(V) = k). By minimality w > 0 everywhere, so by
complementary slackness every vertex is covered exactly once and x_S > 0 implies w(S) = 1. Let W = max w and
M = {v : w(v) = W}. Fix S with x_S > 0 and z ∈ M \ S.
- S ∩ N(z) ≠ ∅, otherwise S + z has weight > 1.
- If S ∩ N(z) = {u}, then S − u + z is stable, so w(u) ≥ W and u ∈ M.
- For u ∈ S ∩ M, A_S(u) := {z ∈ M \ S : S ∩ N(z) = {u}} is a clique: non-adjacent a, b ∈ A_S(u) would make
  S − u + a + b stable of weight 1 + W > 1. So |A_S(u)| ≤ ω(u) − 1.

Hence Σ_{z ∈ M\S} (2 − |S ∩ N(z)|) ≤ Σ_{u ∈ S∩M} (ω(u) − 1). Multiply by x_S and sum over S. Since Σ_{S∌z} x_S = k − 1
and Σ_S x_S |S ∩ N(z)| = d(z), this gives Σ_{z∈M} (2(k−1) − d(z)) ≤ Σ_{u∈M} (ω(u) − 1), so some z ∈ M has
k ≤ ½(d(z) + 1 + ω(z)).

**Lemma B (peeling).** Let D be an integer, H a vertex-critical graph (χ_f(H − v) < χ_f(H) for all v) with
χ_f(H) > D. Then every vertex has degree ≥ D in H.

Proof. If d(v) ≤ D − 1, put k' = max(χ_f(H − v), D) < χ_f(H). In a fractional colouring of H − v of total weight k', the sets
meeting N(v) have total weight ≤ d(v), so sets of total weight ≥ 1 can take v. That colours H with total k', a contradiction.

**Lemma C (degree formula).** Let Δ(G) ≤ 4, y = ab ∈ E(G), R = (N(a) ∪ N(b)) \ {a, b}, t = |N(a) ∩ N(b)|, and e' the
number of edges of G inside R. Then N_{L²}(y) is exactly the set of edges ≠ y with an endpoint in R, so
d_{L²}(y) = Σ_{w∈R} deg(w) − e' ≤ 4(6 − t) − e' = 24 − 4t − e'.

**Proposition D (finite check; currently only by SAT).** If Δ(G) ≤ 4 and Q is a clique of L²(G) with |Q| ≥ 16, then
some y ∈ Q has d_{L²}(y) ≤ 19. Equivalently, by Lemma C it is enough that some y ∈ Q has 4t(y) + e'(y) ≥ 5.

Reduction used. Put H = G[V(Q)]. Conflicts between members of Q are witnessed inside H, and t, e' can only grow from H to G.
So it suffices to refute: a graph H with Δ ≤ 4 and Q ⊆ E(H), |Q| = 16, V(Q) = V(H), pairwise conflicting in H, and
4t_H(y) + e'_H(y) ≤ 4 for every y ∈ Q. Fix z = uv ∈ Q. Every other member touches W = N[u] ∪ N[v], so
|V(H)| ≤ |W| + 15 ≤ 23.

**Proof of Theorem F from A–D.** Suppose k = χ_f(L²(G)) > 20. Take a vertex-critical induced subgraph H of L²(G) with χ_f(H) = k.
By B, every vertex of H has degree ≥ 20 in H, hence in L²(G). So by D, H has no clique with 16 vertices. By A, using
d_H ≤ 24 (Lemma C), k ≤ ½(24 + 1 + 15) = 20, a contradiction.

## Task 1: independent check of Proposition D (do this first)

Do **not** read `C:\Users\21161\Documents\ChatGPT\se20-ideas\exp49_frac_core.py` until you have your own verdict.
- Write your own encoding from the statement above, with your own symmetry handling and a written soundness argument for it. Or better, write an exhaustive search that uses no SAT solver at all, if that is feasible; a pure Python or C search would be the strongest check. (Clang ships with the Lean toolchain under `E:\lean\elan\toolchains\...\bin`.)
- For SAT: Python 3 with `python-sat` is available at `C:\Users\21161\Documents\ChatGPT\se20-ideas\.venv\Scripts\python.exe`.
- Include positive controls: 15 members with the same bound must be satisfiable, and with the bound relaxed to 4t + e' ≤ 5 size 20 must be satisfiable (C5[2]).
- Get an actual proof certificate (DRAT or LRAT) of the UNSAT result and check it with a checker you did not get from the solver. There is no network, so write a small checker if needed, or use the verified LRAT checker in Lean's standard library (`Std.Tactic.BVDecide.LRAT`).
- After your verdict, compare with `exp49_frac_core.py` and audit that encoding for errors: over-constraining, wrong symmetry breaking, a wrong bound on |V(H)|.
- Put everything in `independent/`.

## Task 2: Lean 4 formalization

Project: this directory; toolchain and Mathlib are already set up, and `lake build` works. Environment for every command:
`ELAN_HOME=E:\lean\elan`, `XDG_CACHE_HOME=E:\lean\cache`, `TEMP=TMP=E:\lean\tmp`, and `E:\lean\elan\bin` on PATH.

Formalize under `Se20Fractional/`, in this order, each in its own file:
1. Definitions: `L2 (G : SimpleGraph V) : SimpleGraph G.edgeSet` (or a similar faithful form) and fractional colourability of a finite graph with total weight at most a real number.
2. Lemma C.
3. Lemma B.
4. Lemma A. This needs LP strong duality and complementary slackness for a finite LP. Try hard to prove what you need from Mathlib (for example via Farkas-type results or hyperplane separation on finite-dimensional spaces). If that is genuinely out of reach, isolate exactly the duality statement as a named `structure` or hypothesis, never as an `axiom`, and say so plainly in the report.
5. Theorem F, with Proposition D as an explicit hypothesis `hD`, stated in a way that is not vacuous.
6. Stretch: discharge `hD`, for example by reducing to a finite statement and `bv_decide` / `bv_check`, or a verified checker. Only attempt this after 1–5.

Rules: no `sorry`, no `admit`, no new `axiom`, no `native_decide`. Finish with `#print axioms` on each main theorem and paste the output in the report. Commit to the local git repository here as you go, so that work survives an interruption. Check that statements say what the mathematics says; a definition that makes the theorem trivial counts as a failure.

## Resource limits

The machine is shared with other long jobs. Use at most 6 processes at a time and do not run more than one Mathlib-importing Lean process at once if you can avoid it; commit memory is limited (34 GB in total and other jobs hold about 18 GB). Prefer small imports over `import Mathlib`.

## Report (`REPORT.md`)

- Verdict on each of Lemmas A, B, C, Proposition D and Theorem F: verified how, or what is wrong. Lead with any error found, including errors in the proofs above, with a concrete counterexample if possible.
- For Proposition D: your method, its run time, the certificate, what checked it, the audit of `exp49_frac_core.py`.
- For Lean: which statements are fully proved, the exact `#print axioms` output, anything left as a hypothesis, and why.
- What you did not do. Do not overstate; say "not verified" when that is the truth.
