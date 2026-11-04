# Brief: formalize the conditional proof of the strong edge colouring bound at maximum degree 4

You are verifying a research project's reduction of an open problem. Be adversarial: the most valuable outcome is finding an error, and the same kind of error has already happened three times here (see "The recurring bug").

**Open problem (not your job to solve).** Every finite simple graph with maximum degree ≤ 4 has a strong edge colouring with 20 colours. The best published bound is 21.

**Your job.** Prove in Lean 4 that the project's unproved conjectures imply this bound, and prove the supporting lemmas. Do not try to prove the conjectures; they appear as explicit hypotheses.

## Working rules

- Work only in `E:\lean\se20-insertion`. Do not push, do not touch any other repository, do not edit anything outside this directory. Git metadata is read-only in your sandbox; I will commit.
- Nothing may be installed on drive C. Environment: `ELAN_HOME=E:\lean\elan`, `XDG_CACHE_HOME=E:\lean\cache`, `TEMP=TMP=E:\lean\tmp`, `E:\lean\elan\bin` on `PATH`. Toolchain `leanprover/lean4:v4.35.0-rc4`. Mathlib is the local path dependency already in `lakefile.toml`; do not fetch anything.
- At most 6 processes, ideally one Mathlib-importing Lean process at a time.
- No `sorry`, `admit`, new `axiom`, `native_decide`, or `Lean.ofReduceBool`. `#print axioms` on every main theorem must show only `propext`, `Classical.choice`, `Quot.sound`.
- A conjecture may only appear as an explicit hypothesis of a theorem, under the names below. State the definitions faithfully, do not strengthen a conjecture to make a proof easier, and do not weaken a conclusion.
- `E:\lean\se20-fractional\Se20Fractional\Definitions.lean` has earlier definitions, including `L2`. You may copy from it. `reference\NEW_DIRECTIONS_zh.md` is the source for all numbered statements (Chinese; section 11, especially 11.14, 11.17, 11.18, 11.20, 11.22).
- Write results to `REPORT.md`; see the end. If you stop early, leave partial files out of the default build target and say so.

## Definitions

Let G be a finite simple graph. Two distinct edges **conflict** if they share an endpoint or some edge of G joins an endpoint of one to an endpoint of the other. `L²(G)` is the conflict graph on E(G). **Conflicts are always judged in the whole graph G, whether or not the joining edge is coloured.**

A **partial colouring** with coloured set F ⊆ E(G) assigns one of 20 colours to each edge of F, with conflicting edges of F coloured differently. Equivalently it is a proper colouring of L²(G)[F].

For a coloured or uncoloured edge f and colour x, an **x-neighbour** of f is a coloured edge of colour x conflicting with f. For colours a ≠ b, an **(a, b)-component** is a connected component of the subgraph of L²(G) induced by the edges coloured a or b. The pair (a, b) is **separable at f** if no (a, b)-component contains both an a-neighbour of f and a b-neighbour of f. This holds vacuously if f has no a-neighbour.

A colour p is **single at e** if e has exactly one p-neighbour, written f_p.

## The recurring bug

A strong colouring of the graph G − e is **not** a partial colouring of G: two edges that conflict only through e may get the same colour. Conflicts are monotone under taking subgraphs, and L²(G)[E(G − v)] = L²(G − v) for a vertex v (a joining edge between two edges of G − v cannot touch v), but L²(G)[E(G) − e] ≠ L²(G − e) in general. Check this at every induction step.

## Main statements

Quantify conjectures over `SimpleGraph (Fin n)`; the final theorems must hold for any `[Fintype V]`.

**Star state.** (G, v, U, φ): G is simple, U is a nonempty set of edges at v, φ is a partial colouring with coloured set exactly E(G) − U.

**`Conj119Star` (conjecture 11.9*, the main target).** For every simple 4-regular G, every vertex v such that the complement of G[N(v)] has a perfect matching, and every star state (G, v, U, φ) in which no edge of U lies on a triangle: there is e ∈ U such that one of the following holds.
1. Some colour has no neighbour at e.
2. Some pair a ≠ b is separable at e.
3. Some colour p is single at e, and some pair a ≠ b with a, b ≠ p is separable at f_p.

**`Conj119` (conjecture 11.9).** For every G with Δ ≤ 4, every partial colouring, and every uncoloured e such that every colour has a neighbour at e and no pair is separable at e: some colour p is single at e, and some pair a ≠ b with a, b ≠ p is separable at f_p.

**`Conj1115` (conjecture 11.15).** The same hypothesis as `Conj119`; the conclusion is: there are a colour c and colours a ≠ b, both ≠ c, such that no (a, b)-component contains both an a-neighbour of a c-neighbour of e and a b-neighbour of a (possibly different) c-neighbour of e.

**`Conj1126Weak` (conjecture 11.26, weak form).** Let C(φ) be the total number of components over all 190 colour pairs. For every G with Δ ≤ 4, F ⊆ E(G), h ∈ F, and every proper 20-colouring φ of L²(G)[F − h] such that no single Kempe swap (swap a, b on one (a, b)-component) increases C: either some colour has no neighbour at h, or some pair is separable at h.

**Theorems to prove, in priority order.** Here `StrongColourable G 20` means a proper 20-colouring of `L²(G)` exists.

```text
theorem strongColourable_of_conj119Star (h : Conj119Star) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20
theorem conj119Star_of_conj119 : Conj119 → Conj119Star
theorem strongColourable_of_conj1115    (h : Conj1115)    (hΔ) : StrongColourable G 20
theorem strongColourable_of_conj1126    (h : Conj1126Weak) (hΔ) : StrongColourable G 20
```

Also state and prove the abstract reduction: if every star state as in `Conj119Star` admits some e ∈ U and a partial colouring with coloured set E(G) − U + e, then every G with Δ ≤ 4 is strongly 20-colourable (`strongColourable_of_starInsertion`).

## Proofs to formalize

The statements in the sections marked **new** were written today and have had no independent review. Attack them first.

### Basic facts

- Conflict is monotone under subgraphs. L²(G)[E(G − v)] = L²(G − v).
- A Kempe swap on one (a, b)-component preserves properness. Swapping several (a, b)-components does too.
- If (a, b) is separable at uncoloured e, swapping every (a, b)-component containing an a-neighbour of e leaves e with no a-neighbour: the old a-neighbours became b; an edge that became a was b and lies in a swapped component, so if it conflicted with e it would be a b-neighbour of e sharing a component with an a-neighbour.

### Theorem 11.7 (insertion along a single-colour chain)

Let e be uncoloured. A **chain** is e = x₀, x₁, …, x_k where, for j ≥ 1, x_j is a coloured neighbour of x_{j−1} of colour y_j, y_j occurs exactly once among the coloured neighbours of x_{j−1}, and y₁, …, y_k are pairwise different. Let c ≠ d be colours outside Y = {y₁, …, y_k} with (c, d) separable at x_k.

Then swap every (c, d)-component containing a c-neighbour of x_k; recolour x_k to c; then recolour x_{k−1} to y_k, …, x₁ to y₂; finally colour e with y₁. The result is a partial colouring with coloured set F + e.

Proof. The swaps change only colours c, d, and no x_j or e. After them x_k has no c-neighbour, as above. Process j = k, …, 1. When x_{j−1} gets y_j, its only old y_j-neighbour x_j has already changed; the deeper edges received y_{j+2}, …, y_k, c, none equal to y_j; the swaps produce no y_j.

The case k = 1 is what the main theorem needs; formalize the general k if it is not much harder.

### Theorems 11.14 and 11.18 (colour-class insertion)

Let c be a colour with neighbours g₁, …, g_m at e. Partition them into groups B₁, …, B_t and choose for each group colours a_s, b_s ≠ c such that the sets {a_s, b_s} are pairwise disjoint, and no (a_s, b_s)-component contains both an a_s-neighbour and a b_s-neighbour of (possibly different) edges of B_s. Swap, for each s, all (a_s, b_s)-components containing an a_s-neighbour of an edge of B_s; recolour all of B_s to a_s; colour e with c. The result is a partial colouring with coloured set F + e.

Theorem 11.14 is the case t = 1, needed for `Conj1115`.

### Lemma 11.17 (edges on triangles)

Let Δ(G) ≤ 4, φ any partial colouring, e = uv uncoloured, w a common neighbour of u and v. Then e can be coloured after recolouring at most one edge.

Proof. Name the other neighbours x₂, x₃ of u, y₂, y₃ of v, z₁, z₂ of w. Conflicts of e all have an endpoint in {u, v, w, x₂, x₃, y₂, y₃}, and there are at most 3 + 3 + 2 + 12 = 20. If no colour is free, these 20 edges exist, are coloured, and have distinct colours, so the seven listed vertices are distinct and nothing is counted twice. Let X, Y be the 6 edges at x₂, x₃ and at y₂, y₃ other than ux_i, vy_i, and Z the at most 6 edges at z₁, z₂ other than wz_i, none of which is a conflict of e. uw has 13 conflicts in N(e), namely all but itself and Y, and its only other conflicts are in Z; so it sees the 6 colours of Y only on Z. Likewise vw sees the 6 colours of X only on Z. These are 12 different colours and |Z| ≤ 6, so uw or vw misses a colour q. It is the only edge of its colour p on N(e). Recolour it to q and colour e with p.

### Lemma 11.36, Lemma 11.37, Propositions 11.35, 11.38 (**new**)

**Lemma 11.36.** If F ⊆ E(G), T is the set of edges of F lying on a triangle of G, and L²(G)[F − T] is 20-colourable, so is L²(G)[F]. Insert T one edge at a time with Lemma 11.17.

**Lemma 11.37.** Let G be simple 4-regular. Call v **exceptional** if the complement of G[N(v)] has no perfect matching. (1) At most one edge at an exceptional vertex lies on no triangle. (2) If every vertex is exceptional, G is strongly 20-colourable.

Proof. (1) K₄ on N(v) has 3 perfect matchings, each containing an edge of G[N(v)]. Edges from different perfect matchings of K₄ intersect, so these 3 edges form a triangle or a claw. For a triangle x₁x₂x₃, the edges vx₁, vx₂, vx₃ lie on triangles. For a claw with centre x₁, all four edges at v lie on triangles. (2) By (1) the triangle-free edges form a matching M. An edge ab ∈ M conflicts only with M-edges meeting N(a) − b or N(b) − a, at most 6 of them, so L²(G)[M] is greedily 7-colourable. Apply Lemma 11.36.

**Proposition 11.35.** If every star state (for Δ ≤ 4 graphs) admits an insertion, every Δ ≤ 4 graph is strongly 20-colourable. By induction on the number of vertices: a colouring of G − v is a star state with U = E(v). (This is the easier form; it is optional if you prove 11.38 directly.)

**Proposition 11.38.** The statement `strongColourable_of_starInsertion`.

Proof. Every simple graph with Δ ≤ 4 is a subgraph of a simple 4-regular graph: take two copies and join corresponding vertices of degree < 4, which raises the minimum degree by 1; repeat. So it suffices to treat simple 4-regular graphs, possibly disconnected, by induction on the number of vertices. If every vertex is exceptional, use Lemma 11.37. Otherwise take a non-exceptional v and split its neighbours into non-adjacent pairs x₁x₂, x₃x₄. G″ = G − v + x₁x₂ + x₃x₄ is simple 4-regular on n − 1 vertices, hence 20-colourable. G − v is a subgraph of G″, so the restriction to E(G − v) is a proper colouring of L²(G − v) = L²(G)[E(G) − E(v)], a star state with U = E(v). Insert the edges of U one by one: an edge on a triangle by Lemma 11.17, otherwise by the hypothesis. ∎

`strongColourable_of_conj119Star` then follows from cases 1, 2, 3 of `Conj119Star` with the separable-pair fact and Theorem 11.7 at k = 1.

### Proposition 11.27 (fragmentation, for `strongColourable_of_conj1126`)

C(φ) is bounded and a raising swap increases it strictly, so a hill climb on proper colourings of L²(G)[F − h] stops at a local maximum. Then h has a free colour, or a separable pair frees one. Use induction on |F| (the statement quantifies over F, so no G − h appears).

### Supporting lemmas (next priority)

- **Lemma 11.6.** If every colour has a neighbour at e and no pair is separable at e via single-edge components, then each f_p sees every colour other than p.
- **Corollary 11.8**, including the count: at least 2(20 − j) − 24 colours occur exactly once at x_j outside Y (at j = 1, at least 15, since e is uncoloured).
- **Lemma 11.11.** The hole move (colour e with p, erase f_p) is a legal reversible move, preserves colour-class sizes, and leaves f_p blocked if e was stuck.
- **Lemma 11.12.** If e is stuck, then after the hole move no pair (p, x) is separable at f_p.
- **Lemma 11.13.** If e is stuck, p, a, b are different single colours, and f_a, f_b conflict with f_p, then (a, b) is not separable at f_p.
- **Lemma 11.16.** Any partial colouring with m coloured edges has at least 7m components over the 190 pairs.
- At e with k other uncoloured conflicts, at least 16 + k colours are single when e is blocked.

### Stretch (only after the above builds; at most about 3 hours of wall-clock time, check with `Get-Date`)

- Lemma 11.24 and Corollary 11.25 (degree-3 vertices).
- Corollary 11.19 and Lemmas 11.20–11.22.

## `REPORT.md`

Lead with any flaw found in a statement or proof, however small, including anything that makes a conjecture vacuous, or false on a small explicit graph (such a counterexample would be very valuable; give it in full). Then:
- the exact Lean statements of the definitions and of each conjecture, for audit;
- which theorems are proved, with file names, and the exact `#print axioms` output for each main theorem;
- what remains a hypothesis, and what was not done.

A partial result reported honestly is fine; a hidden assumption is not.
