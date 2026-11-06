# Proposition D: structural proof attempt and finite reduction

This is **not a proof of Proposition D**. The contradiction for sixteen locally
low selected edges remains open in this pass. What is proved here, both on
paper and in Lean, is a stronger support reduction: a conflict clique with at
least sixteen edges has at most **fourteen endpoints**. The proof uses no SAT
and does not even need the local rim inequalities. See
`third_pass/RootCounting.lean`, theorem `endpoint_bound_14`, and the complete
reduction to `Obstruction14` in `third_pass/FiniteReduction14.lean`.

Throughout, Q is a set of distinct actual edges, pairwise conflicting in H,
and Δ(H) ≤ 4. Conflict witnesses are edges of H, not necessarily edges of Q.
Write f(v) for the number of selected edges at v.

## A root with three selected neighbours

If f(v) ≤ 2 everywhere, fix uv in Q. Every other selected edge touches
R = (N(u) ∪ N(v)) \ {u,v}. This has at most six vertices, so
|Q| − 1 ≤ Σ_R f ≤ 12. Consequently |Q| ≥ 14 supplies a vertex r with
at least three selected neighbours.

Put A = N(r), S = {a ∈ A : ra ∈ Q}, s = |S| ≥ 3, and
U = V(Q) \ (A ∪ {r}). For x in U, put T(x) = N(x) ∩ A and t(x) = |T(x)|.
There are at most twelve incidences from A to U: each a ∈ A already uses one
of its four neighbours at r. Thus Σ_U t ≤ 12.

An edge xy of Q with both endpoints in U must satisfy
S ⊆ T(x) ∪ T(y). This follows by conflicting xy with each selected ra.
Neither x nor y equals or is adjacent to r, so one must be adjacent to a.

Let Z be the vertices of U with t = 0, and let P₃ be those with t ≥ 3.
Every x ∈ Z is incident with a selected edge xy; its partner y lies in U
and has S ⊆ T(y), hence lies in P₃. Such y has at least three neighbours
in A and at most one outside A. Distinct x therefore have distinct partners.
In particular |Z| ≤ |P₃|. Counting types gives

    |U| + 2|P₃| ≤ Σ_U t + |Z|,

so |U| ≤ 12 and |V(Q)| ≤ 1 + 4 + 12 = 17.

This proves, without any rim hypothesis:

> Every conflict clique with at least fourteen edges in a graph of maximum
> degree four has at most seventeen endpoints.

## Further root counting: reducing seventeen to fourteen

The following inequalities close the support reduction.
Let O be the selected edges inside U, o = |O|, and let
E = Σ_U max(t(x) − 1, 0). Then Σ_U t = |U| + E − |Z|.
Every edge of O meets M = {x ∈ U : t(x) ≥ 2}. Its selected incidence at x
is at most 4 − t(x). For t = 2,3,4 these bounds are 2,1,0. Hence

    o + 3|P₃| ≤ 2E,
    o + |Z| ≤ 2(E − |Z|).

When A is independent, partition Q into its s root edges, the K edges from
A to U, and O. Let B be the U endpoints of K and k = |K|. Then

    |Q| = s + k + o,       k ≤ |B| + E.

If some ax ∈ K has T(x) = {a}, every selected tip y whose type omits a
must be adjacent to x: the other possible conflict witnesses for ax and by
are absent. Thus

    B ⊆ (N(a) \ {r}) ∪ (N(x) \ {a}),       |B| ≤ 6.

If there is no such selected singleton, k ≤ 2E. These restrictions are
enough to exclude a support of fifteen or more vertices, as follows.

Suppose |Q| ≥ 16 and |V(Q)| ≥ 15. Choose r as above. Then |U| ≥ 10.
Write z = |Z|, p = |P₃| and D = E − z. We have

    z ≤ p,       2p ≤ E,       |U| + D = Σ_U t ≤ 12.

In particular 0 ≤ D ≤ 2 and z ≤ D.

First suppose A contains an edge ab. The edge ab uses two of the twelve
available incidences from A, so Σ_U t ≤ 10. As |U| ≥ 10, this forces D = 0.
The inequalities z ≤ p and 2p ≤ E = z then force z = p = E = 0. All vertices
of U have type size one. No selected edge can lie inside U, since its two
types could not cover the at least three labels in S. Thus every selected
edge meets A. But the number of *all* H-edges meeting A is

    Σ_{a∈A} deg(a) − e_H(A) ≤ 16 − 1 = 15,

a contradiction. Hence A is independent.

If there is no selected singleton, k ≤ 2E and o + 3p ≤ 2E give

    |Q| = s + k + o ≤ 4 + 4E − 3p
                       ≤ 4 + 4D + z ≤ 4 + 5D ≤ 14,

again impossible.

Otherwise |B| ≤ 6, so k ≤ 6 + E and

    16 ≤ |Q| = s + k + o ≤ s + 6 + 3E − 3p
                           ≤ s + 6 + 3D ≤ 16.

Equality is forced throughout: s = 4, D = 2 and p = z. For s = 4 there are
no zero-type vertices: a selected edge at such a vertex would have its other
endpoint adjacent to all four vertices of A, leaving no degree for the edge
itself. Therefore z = p = 0 and E = 2.

Every type now has size one or two, with exactly two double-type vertices.
Every edge of O must have both endpoints at these two vertices, since its
types must cover all four labels. Consequently o ≤ 1. On the other hand
k ≤ 6 + E = 8, giving |Q| ≤ 4 + 8 + 1 = 13. This final contradiction proves

> If Δ(H) ≤ 4 and Q is a conflict clique with |Q| ≥ 16, then |V(Q)| ≤ 14.

Lean uses the sufficient weaker bound o ≤ 2 in the final two-vertex case.
The theorem is otherwise the same counting proof. In particular, the
formal proof does not replace the local condition by any unproved hypothesis.

## The step that still does not close

Restrict a counterexample to Proposition D to the endpoints of sixteen of
its selected edges. The previous pass already proves that conflicts survive,
degrees and local quantities do not increase, and isolated padding preserves
the local quantities. The new support bound permits padding to `Fin 14`.

It remains to exclude a simple graph H on these fourteen slots and sixteen
selected pairwise conflicting edges Q satisfying Δ(H) ≤ 4 and
4t_H(e) + e′_H(e) ≤ 4 for every e ∈ Q. Non-isolated vertices must be endpoints
of Q. The new support theorem does **not** exclude these configurations.
There are 91 possible unordered vertex pairs; even counting only exactly
sixteen selected edges and at most twenty-eight total edges leaves a crude
labelled upper bound of 8,333,698,191,356,090,495,978,959,459,536 candidates.
This is an upper bound before the individual degree, conflict and rim tests,
not a measured number of surviving configurations. A direct `decide` over
that space is not a practical completion.

## Why the cited classification does not finish the argument

The 19-edge classification in `eighteen.md` uses SAT in its Section 5,
including the regular ten-vertex subcase in Lemma 4.1. It is not a
SAT-free theorem that can simply be substituted here. Its threshold is also
nineteen, whereas the obstruction here has sixteen selected edges.

The original full-edge-set 2K₂-free setting cannot be assumed for H: deleting
H-edges outside Q can destroy conflict witnesses. Conversely, arbitrary edges
of H outside Q need not form a conflict clique with Q.

Finally, the local inequality 4t + e′ ≤ 4 is a necessary condition obtained
from high full conflict degree, not a pointwise equivalent reformulation.
All reductions use the correct sufficient direction for proving D.
