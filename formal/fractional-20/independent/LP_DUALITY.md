# The remaining LP hypothesis

The formal development proves weak duality, exact-cover normalization, and the
complementary-slackness consequence used in Lemma A. It does not prove strong
duality or primal/dual attainment for the finite covering LP.

`FractionalLPWitness G U` contains precisely:

1. a finite nonnegative stable-set colouring covering U;
2. weights w(v)>=0 on U with sum over every stable subset of U at most 1;
3. equality of primal total weight and sum of dual weights on U.

`FractionalDuality G` says such a witness exists for each U. The proved theorem
`FractionalLPWitness.is_optimal` shows its primal objective is an attained
fractional chromatic minimum. No degree bound, clique bound, Reed inequality,
or statement about L2 is hidden in this hypothesis.

## Mathlib investigation and the uncompleted reduction

The available version has geometric separation results, including
`ProperCone.hyperplane_separation_point` in
`Mathlib/Analysis/Convex/Cone/Dual.lean`, and compact/closed finite convex hulls
in `Mathlib/Analysis/Convex/Topology.lean`. The introductory TODOs in
`Analysis/Convex/Cone/Basic.lean` explicitly still list cone/linear-programming
strong duality as future work. No directly applicable finite-LP or minimax
duality theorem was found in the available sources. The tactic simplex oracle
is not an LP strong-duality theorem for arbitrary real finite matrices.

A viable route would use the finite matrix A whose columns are indicators of
stable subsets of U. Consider the epigraph cone

    C = {(A x - s, 1^T x + t) : x,s,t >= 0}.

Membership of (1,r) is equivalent to covering U with cost at most r. Separate
(1,r) from C for r below the optimum. A separator has coefficients (-w,alpha)
with w>=0, alpha>=0 and A^T w <= alpha. Singleton columns ensure alpha>0 for
a separator of (1,r), permitting normalization alpha=1. Compactness of the
dual feasible box [0,1]^U then gives a dual maximizer at the primal optimum.
Primal attainment can be established by restricting to a nonempty bounded
sublevel set of the finite nonnegative coefficient vector x.

To apply Mathlib's cone separation theorem, the exact image cone C must first
be proved closed and packaged as a `ProperCone`; taking its closure without
proving equality is insufficient. The coordinate inequalities, finite matrix
representation, closed-image/finite-generation argument and attainment-to-
`Colouring` conversions were not completed in Lean. The geometric theorem
alone does not discharge the required hypothesis. This is a substantive
remaining formalization, not a new axiom or a claim that duality was proved.

The graph-specific work that follows duality is fully checked: normalization,
objective double counting, tightness of positive primal sets, the singleton-
neighbour replacement argument, the clique argument for replacement classes,
and the final weighted local inequality.
