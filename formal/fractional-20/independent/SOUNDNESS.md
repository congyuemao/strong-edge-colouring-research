# Independent encoding and checker

This implementation was written without reading `exp49_frac_core.py`.

`encode.cpp n m b prefix` represents an undirected simple graph by one Boolean
`E_ij` for each unordered pair and a separate Boolean `Q_ij` indicating clique
membership. It requires exactly m selected edges, Q implies E, degree at most
4 at each vertex, and conflict for every pair of selected disjoint edges.
For disjoint ab and cd, the conflict clause is exactly
`not Q_ab or not Q_cd or E_ac or E_ad or E_bc or E_bd`.
Pairs with a shared endpoint already conflict.

For each potential selected edge ab and vertex v other than a,b, an auxiliary
variable represents `E_av or E_bv`, and another represents `E_av and E_bv`.
For each pair cd disjoint from ab, another auxiliary represents
`E_cd and R_ab(c) and R_ab(d)`. Four copies of every common-neighbour literal
and one copy of every internal-edge literal are counted. Conditional on Q_ab,
their sum is at most b. Repeated literals in the counter intentionally give
weight four; they are not deduplicated. All Boolean gates have clauses in
both directions. The sequential counter represents threshold j in a prefix
by `(previous threshold j) OR (x AND previous threshold j-1)`, including its
boundary cases. Thus cardinality bounds have their usual exact meaning.

Every non-isolated vertex must be incident with a selected edge. This is
exactly V(Q)=V(H) after discarding padding isolates. Such isolates leave every
property unchanged, so a single n=23 instance covers every order <=23.

## Reduction and symmetry

Choose 16 edges of any putative counterexample and restrict G to their endpoint
set. A conflict witness edge has both endpoints in this set, so conflicts
survive. The maximum degree and local quantities cannot increase. Fix one
selected edge ab. Its closed endpoint neighbourhood W has at most 8 vertices.
Every other selected edge touches W, so contributes at most one vertex outside
W. All vertices are endpoints of selected edges, hence there are at most
8+15=23 vertices. Padding with isolates is legitimate.

Relabel the fixed selected edge as 01, orienting it to have deg(0)<=deg(1).
Enumerate all possible endpoint degrees da,db in 1..4 and common-neighbour
counts t. A selector fixes the endpoint adjacency rows by listing first the
t common neighbours, then the da-1-t neighbours of 0 only, then the db-1-t
neighbours of 1 only. The remaining vertices lie outside W. This is only a
relabelling. Cases with 4t>b are impossible. Cases with
`4*(da+db-2-t)<m-1` are impossible because the other m-1 selected edges each
touch R, which has da+db-2-t vertices and maximum degree four.

For each case, the vertices outside W are sorted in descending lexicographic
order of their adjacency vectors to W. Permuting only these vertices always
achieves this order without changing the fixed endpoint rows. Ties are left
unrestricted. No further symmetry constraints are used. At least one selector
is true; mutual exclusion is unnecessary, since any true selector gives a
legitimate case. There are six cases for m=16,b=4.

Consequently every counterexample to the stated stronger finite proposition
gives a satisfying assignment, and any satisfying assignment gives a graph
with the required properties after deleting isolates. The encoding itself is
not mechanically proved correct in Lean.

## Independent certificate checking

`check_lrat.cpp` is newly written, uses no SAT library and imports no solver
code. It reads the original DIMACS clauses, then checks LRAT additions by
ordered unit propagation of the listed antecedents under the negation of the
new clause. A RUP addition is accepted only on conflict (or if the new clause
is a tautology). This checker deliberately supports only the RUP fragment of
LRAT and rejects all RAT steps. Deletions remove clauses. Acceptance
requires an original or derived empty clause. It is a conventional checker,
not itself a formally verified program. Its correctness and parser remain
part of the computational trust base.

`check_model.cpp` separately reconstructs the graph from a SAT model, enumerates
degrees, conflicts, common neighbours and induced R edges, and checks every
original CNF clause. It also checks the exact degree identity of Lemma C on
the selected edges in each positive control.
