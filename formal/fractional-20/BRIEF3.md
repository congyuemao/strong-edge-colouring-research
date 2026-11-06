# Third pass: Proposition D (Proposition 11.33) without SAT, if possible

Read `REPORT.md`, `REPORT2.md`, `second_pass\PropositionDReduction.lean`, and section 11.21 of the document in `E:\lean\se20-insertion\reference\NEW_DIRECTIONS_zh.md`. `theorem_F_of_D` has `PropositionD` as its only hypothesis, and `PropositionD` is only known from SAT (two encodings, LRAT certificate 478 MB). This is the single unformalized step of the fractional theorem. Same rules: no `sorry`, no new axioms, no `native_decide`, no change to existing statements, flaws first in the report. Never install anything on drive C; never fetch anything.

Statement: if the maximum degree of G is at most 4 and Q is a clique of size at least 16 in L^2(G), then some edge of Q has L^2-degree at most 19. The reduced form: Q has 16 edges, pairwise conflicting in H = G[V(Q)], and every y in Q has 4 t_H(y) + e'_H(y) <= 4, where t is the number of common neighbours of its endpoints and e' the number of edges inside its rim; 16 is tight (15 is satisfiable).

Try, in order:
1. A human proof by structure. The hypothesis says every edge of Q has at most one common neighbour and few edges in its rim, so H is locally sparse around each clique edge, while 16 pairwise conflicting edges force many short connections. Count paths of length at most 3 between endpoints, or use the Chung-Gyarfas-Tuza-Trotter clique analysis and the classification results in `E:\lean\sep19\route-c\manuscript\eighteen.md`. Case-split on the number of vertices of degree 4 in H, on a vertex cover of Q, or on the matching number of Q (an edge set of size 16 in maximum degree 4 with small matching number is small), whichever closes. Write the proof out in `PROPOSITION_D_PROOF.md` and then in Lean.
2. If a full human proof does not close, reduce the finite problem as far as a proof allows: to as small a kernel-checkable statement as possible, with case counts small enough for `decide` or for structured proof. Report the size of what remains.
3. If 1 and 2 stall, give an honest assessment of what the link from `Fin 23` to the CNF and a kernel-checkable certificate would cost.

Write `REPORT3.md`: flaws first, exact statements, what is not done.
