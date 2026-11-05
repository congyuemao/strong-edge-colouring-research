# Second pass on Part I: finish Theorem B, then the rest

Read `REPORT.md`, `Se20Part/OpenStatements.lean` and `reference\MANUSCRIPT_zh.md` section 3 (`reference\exp31_lll_girth.py` and `reference\exp31.log` are now supplied for the numerics). Same rules as `BRIEF.md`: no `sorry`, no new axioms, no `native_decide`, no change to statements already proved, no weakening without saying so, cited theorems only as named hypotheses, adversarial report with flaws first.

The first pass stopped with major targets open. Do not stop at a partial result while a target can still be attacked: there is time. Work on these in order, and when one blocks, write down the exact obstruction and continue with the next.

1. Theorem B, step 1: for finite `G` with maximum degree at most 4, `E(G) = F1 ∪ F2` with each `F_j` of maximum degree at most 2. Prove the Euler orientation and the Konig step directly, or use a cleaner proof of the same statement if you find one (for instance a counting or extremal argument on 2-factors or on edge partitions minimizing monochromatic degree excess: the statement only needs the maximum-degree partition, so a Lovasz-style local-improvement proof may be much shorter than Euler tours; say which one you used).
2. Theorem B, step 2 and 3: the odd-cycle partition from step 1, Haxell, the decomposition into paths and even cycles, the alternating colouring into four matchings.
3. Lemma 3.6, then steps 4-6 using `twenty_of_dominating_seed`. **Theorem 3.5 (Theorem B) with hypotheses `Kostochka` and `Haxell`.**
4. Lemma 3.9 (a), (b) with girth at least 9, Corollary 3.10.
5. Lemma 3.11 (tree lemma) on `InfiniteFourTree`, or a finite-ball version if you explain why it is equivalent for the use made of it.
6. Proposition 3.13, including the construction and orientation of the option graph. Also the corrected form of the Haxell remark: disjoint parts obtained by tagging each candidate with its problem edge, with the degree hypothesis stated for the tagged graph.
7. Lemma 3.15; then Theorem 3.14 (Theorem B+) with hypothesis `LovaszLocalLemma` and with the transfer-matrix bound either kernel-checked from an explicit matrix built from `exp31_lll_girth.py` or left as the named hypothesis `TransferMatrix5710Bound`. If you reconstruct the matrix, prove it counts the spanning families, or state clearly that this correspondence is a hypothesis.
8. If everything above is done: prove `LovaszLocalLemma`.

Append to `REPORT.md` a section "Second pass" (flaws first; exact statements; axioms; what remains), and update `AxiomAudit.lean`.
