# Fourth pass: discharge `hfinite` on `Fin 14` in the kernel

Read `REPORT3.md` and `PROPOSITION_D_PROOF.md`. Goal: `∀ H : SimpleGraph (Fin 14), ∀ Q : Finset H.edgeSet, ¬ Obstruction14 H Q`, which with `theorem_F_of_no_obstruction14` makes the fractional theorem unconditional in Lean. Same rules: no `sorry`, no new axioms, no `native_decide`, no `bv_decide`, no change to existing statements, flaws first. Never install anything on drive C; never fetch anything. There is time: keep going while the target can still be attacked.

Data: CaDiCaL (run by the session owner) proves the 14-slot CNF `third_pass/reduced14.cnf` unsatisfiable in about 32 seconds with 316,785 conflicts, without any symmetry reasoning beyond what the encoder does. So the search space, well organized, is small. You may run solvers already on this machine if you use them only as an oracle to plan the case split, never as a proof.

Suggested route:
1. Strengthen the human reduction further: more structure from the root argument (six root-edge cases, type-incidence budget, zero/triple injection, at most nine selected endpoints outside the closed neighbourhood), and the local condition `4 t + e' <= 4`. Every reduction that removes cases is worth it; try to bring the endpoint bound below 14 for selected cases.
2. Write a verified exhaustive search in Lean: a computable function on `Nat` bitmasks (structural recursion or explicit fuel, not well-founded recursion, so that the kernel can reduce it), which enumerates the remaining canonical configurations with early pruning, and a proved theorem: if it returns `true`, no obstruction exists. Prove soundness first on a small analogue, then evaluate with `by decide` or `rfl`; the kernel has GMP-accelerated `Nat` operations, so use them. Split the computation across many separately compiled lemmas, one per root case or per first branching level, so that each stays within kernel limits, and measure the rate before committing.
3. If the kernel is too slow for the whole search, reduce with further hand proof, or report the exact number of nodes and the measured rate, so the remaining cost is known.

Write `REPORT4.md`: flaws first, exact statements, measured sizes, axiom output, what is not done.
