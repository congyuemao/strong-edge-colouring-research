# Third-pass report

## Flaws, qualifications, and the remaining gap

**Proposition D is still not proved without SAT, and is still not an
unconditional Lean theorem.** This pass proves a substantially smaller finite
reduction, from `Fin 23` to **`Fin 14`**, but does not prove the resulting
finite premise. The remaining case count is not small enough for a direct
`decide`. Thus step 1 did not close, and step 2 is only partially completed.

**The installed `bv_decide`/`bv_check` path does not satisfy the no-new-axioms
rule.** This is a concrete toolchain issue, not merely a hypothetical trust
concern. In Lean 4.35.0-rc4,
`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean`,
`LratCert.toReflectionProof` calls `nativeEqTrue`; both the solver path and
`lratChecker` use it. `Lean/Meta/Native.lean`, lines 37–87, implements this by
compiled evaluation followed by `Declaration.axiomDecl` and `addDecl`.
Therefore using the standard tactic unchanged would add an auxiliary axiom.
Neither tactic was used in this pass. The proved soundness of the LRAT
checker does not itself prove acceptance of a particular certificate.

**The cited classification does not provide a SAT-free shortcut.** The
19-edge classification in `eighteen.md` depends on Section 5's SAT searches;
even its regular ten-vertex Lemma 4.1 uses the instance `R`. It also applies
at nineteen selected edges, not sixteen. Enumeration of 4-regular graphs
alone does not cover the reduced problem, which allows vertices of degree
two and three and measures the necessary local rim condition in the induced
support graph. No claim of completeness is made from those graph lists.

No counterexample or substantive flaw in the existing Lean reductions was
found. The earlier qualification remains: `4t + e′ ≤ 4` is a necessary local
condition extracted from conflict degree at least 20, not a pointwise
equivalence. Removing unselected graph edges indiscriminately would destroy
some conflict witnesses; the new proofs keep the original graph throughout.

## What is proved

The complete paper argument is in
[PROPOSITION_D_PROOF.md](PROPOSITION_D_PROOF.md). Its new conclusion is:

> If H has maximum degree at most four and Q is a set of at least sixteen
> pairwise conflicting edges, then Q has at most fourteen endpoints.

This statement needs **no local rim hypothesis**. It is proved in Lean in
[RootCounting.lean](third_pass/RootCounting.lean), using the elementary
preliminaries in [SupportBound.lean](third_pass/SupportBound.lean).

The root argument is short to state. Selected maximum degree at most two
would give at most thirteen selected edges, so choose a vertex r with at
least three selected neighbours. Its neighbourhood A has at most four
vertices. Classify each selected endpoint outside A and r by its set of
neighbours in A. There are at most twelve such incidences. A zero-type
endpoint needs a distinct partner with at least three neighbours in A.
This first gives seventeen endpoints.

For the sharper bound, suppose there are at least fifteen endpoints, so at
least ten lie outside A and r. Count the excess of each nonzero type over
size one. Selected edges outside A must join types covering the selected
root labels. If A has an internal edge, the incidence budget drops from
twelve to ten and the selected clique has at most fifteen edges. If A is
independent, a selected singleton type bounds the number of selected tips
by six; the case without a selected singleton has an even smaller edge
budget. The only numerical equality case has four selected root edges,
two double-type vertices, and all remaining types singleton. It also
contradicts sixteen selected edges. Each of these steps is checked in Lean.

The exact main statements, in namespace `Se20Fractional.ThirdPass`, are:

```lean
theorem endpoint_bound_14
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hsize : 16 ≤ Q.card) :
    (DReduction.endpoints Q).card ≤ 14

def Obstruction14 (H : SimpleGraph (Fin 14)) (Q : Finset H.edgeSet) : Prop :=
  (∀ v, H.degree v ≤ 4) ∧ Q.card = 16 ∧ Clique (L2 H) Q ∧
    DReduction.LocallyLow H Q ∧
    ∀ v, (∃ u, H.Adj v u) → v ∈ DReduction.endpoints Q

theorem obstruction14_of_not_D
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hΔ : ∀ v, G.degree v ≤ 4) (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 14), ∃ Q : Finset H.edgeSet, Obstruction14 H Q

theorem propositionD_of_no_obstruction14
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 14), ∀ Q : Finset H.edgeSet,
      ¬ Obstruction14 H Q) : PropositionD G

theorem theorem_F_of_no_obstruction14
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 14), ∀ Q : Finset H.edgeSet,
      ¬ Obstruction14 H Q) : FractionalColourable (L2 G) 20
```

The last three declarations are in
[FiniteReduction14.lean](third_pass/FiniteReduction14.lean). They reuse the
previous pass's checked induced restriction and padding lemmas. The
intermediate seventeen-slot reduction is also retained, in
[FiniteReduction.lean](third_pass/FiniteReduction.lean).

**`hfinite` is not discharged.** No existing statement was weakened or
changed. In particular, `theorem_F_of_D` still has its original meaning and
its original explicit Proposition D hypothesis.

## Size of the finite problem

The obstruction is now supported on at most fourteen vertices (and at least
eight non-isolated vertices by the handshake bound). There are 91 unordered
pairs of fourteen labelled slots. Giving each pair one of the three states
absent / unselected edge / selected edge yields:

| Restrictions imposed in this count | Number of labelled assignments |
| --- | ---: |
| Three states on 91 pairs | 26,183,890,704,263,137,277,674,192,438,430,182,020,124,347 |
| Exactly sixteen selected edges | 9,840,009,988,453,909,143,513,505,773,708,103,385,088 |
| Also at most twenty-eight total edges | 8,333,698,191,356,090,495,978,959,459,536 |

The last number is
`choose(91,16) * sum(k=0..12, choose(75,k))`, about `8.33 × 10^30`.
These are **crude upper bounds**, not measured counts after testing every
vertex's degree, conflicts, endpoint coverage, local sparsity, or symmetry.
The count log is [case-counts.txt](third_pass/case-counts.txt).

The root proof supplies additional sound pruning: at least three selected
root neighbours, at most nine selected endpoints outside its closed
neighbourhood, the type-incidence budget, the zero/triple injection, the
outer-edge budget, and the singleton bound. The existing six numerical
root-edge cases remain valid. However, this pass does not implement and
prove complete a canonical search using all these restrictions. There is
no measured small number of residual branches and no exhaustive kernel
check. Claiming that `Fin 14` by itself makes `decide` practical would be
misleading.

For a concrete size comparison, the existing independent encoder was run
with `n=14, m=16, bound=4`. **Only encoding was run, not a SAT solver.**

| Instance | Variables | Clauses | DIMACS bytes |
| --- | ---: | ---: | ---: |
| Existing 23-slot instance | 442,553 | 1,707,026 | 37,510,408 |
| New 14-slot instance | 62,519 | 238,730 | 4,655,947 |

See [reduced14-encoding.log](third_pass/reduced14-encoding.log) and
[reduced14.cnf](third_pass/reduced14.cnf). There are six root cases in both.
This smaller CNF is **not** formally linked to `Obstruction14` and has no
new UNSAT certificate. The old certificate cannot simply be replayed against
the new file.

## Cost of finishing through CNF and a kernel certificate

The old 23-slot route remains available, or the new support proof can be
used to start from fourteen slots. Either route still needs the following
proofs and implementation work.

1. **A formally specified encoder and its model-extension theorem.** Assign
   actual and selected edge variables from H and Q; define the region,
   common-neighbour and internal-edge gates; prove every Tseitin clause and
   sequential-counter clause. Common-neighbour literals are intentionally
   counted four times. The selected-edge subtype and the unordered pair
   numbering must agree with the implementation. The required implication
   is from an obstruction to a satisfying assignment.
2. **The additional symmetry proof if the existing certificate is reused.**
   The previous pass handles a root edge and the six numerical cases, but
   the exact neighbour labels and sorted exterior adjacency vectors used
   by `encode.cpp` still need their relabelling proofs. Alternatively omit
   these constraints in a newly proved encoder and obtain a new certificate.
3. **The exact concrete CNF connection.** A theorem about an abstract
   encoder is insufficient unless the concrete clauses checked by the
   certificate are those clauses. A hash or an IO parser result is not
   such a theorem. Generating Lean constants externally is acceptable only
   when their required relations are proved in the kernel.
4. **Kernel-checked certificate acceptance or reconstructed RUP proofs.**
   The general LRAT soundness theorem is available. The concrete acceptance
   theorem is not. The standard native-evaluation tactic path described
   above is excluded by the user's rules.

A read-only scan of the existing certificate gives the following actual
workload; it is not a new validity check:

| Quantity | Count |
| --- | ---: |
| Original clauses / literal occurrences | 1,707,026 / 4,625,588 |
| RUP additions, including final empty clause | 2,418,926 |
| Added literal occurrences | 14,977,172 |
| Hint references | 49,477,946 |
| Deletion actions / deleted IDs | 632,126 / 3,943,654 |
| Maximum added-clause width | 208 |
| Maximum hints in one addition | 3,190 |
| Negative RAT hints | 0 |

The scan source is [certificate_stats.cpp](third_pass/certificate_stats.cpp)
and its output is [certificate-stats.txt](third_pass/certificate-stats.txt).
The earlier 50.63-second compiled Lean replay and 19.10-second C++ replay
are **not estimates for kernel reduction**. They were not rerun here.

The RUP-only format helps: an untrusted generator could emit kernel-checked
unit-resolution derivations, using previously proved clauses. Deletions need
not be logical proof steps. Before attempting the full trace, dependency
trimming, proof-term sharing, batching and memory measurements would be
necessary. A second option is a deliberately reducible, proved-sound
checker with chunked acceptance theorems. Neither is implemented here.
A small exploratory attempt to apply `decide` directly to the stock checker
encountered opaque/irreducible internal helpers even on a synthetic chain;
this was not a performance benchmark and does not establish impossibility.

My assessment is that this is a separate proof-engineering project, not a
small wrapper around the existing 478 MB file. The 49.5 million hint
references make a promised kernel runtime unjustified without a prototype.
The new 14-slot encoding is a better place to seek smaller certificates or
a certified SAT-free branch search, but its certificate size and runtime
have not been measured. I do not give an unsupported completion-time estimate.

## Validation and reproduction

`lake --no-cache build` succeeded for the unchanged default library.
The new modules were compiled separately and are deliberately outside the
default import graph. Reproduce with [third_pass/build.ps1](third_pass/build.ps1).
It uses only the configured local Mathlib and toolchain and redirects
temporary/cache locations to E:.

Logs: [project-build.log](third_pass/project-build.log),
[RootCounting-build.log](third_pass/RootCounting-build.log),
[FiniteReduction14-build.log](third_pass/FiniteReduction14-build.log), and
[axioms.txt](third_pass/axioms.txt).

The first scripted standalone recheck encountered a transient failure to
read an existing toolchain `.olean.private` file. An immediate standalone
retry succeeded; the subsequent sequential checks and axiom audit passed.
No toolchain files were changed or fetched.

All audited new results depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

This includes `endpoint_bound_14`, `obstruction14_of_not_D`,
`propositionD_of_no_obstruction14`, and `theorem_F_of_no_obstruction14`.
As before, explicit hypotheses do not appear in `#print axioms`; the finite
premise remains a hypothesis. The saved Lean sources contain no `sorry`,
`admit`, new axiom, `native_decide`, or native-reflection shortcut.

No SAT solver was run in this pass. Nothing was installed or fetched.
Existing source files and the previous reports were preserved. No commit,
push, or modification to another repository was attempted.

## Not done

- No complete human proof of Proposition D, including the locally sparse
  sixteen-edge case on at most fourteen vertices.
- No complete SAT-free enumeration or certified branch count.
- No graph-to-CNF theorem for either concrete encoding.
- No kernel acceptance of the old certificate or a new certificate.
- No unconditional fractional theorem; `hD`, or its reduced `hfinite`
  replacement, remains explicit.
