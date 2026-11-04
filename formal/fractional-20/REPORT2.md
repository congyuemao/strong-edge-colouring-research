No substantive flaw was found in the proposed elementary proof. The weighted statement needs `0 ≤ k` when the support is empty, as the question anticipated: with `U = ∅` and `k = -1`, the local inequalities are vacuous, but nonnegative weights cannot have total at most `-1`. The formal statement includes `0 ≤ k` explicitly. No other correction to this proof was needed.

**Part 1 is complete.** Lemma A now has an elementary Lean proof, and `theorem_F_of_D` has no LP duality hypothesis. **Part 2 is incomplete:** Proposition D remains an explicit hypothesis of the main theorem. There is no `theorem_F_unconditional`.

The new proof is in [LocalReedElementary.lean](Se20Fractional/LocalReedElementary.lean). The new theorem is in [TheoremF.lean](Se20Fractional/TheoremF.lean); the previous conditional `theorem_F` is retained unchanged. The new file is included in the default library build.

The following statements are fully proved. In the first two declarations, the context is `{V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}`, in namespace `Se20Fractional.Elementary`.

```lean
theorem maximum_stable_key (U : Finset V) (v : V) (hvU : v ∈ U) (ω : ℕ)
    (hω : ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω) :
    2 * (maximumStableSets G U).card ≤
      (∑ S ∈ maximumStableSets G U, degreeOn G S v) +
        (ω + 1) * occurrence (maximumStableSets G U) v

theorem weighted_local_reed (U : Finset V) :
    ∀ (r : V → ℝ) (k : ℝ) (ω : V → ℕ),
    (∀ v ∈ U, 0 ≤ r v) → 0 ≤ k →
    (∀ v ∈ U, ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω v) →
    (∀ v ∈ U, (∑ u ∈ neighbors G U v, r u) + ((ω v : ℝ) + 1) * r v ≤ 2*k) →
    ∃ c : DemandColouring G U r, c.total ≤ k
```

Here `maximumStableSets` contains all stable subsets of `U` of maximum cardinality, and `occurrence F v` counts those members of `F` containing `v`. `DemandColouring` assigns a nonnegative real weight to every finite vertex subset; every subset with nonzero weight is stable and contained in `U`; the total weight covering each `v ∈ U` is at least `r v`. Its `total` is the sum of all weights. These definitions do not contain the desired inequality as a field or assumption.

The public Lemma A statement, in namespace `Se20Fractional`, is:

```lean
theorem local_fractional_reed_elementary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (k : ℝ) (hk : 0 ≤ k) (ω : V → ℕ)
    (hω : ∀ v ∈ U, ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω v)
    (hlocal : ∀ v ∈ U, (degreeOn G U v : ℝ) + 1 + (ω v : ℝ) ≤ 2*k) :
    FractionalColourableOn G U k
```

The final theorem has context `{V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)`:

```lean
theorem theorem_F_of_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : PropositionD G) :
    FractionalColourable (L2 G) 20
```

`hD` retains its original, nonvacuous meaning:

```lean
def PropositionD : Prop :=
  ∀ Q : Finset G.edgeSet, Clique (L2 G) Q → 16 ≤ Q.card →
    ∃ y ∈ Q, degreeOn (L2 G) univ y ≤ 19
```

The elementary proof formalizes the swap map, recovery of its source from the target and replacement vertex, the clique bound on each fibre, and the required double count. The induction removes zero-demand vertices first. For positive demands, it uses `c(v) = occurrence F v`, selects a minimizer of `r(v)/c(v)` among vertices with `c(v) > 0`, and gives every maximum stable set weight `a = r(v₀)/c(v₀)`. Thus the total added weight is `a * |F|`, equal to the question's `ε`. This avoids dividing every occurrence count by `|F|`. The proof establishes `a * |F| ≤ k` before recursing, including when the residual support is empty. The residual support is strictly smaller, and the same clique bound remains valid on it. Finally, the demand colouring is converted to the existing `Colouring` definition, preserving its total weight and coverage.

The proof of `theorem_F_of_D` uses the existing peeling theorem and degree bound. On a minimally uncolourable support, D excludes cliques of size 16; the new Lemma A applies with `ω = 15` and `k = 20`. Neither this argument nor the elementary Lemma A uses `FractionalDuality`, a replacement duality hypothesis, or an unproved process/colouring hypothesis.

`lake --no-cache build` succeeded. A separate invocation of `lake env lean second_pass\Axioms.lean` checked the statements and printed the following exact output; see [axioms.txt](second_pass/axioms.txt). The build log is [part1-build.log](second_pass/part1-build.log).

```text
'Se20Fractional.Elementary.maximum_stable_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.Elementary.weighted_local_reed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.local_fractional_reed_elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.theorem_F_of_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.theorem_F' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For Part 2, [PropositionDReduction.lean](second_pass/PropositionDReduction.lean) is deliberately outside the default library import graph. It compiles separately with `lake env lean second_pass\PropositionDReduction.lean`; see [reduction-build.log](second_pass/reduction-build.log). Its proved results are:

- A failure of D contains an exact 16-edge clique whose selected edges all satisfy `4t + e' ≤ 4`.
- The endpoint set of a nonempty conflict clique has size at most `|Q| + 7`; hence the selected 16 edges have at most 23 endpoints. This counts the closed neighbourhood of a root edge and the at most one outside endpoint contributed by each other selected edge.
- Restricting to the induced graph on exactly these endpoints preserves all selected edges and conflicts. Degree and both local quantities cannot increase.
- Embedding the induced graph into `Fin 23` and adding isolated vertices preserves the local quantities exactly and the other required conditions.
- A permutation can send a selected edge to `01`. The map and its preservation properties are proved, rather than imposed as an assumption.
- After orienting a selected edge so that `degree a ≤ degree b`, the only possible `(degree a, degree b, t)` triples are `(2,4,0)`, `(3,3,0)`, `(3,4,0)`, `(3,4,1)`, `(4,4,0)`, `(4,4,1)`. This verifies the encoder's numerical case elimination, but does not prove its prescribed neighbour labels or lexicographic conditions.

The finite predicates are explicit:

```lean
def LocallyLow (G : SimpleGraph V) (Q : Finset G.edgeSet) : Prop :=
  ∀ a b : V, ∀ hab : G.Adj a b, (⟨s(a,b),hab⟩ : G.edgeSet) ∈ Q →
    4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card ≤ 4

def Obstruction23 (H : SimpleGraph (Fin 23)) (Q : Finset H.edgeSet) : Prop :=
  (∀ v, H.degree v ≤ 4) ∧ Q.card = 16 ∧ Clique (L2 H) Q ∧ LocallyLow H Q ∧
    ∀ v, (∃ u, H.Adj v u) → v ∈ endpoints Q

def RootObstruction23 (H : SimpleGraph (Fin 23)) (Q : Finset H.edgeSet) : Prop :=
  Obstruction23 H Q ∧ ∃ hab : H.Adj 0 1, (⟨s(0,1),hab⟩ : H.edgeSet) ∈ Q
```

The principal reduction statements, with the same finite-graph context as above, are:

```lean
theorem obstruction23_of_not_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 23), ∃ Q : Finset H.edgeSet, Obstruction23 H Q

theorem root_obstruction23_of_not_D (hΔ : ∀ v, G.degree v ≤ 4)
    (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 23), ∃ Q : Finset H.edgeSet, RootObstruction23 H Q

theorem propositionD_of_no_root_obstruction23 (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 23), ∀ Q : Finset H.edgeSet,
      ¬ RootObstruction23 H Q) : PropositionD G
```

**The `hfinite` premise is not proved.** These are reduction theorems, not an unconditional proof of D. Their exact axiom output includes:

```text
'Se20Fractional.DReduction.obstruction23_of_not_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.DReduction.root_obstruction23_of_not_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.DReduction.propositionD_of_no_root_obstruction23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

A computational experiment removed the existing encoder's root-neighbour case clauses and all lexicographic symmetry clauses, retaining only the selected root edge `01` and the original graph/gate constraints. The reproducible script is [root_only_experiment.ps1](second_pass/root_only_experiment.ps1). It generated 440,107 variables and 1,698,843 clauses. CaDiCaL was stopped after 120.025 seconds without a SAT or UNSAT verdict. The generated `root_only.lrat` is an **incomplete proof trace, not a certificate of UNSAT**. This short timeout does not establish that the encoding is infeasible to solve.

No Lean proof connects either this experimental CNF or the existing `d16.cnf` to `RootObstruction23`. The remaining work includes the variable assignment and numbering, Tseitin and sequential-counter clauses, and a theorem-backed acceptance of a concrete certificate. To reuse the existing certificate, the further neighbour relabelling and lexicographic symmetry reduction must also be proved. The existing first-pass certificate/checker results were not rerun in this pass and are not treated as discharging a Lean hypothesis. The verified BVDecide path was inspected, but no `bv_decide`/`bv_check` proof of the finite statement was produced.

Part 2 ran from `2026-11-04T19:19:26.3769766+11:00` to `2026-11-04T19:47:32.1881354+11:00`, approximately 28.10 minutes, after Part 1 built. See [part2-timing.txt](second_pass/part2-timing.txt). I stopped at the compiled finite-reduction milestone; I did not exhaust the three-hour allowance. The uncompleted stretch result is **not verified**.

No `sorry`, `admit`, new axiom, `native_decide`, or `Lean.ofReduceBool` was used in the new proofs, including the partial reductions. No commit or push was attempted. No installations were made. `REPORT.md` was preserved; its SHA256 remains `83714E215081BC874CEC5B7DC2953CE638DFDEBE201021D5DCE98C75ABA38FE3`.
