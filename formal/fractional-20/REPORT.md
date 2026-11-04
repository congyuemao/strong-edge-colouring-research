# Verification report

## Errors and qualifications found

**The peeling proof omits exact-cover normalization.** Under the stated
definition (coverage at least one), colour sets meeting a vertex can have total
weight greater than one. For example, let H=K2, delete one endpoint v, and give
the remaining singleton weight 2. This is a colouring of H-v of total 2, but
weight 2 meets N(v), although d(v)=1. This refutes the intermediate estimate for
an arbitrary colouring, not Lemma B. The repair is to normalize coverage to
exactly one and then pad with the empty stable set. Both operations and the
repaired extension argument are proved in Lean here.

**“Equivalently” in D should be read as a sufficient reduction.** Lemma C gives
`4t+e' >= 5` as a sufficient condition for L2 degree at most 19. It does not give
a pointwise equivalence: an isolated edge has L2 degree 0 and `4t+e'=0`. This
wording issue does not invalidate the stronger finite UNSAT statement.

**No counterexample to A, B, C, D, or F was found.** This is not an unconditional
Lean certification of F: finite LP strong duality and Proposition D remain
explicit hypotheses of the final Lean theorem.

## Verdicts

| Statement | Verdict and evidence |
| --- | --- |
| Lemma A | Graph-specific proof checked in Lean, conditional only on the named finite LP strong-duality/attainment hypothesis. Weak duality, normalization, and the needed complementary-slackness consequence are proved. The supplied paper proof's minimality argument is sound for nonempty graphs; the formal proof normalizes the primal directly instead. |
| Lemma B | Proved in Lean, with normalization and padding. Both threshold peeling and the integer-D vertex-critical version are proved. |
| Lemma C | Fully proved in Lean: conflict characterization, exact incidence formula, endpoint-region cardinality, and `d + 4t + e' <= 24`. |
| Proposition D | Independently computationally verified. The new full 23-slot encoding is UNSAT. Its certificate passed a separately written C++ checker and Lean's standard-library proved-sound LRAT checker. The graph-to-CNF reduction is justified in writing, not formalized. |
| Theorem F | Deduction checked in Lean with exactly `hLP` and `hD` left explicit. An unconditional Lean theorem is **not verified**. Mathematically, the evidence supports F using known finite LP duality and the checked finite step. |

The empty graph needs a convention for the maximum in informal Lemma A. The
formal colourability statement handles empty vertex sets directly.

## Independent check of Proposition D

The supplied `exp49_frac_core.py` was first read only after the full independent
UNSAT certificate passed. The pre-audit verdict is preserved in
[independent/VERDICT.md](independent/VERDICT.md).

### Method and soundness

Source: [independent/encode.cpp](independent/encode.cpp). Full soundness argument:
[independent/SOUNDNESS.md](independent/SOUNDNESS.md).

Separate Boolean variables represent graph edges and selected clique edges.
The formula requires exactly 16 selected edges, maximum degree 4, and one of
the four possible cross edges for every disjoint pair of selected edges. It
computes endpoint regions and common neighbours with Boolean equivalences,
counts each common neighbour four times, and imposes the bound 4 conditional
on selection. Every non-isolated vertex is incident with a selected edge;
isolates pad smaller instances to 23 slots.

The 23 bound is valid: restrict to endpoints of 16 selected edges. Conflict
witnesses survive inside that induced graph. For one selected edge uv, W has
at most 8 vertices, and each of the other 15 selected edges contributes at most
one endpoint outside W. Local quantities cannot increase on restriction.

Independent symmetry handling fixes a selected edge as 01, orders endpoint
degrees, enumerates all six endpoint-degree/common-neighbour patterns allowed
by the necessary root incidence bound, and sorts only exterior adjacency
vectors to W. Every graph admits such a relabelling. This differs from the
original script's double-lex scheme.

The full instance has **442,553 variables and 1,707,026 clauses** and refutes
the stronger statement with `4t+e' <= 4` at every selected edge.

### Certificate and runtime

Existing solver: **CaDiCaL 2.1.2**, with `--lrat --no-binary`.

- Solve: **350.50 seconds CPU; 361.45 seconds wall time**.
- Solver-reported maximum resident set: **391.89 MB**.
- [independent/d16.cnf](independent/d16.cnf): **37,510,408 bytes**.
- [independent/d16.lrat](independent/d16.lrat): **477,598,828 bytes**.
- [independent/d16.log](independent/d16.log): solver log.

The first checker, [independent/check_lrat.cpp](independent/check_lrat.cpp), was
written here without solver code or solver libraries. It accepts only the RUP
fragment of LRAT and rejects RAT steps. Each non-tautological addition must
produce a conflict by its unit-propagation hints; deletions are honoured and
acceptance requires an empty clause. Its result:

```text
VERIFIED UNSAT; RUP=2418926 RAT=0 deleted=3943654 seconds=19.1004
```

The second replay uses the standard library's `Std.Tactic.BVDecide.LRAT.check`,
whose soundness is proved in Lean. Wrapper:
[independent/CheckLRAT.lean](independent/CheckLRAT.lean). Output:
[independent/d16.std-check.log](independent/d16.std-check.log).

```text
'Std.Tactic.BVDecide.LRAT.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
Parsed 1707026 original clauses
Parsed 3051052 LRAT actions
Std.Tactic.BVDecide.LRAT.check = true; elapsed_ms=50630
```

This is execution of the proved-sound checker, not a kernel-reduced proof term
for this concrete CNF. Parsing and runtime/compiler execution remain in the
computational trust base, and encoding correctness is not a Lean theorem.

Checker self-tests accepted a valid proof and rejected a proof of a satisfiable
formula, a missing antecedent, a deleted antecedent, and an incomplete proof.
See [independent/checker-tests.log](independent/checker-tests.log). A preliminary
12-slot UNSAT instance is retained as `probe16.*`; it is not the basis of the
full verdict.

SHA256:

```text
d16.cnf  05F89B4089DDB6668E1FC5DC8873FC807DE1A487BF81A9DE60A8628E0420F8D4
d16.lrat 6E60536ABFA146C11EF7D7F9F7072AB20ADAA4EEDA836F41F0CEF57C994FC3D2
```

### Positive controls

Both passed [independent/check_model.cpp](independent/check_model.cpp), which
checks every original CNF clause and independently reconstructs graph degrees,
pairwise conflicts, common neighbours, internal R edges, and Lemma C's identity.

- **15 selected edges at bound 4: SAT.** There are 11 non-isolated vertices,
  22 graph edges, and selected-edge L2 degrees 20 or 21. Graph and statistics:
  [independent/control15.graph.txt](independent/control15.graph.txt).
- **20 selected edges at bound 5: SAT.** The model is C5[2], with twin pairs in
  cycle order `(0,5), (1,3), (6,7), (8,9), (2,4)`. Every edge has `t=0`, `e'=5`,
  and L2 degree 19. Graph:
  [independent/control20.graph.txt](independent/control20.graph.txt).

### Audit of the supplied encoding

Detailed audit: [independent/AUDIT.md](independent/AUDIT.md).

No over-constraint was found in its **default bound-4 run with both root cases
and nT=15**. Endpoint-neighbour slots are optional, covering low endpoint
degrees. Padding and the 23/22 slot bounds are sound. The one-way auxiliary
implications suffice for equisatisfiability. Double-lex symmetry follows by
taking a lexicographically greatest matrix in the allowed row/column orbit;
the shared triangle column is excluded from column permutations.

Limitations: smaller `nt` or one root case is not a full check. Hard-coding at
most one common neighbour makes arbitrary relaxed bounds >=8 unsound
generalizations. Its model checker tests the necessary `4t+e'` bound, not actual
L2 degree, and does not separately recheck `dz`. The script produces no proof
certificate. None of these issues invalidates its default instance. The
original file was read, not executed or modified.

## Lean development

Toolchain: `leanprover/lean4:v4.35.0-rc4`, with the configured local Mathlib.
The final project build passed, including the default library target.
Modules were built sequentially with
[independent/build_lean.ps1](independent/build_lean.ps1). Log:
[independent/lean-build.log](independent/lean-build.log).

| File | Content |
| --- | --- |
| [Definitions.lean](Se20Fractional/Definitions.lean) | `L2 : SimpleGraph G.edgeSet`, actual unordered edges, stable sets, cliques, support degrees, nonnegative fractional colourings with coverage >=1. |
| [DegreeFormula.lean](Se20Fractional/DegreeFormula.lean) | Full Lemma C and the degree bound 24. |
| [Peeling.lean](Se20Fractional/Peeling.lean) | Normalization by splitting weighted sets, padding, extension, threshold peeling, and integer-D vertex-critical peeling. |
| [LocalReed.lean](Se20Fractional/LocalReed.lean) | Explicit LP hypothesis, weak duality, optimum characterization, complementary slackness, and conditional Lemma A. |
| [TheoremF.lean](Se20Fractional/TheoremF.lean) | Explicit Proposition D and conditional Theorem F. |

The finite-family colouring representation allows repeated stable sets.
Merging equal sets adds their weights and preserves total and coverage;
conversely a weighting of stable sets is a finite family. The conclusion
`FractionalColourable (L2 G) 20` thus asserts an actual colouring of total at
most 20, not a redefinition making the bound trivial.

Lemma C is stated without natural-number subtraction:
`d_L2(y) + e'(y) = sum_{w in R} degree(w)`, and
`d_L2(y) + 4*t(y) + e'(y) <= 24`.

For B, `IsFractionalChromaticOn G U k` says k is an attained minimum: a colouring
of budget k exists and every feasible budget is at least k. The integer-D
theorem takes `D < k` and a strictly smaller feasible budget for each deletion,
and concludes all induced degrees are at least D. Criticality therefore has
its intended mathematical meaning.

### Exact remaining hypotheses

`FractionalLPWitness G U` contains a feasible primal colouring, nonnegative dual
weights satisfying every stable-set inequality, and equality of the objectives.
`FractionalDuality G` asserts such a witness exists for every support U. It
contains no Reed, clique, or degree estimate. The proved theorem
`FractionalLPWitness.is_optimal` identifies its primal objective with the
attained fractional chromatic minimum.

The derivation of this existence statement from Mathlib's geometric Farkas /
Hahn–Banach results was **not completed**. The available APIs and the exact
uncompleted cone-closedness and attainment reduction are documented in
[independent/LP_DUALITY.md](independent/LP_DUALITY.md). Weak duality and all
graph-specific complementary-slackness work are completed. No axiom was added.

`hD : PropositionD G` states precisely that every Q of actual edges forming a
clique in `L2 G`, with `16 <= Q.card`, contains some y whose full L2 degree is
at most 19. It is not a property of an artificially restricted clique type.

The final theorem has the form:

```text
theorem_F
  (hDelta : forall v, G.degree v <= 4)
  (hLP : FractionalDuality (L2 G))
  (hD : PropositionD G) :
  FractionalColourable (L2 G) 20
```

The SAT result was not connected to `hD` inside Lean. The standard-checker
replay does not formalize the graph reduction or remove this hypothesis.

### Exact axiom output

Fresh output, including theorem signatures and the hypothesis structures, is
saved in [independent/axioms.txt](independent/axioms.txt), generated by
[independent/Axioms.lean](independent/Axioms.lean):

```text
'Se20Fractional.l2_adj_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.region_degree_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.degree_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.degree_formula_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.l2_degree_le_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.normalize_colouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.extend_colouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.peeling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.vertex_critical_peeling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.weak_duality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.FractionalLPWitness.is_optimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.stable_set_local_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.local_fractional_reed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Fractional.theorem_F' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms. Explicit hypotheses `hLP` and `hD` do
not appear in `#print axioms`; that does not mean they have been discharged.
The theorem source scan found no `sorry`, `admit`, new `axiom`, or `native_decide`.

## Reproduction and work not done

From this directory, `independent/build.ps1` compiles the C++ tools using the
existing MinGW g++ 13.1.0 on E:. `independent/reproduce_sat.ps1` recreates the
instances, controls and certificate and runs both checkers. It overwrites
generated outputs and may produce a different valid proof on another solver
build. `independent/build_lean.ps1` builds Lean sequentially. All scripts set
the environment requested in the brief.

The supplied Python venv could not launch because its base interpreter was
unavailable. Clang lacked C++ standard-library headers, so the existing
E:-drive MinGW compiler was used. Nothing was installed.

Not done:

- No SAT-free exhaustive enumeration.
- No completed Lean proof of LP strong duality / attainment.
- No formal graph-to-CNF reduction or discharge of `hD`.
- No kernel proof term for the concrete 477 MB certificate; the proved-sound
  standard checker was executed as an IO program.
- No rerun of the original Python script or its external graph corpus.
- No pushes, publication, or edits to another repository.
- **No local git commit:** `git add` / `git commit` failed with
  `Unable to create 'E:/lean/se20-fractional/.git/index.lock': Permission denied`.
  Git metadata is read-only in this sandbox and escalation is unavailable.
  All work is saved here. The pre-existing `codex_run.log` was left alone.
