# Part I formalization report

The earlier pass records are preserved below. Current results and limitations are in [Third pass](#third-pass).

## Flaws and proof gaps first

**The independent-transversal remark after Proposition 3.13 has a missing disjointness argument.** It treats the candidate sets `P(h)` as parts of a partition of the candidate edges. Those sets can overlap under the local hypotheses used in that argument.

Here is the local configuration, in a tree. Take a path `x₀–x₁–x₂–x₃–x₄–x₅`, defect edges `yx₀` and `x₅z`, and matching edges `h=x₁b`, `h'=x₄c`, and `s=x₂x₃`, with `b,c,y,z` off the path. The defect-edge distance is 5. The option `x₂` for `h` and the option `x₃` for `h'` are covered by the **same** matching edge `s`. To make both edges problem edges, give `x₁` one additional neighbor `a`, give `b` three new neighbors, and cover `x₀`, `a`, and those three new neighbors with separate matching edges to new leaves. Do the symmetric construction at `x₄,c,x₅`. This is still a tree of maximum degree four; both problem edges have all six external vertices covered. In particular, `P(h) ∩ P(h')` contains `s`.

This is a defect in the stated use of Haxell, **not a counterexample to Theorem B or B+**, and the local example is not asserted to be a complete odd-cycle decomposition satisfying every global premise of Proposition 3.13. The argument needs either an additional disjointness proof from those global premises or a different transversal formulation. Tagging each candidate by its problem edge makes disjoint parts, but then the degree bound must be proved for that new graph; it does not follow automatically from the degree bound for the graph on untagged candidate edges.

The need for this distinction is kernel-checked in `OverlapAudit.lean`: the graph with conflict edges `01` and `23` has degree one, and the four overlapping size-two sets `{0,2}`, `{0,3}`, `{1,2}`, `{1,3}` have no independent choice of representatives, even allowing repeated representatives. Thus Haxell's disjoint-part hypothesis cannot simply be omitted. This abstract counterexample is not claimed to realize the manuscript's full geometric configuration.

**The older reference still contains the known erroneous girth-8 version of Lemma 3.9(b).** `LARGE_GIRTH_zh.md` §10.4 states that version; its §10.8 and the manuscript correct it to girth at least 9. The recorded Lean statement uses 9. No Lean proof of this lemma or of the historical counterexample is claimed here.

**The numerical certificate for Theorem B+ is not reproducible from the supplied files alone as an explicitly specified matrix computation.** The manuscript describes a 42-state matrix and refers to `exp31_lll_girth.py`, but neither its entries, an indexed state/transition definition, nor that program is in `reference/`. A matrix could be reconstructed, but its correspondence to the specified counting problem would itself require proof. No guessed matrix or floating-point certificate has been substituted.

## Overall status

This is a **partial formalization**, not a completed formalization of Part I. Lemmas 3.1 and 3.2, Remark 3.3, Theorem A, and Theorems B′ and B″ are proved. The finite edge-ball upper bound and several substantial parts of the B/B+ reductions are also proved. **Theorems B and B+ are not proved.**

All mathematical conflicts use `L2 G` on the actual subtype `G.edgeSet`, with the same definition as the supplied sister-project insertion file. `MaxDegreeFour` is also the same `∀ v, G.degree v ≤ 4` definition. No sister-project source was imported or edited.

`GirthAtLeast G g` means every simple cycle has length at least `g`. `girthAtLeast_iff_egirth` proves its equivalence to `(g : ℕ∞) ≤ G.egirth`. This includes forests at every finite threshold, avoiding Mathlib's natural-valued `girth = 0` convention for forests. `DegreeLE` uses `Nat.card` of the neighbor subtype to avoid dependence on a particular `Fintype` enumeration; `degreeLE_iff` proves equivalence to ordinary degree bounds on finite graphs.

## Target-by-target status

| Target | Status and exact scope | File / main declarations |
|---|---|---|
| Lemma 3.1(a) | Proved: exact equality of conflict degree and the number of matching-covered external vertices; maximum degree at most 6 | `Contraction.lean`: `matching_degree_eq_covered_external`, `external_card_le_six`, `matching_maxDegree_six` |
| Lemma 3.1(b) | Proved: every matching-conflict cycle lifts to an ambient cycle of length at most twice its length; both integer-threshold and extended-girth formulations | `Contraction.lean`: `lift_matching_path`, `matching_cycle_lift`, `matching_girth`, `matching_egirth` |
| Lemma 3.2 | Proved for arbitrary covers, including overlaps. The matching assumption is unnecessary. Both explicit palettes and the literal chromatic-number sum inequality are provided | `Assembly.lean`: `assembly`, `assembly_uniform`, `assembly_chromaticNumber` |
| Remark 3.3 | Proved in full for finite graphs: construct `G` on `V × Bool`, with maximum degree 4, a matching, a conflict-graph isomorphism with the input `H`, and preservation of every girth lower bound | `Split.lean`: `remark_3_3` |
| General Kostochka ⇒ K6, K5 | Proved, including the real inequalities containing `Real.exp 1` | `External.lean`: `Kostochka.to_K6`, `Kostochka.to_K5`, both `kostochka_*_numeric` lemmas |
| Theorem 3.4 / A | Proved with only the explicit `Kostochka` literature hypothesis | `ColouringTheorems.lean`: `theorem_A` |
| Section 2, Fact 3 | Finite-graph upper bound proved for every natural radius, including radius zero. All seven displayed constants are checked. Equality in the infinite 4-regular tree is not proved | `Balls.lean`: `edgeBall_card_le`, `ball_constants` |
| Theorem B, step 1 | Not proved. Euler orientation and König decomposition were not replaced by hypotheses of a claimed Theorem B | Exact target in `OpenStatements.lean`: `TwoDegreeDecompositionStatement` |
| Theorem B, step 2 | Haxell selection proved for a supplied partition of eligible edges with sufficiently large fibers. The odd-cycle partition still needs to be constructed from step 1 | `Selection.lean`: `sparse_transversal`, `sparse_transversal_eight` |
| Theorem B, step 3 | Not proved: decomposition into paths/even cycles after deleting one edge from each odd cycle, then alternating edge-coloring | — |
| Lemma 3.6 | Not proved; its simultaneous local-dominator statement, including layers 2/3 and pairwise separation, is recorded | `OpenStatements.lean`: `LocalDominatorsStatement` |
| Theorem B, steps 4–6 | Proved as a reduction from a supplied matching cover, induced defect matching, and independent seed avoiding defects and dominating all degree-6 forbidden vertices. Seed construction is not assumed implicitly | `Domination.lean`; `SeedReduction.lean`: `twenty_of_dominating_seed` |
| Theorem 3.5 / B | Not proved | `TheoremBStatement` is an unproved proposition definition |
| Theorems 3.7, 3.8 | Proved with their original Property P / Property R conditions and explicit Kostochka hypothesis | `ColouringTheorems.lean`: `theorem_B_prime`, `theorem_B_double_prime` |
| Lemma 3.9(a), (b), Corollary 3.10 | Not proved; precise finite-graph targets recorded, with the corrected threshold 9 in (b) | `OpenStatements.lean`: `DeadEdgeAStatement`, `DeadEdgeBStatement`, `NoDeadEdgesStatement` |
| Lemma 3.11 | Not proved. Genuine infinite-tree representation and the full target are recorded. The parent-map non-facing argument is separately proved | `OpenStatements.lean`: `InfiniteFourTree`, `TreeLemmaStatement`; `LocalGeometry.lean`: `no_facing_parent_choices` |
| Proposition 3.13 | Not proved. The distance-5 Haxell bound and the parent-map path obstruction are proved, but construction/orientation of the option graph and geometric conflict analysis are missing | `Selection.lean`: `sparse_transversal_five`; `LocalGeometry.lean` |
| Haxell transversal remark | Proved for actual disjoint parts, represented as fibers of a surjective map; original overlapping-candidate issue remains as explained above | `Selection.lean`: `haxell_degree_one`; `OverlapAudit.lean` |
| Lemma 3.15 | Only step 1 is proved: every simple path of length less than half the girth is geodesic. The spanning-family implication is not proved | `LocalGeometry.lean`: `short_paths_unique`, `short_path_geodesic` |
| Theorem 3.14 / B+ | Not proved. Neither the probabilistic construction nor its matrix enumeration is formalized | `TheoremBPlusStatement` is an unproved proposition definition |
| Numerical step at 5710 | Logarithm lower bound and final rational comparison proved. The actual 42-state matrix bound remains unverified and parameterized | `Numerics.lean`: `TransferMatrix5710Bound`, `log_beta5710_lower`, `numerical5710_suffices` |
| Local lemma itself | Stated as a named proposition, not proved | `External.lean`: `LovaszLocalLemma` |

## Exact proved statements and assumptions

For all finite simple graphs, with colors numbered from zero:

- `theorem_A`: `Kostochka → MaxDegreeFour G → EdgeColourable G 4 → GirthAtLeast G 41 → StrongColourable G 20`.
- `theorem_B_prime`: `Kostochka → MaxDegreeFour G → GirthAtLeast G 69 → PropertyP G → StrongColourable G 20`. Property P is a genuine matching-fiber coloring with at most five matching-covered external vertices per edge.
- `theorem_B_double_prime`: `Kostochka → MaxDegreeFour G → GirthAtLeast G 69 → PropertyR G → StrongColourable G 20`. Property R has five matching fibers, degree at most five in fiber 3, and fiber 4 an induced matching.
- `matching_degree_eq_covered_external`: for a matching `M` and `e : M`, under girth at least 5, `degree (L2 G)[M] e = card (External G e ∩ Covered M)`.
- `matching_egirth`: `IsMatching M → G.egirth ≤ 2 * (ConflictGraph G M).egirth`. The proof does not need a degree bound or girth at least 5.
- `assembly_chromaticNumber`: for any finite cover `M`, `χ(L2 G) ≤ Σ i, χ((L2 G)[M i])`.
- `edgeBall_card_le`: `MaxDegreeFour G → Nat.card {f ≠ e | endpoint-distance(e,f) ≤ k} ≤ 3^(k+2)-3`. Distance is represented by existence of a walk of length at most `k`, so disconnected components cannot create spurious zero distances.
- `sparse_transversal_eight`: from `Haxell`, degree at most four, a surjective partition of eligible edges, and fibers of size at least 39360, obtain one edge from each fiber with no two within endpoint-distance 7. The analogous threshold is 1452 for distance 4.
- `twenty_of_dominating_seed`: under Kostochka, degree at most four and girth at least 69, four matching sets plus an induced defect matching covering all edges yield twenty colors **when** an independent seed in the fourth matching avoids every defect and dominates every degree-6 conflict vertex that conflicts with a defect. The proof extends the seed maximally, removes at least one neighbor from every remaining degree-6 vertex, then uses palettes `5+5+5+4+1`. Its seed and cover hypotheses are explicit; it is not named or presented as Theorem B.

`Kostochka`, `K6`, `K5`, `Haxell`, and `LovaszLocalLemma` are ordinary `def ... : Prop`, with no inhabiting declaration asserted. The Kostochka definition states the general numerical criterion with real subtraction and `q=(g+1)/2`. K6 and K5 are derived at the fixed thresholds 21 and 35; larger-girth graphs satisfy those fixed thresholds, so no additional monotonicity premise for the numerical expression is needed. The kernel-checked bound `exp 1 < 3` is already sufficient: K6 is bounded by `297*3 = 891 < 1024`, and K5 by `315*3 = 945 < (3/2)^17`.

Haxell is stated for a surjective partition map, ensuring nonempty parts even when the degree bound is zero. The local lemma is the finite general asymmetric form for normalized nonnegative probability weights, with joint independence from every intersection of nonneighbor event complements. This suffices for the finite random variables in the manuscript, but its application and proof remain unfinished.

The definitions ending in `Statement` in `OpenStatements.lean` are **unproved specifications**. They are not axioms and are not used to prove A, B′, or B″. Adding such a definition proves none of its mathematical content.

## Infinite tree and numerical representation

`InfiniteFourTree` consists of an arbitrary infinite vertex type, a `SimpleGraph`, a proof of `IsTree`, finite neighbor sets, and neighbor cardinality exactly four. No finite truncation is substituted for the infinite tree. `TreeLemmaStatement` includes the two-factor partition, defect separation, matching containment in `F₂ \ D`, coverage of nondefect vertices, and all three conclusions for `J`. The tree lemma is still unproved.

For the numerical interface, `M : Matrix (Fin 42) (Fin 42) ℚ` is intended to be the matrix **already evaluated at** `t = (1203/1000)/5710`. Define `u_k` as the sum of all entries of `M^k`. The exact named hypothesis is

```text
TransferMatrix5710Bound M :
  (1-t)^(-1) *
    (726*β*t + (9/4)*β*(Σ δ=1..5, 12*3^δ)*
      (Σ k=0..2854, u_k*u_(2854-k))) ≤ 184154/1000000,
  where β=1203/1000 and t=β/5710.
```

This is a rational inequality, not an opaque floating-point assertion. It is **not proved for any concrete transfer matrix**. `numerical5710_suffices` proves that this hypothesis implies the displayed real local-lemma inequality, using the independently proved `184818/1000000 ≤ log(1203/1000)`. The logarithm bound uses three terms of Mathlib's positive series for `log((1+x)/(1-x))/2`, with `x=203/2203`. The rational slack is exactly `83/125000`.

## Remaining proof work and blockers

1. **Finite decomposition:** the local Mathlib `Combinatorics/SimpleGraph/Trails.lean` has necessary parity facts for Euler trails, but explicitly lists existence as a TODO. A search of the local graph library found no König edge-coloring theorem. A balanced orientation plus the needed degree-two bipartite edge-coloring must be implemented, or the two-degree decomposition must be proved by a different finite argument. The decomposition is not imported from another project and is not smuggled into a cited-theorem hypothesis.
2. **Odd components:** classify finite maximum-degree-two components, form their odd-cycle edge partition, prove the part-size bounds, and obtain the four matchings by alternating colors after defect deletion. The reusable Haxell selection theorem is ready, but supplying these objects is not done.
3. **Local geometry:** Lemma 3.6 requires turning the manuscript's small tree neighborhoods into explicit unique-path and distance arguments, then constructing simultaneous seed choices. Lemmas 3.9 and Corollary 3.10 additionally need distinct-killer counting. `short_paths_unique` supplies the basic girth tool; none of those local conclusions is asserted as a proved theorem.
4. **Tree/pseudoforest coordination:** construct the root/parent map (or pseudoforest orientation), prove the option geometry and the facing-only conflict implication, then apply `no_facing_parent_choices`. The infinite representation and the path obstruction do not by themselves prove Lemma 3.11 or Proposition 3.13.
5. **B+:** define the option graph and spanning families; prove the rest of Lemma 3.15; give and verify the actual transition system; prove the weighted counting bounds and variable dependency bookkeeping; then prove the rational matrix inequality or retain that exact numerical hypothesis. Even a verified numerical bound alone would not complete B+ at the current state.
6. **Optional local lemma proof:** not attempted to completion while these earlier geometric and decomposition targets remain open.

## Build and axiom audit

The complete default build finished with exit code **0** on 2026-11-06, including all 15 modules, the axiom audit, and the root library. The source scan found no `sorry`, `admit`, `native_decide`, `sorryAx`, or project axiom declarations. One harmless tactic-style linter warning remains in `Split.lean`.

Use `./build.ps1` from this directory. Its default module list includes every project module and `AxiomAudit`. A selected list can be supplied, for example `./build.ps1 -Modules Balls,Selection,AxiomAudit` after their dependencies have been compiled.

The script invokes the already-installed Lean 4.35.0-rc4 compiler directly and assembles `LEAN_PATH` from this project's output and the existing local package `.olean` directories. It never invokes Lake, a package manager, an installer, or a network tool. All project output is inside this workspace; temporary/cache environment variables point to E:.

**Build-setup incident:** the first run of the *supplied* script used `lake env lean`. Despite its comment, Lake attempted to fetch the absent transitive `plausible` dependency. That network connection failed. No dependency was downloaded or installed. The script was immediately changed to direct offline compiler invocation; subsequent builds have no Lake fetch path.

`Se20Part/AxiomAudit.lean` has `#print axioms` for all main proved results, including the reduction and audit counterexample. Raw final build/audit output is saved in `build-output.txt`. The audited results use only subsets of Lean's standard foundations:

```text
[propext, Classical.choice, Quot.sound]
```

For example, A, B′, B″, both matching-contraction parts, Remark 3.3, the ball bound, sparse selection, and the seed reduction report this standard set. `independent_union` reports no axioms; `ball_constants` reports only `propext`. There are no project axioms, `sorryAx`, or native-evaluation trust axioms. Ordinary `decide` in the four-vertex audit is kernel reduction, not `native_decide`.

Selected literal audit output (the complete output is in `build-output.txt`):

```text
'Se20Part.Kostochka.to_K6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Kostochka.to_K5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.matching_degree_eq_covered_external' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.matching_cycle_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.assembly_chromaticNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.remark_3_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.theorem_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.theorem_B_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.theorem_B_double_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.edgeBall_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.sparse_transversal_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.sparse_transversal_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.twenty_of_dominating_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.numerical5710_suffices' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit establishes the foundational dependencies of the **proved declarations**. It does not discharge the explicitly listed literature hypotheses, unproved specifications, or matrix inequality.

## Second pass

### Flaws and limitations first

**B+ still has two explicit transfer-matrix hypotheses.** The matrix is now concrete, and the geometric and probabilistic reductions are proved. However, neither `TransferMatrix5710Bound exp31Matrix5710` nor `TransferMatrixSpanningFamilyBound` is proved. The latter is a **weighted counting correspondence for embedded spanning families**, including the per-part convolution bound. It is stronger than merely identifying a scalar depth-pattern generating function with a matrix product. This additional scope must not be hidden under the word “numerics.” The user allowed a retained counting correspondence and numerical bound; the exact retained propositions are described below. The unchanged, unqualified `TheoremBPlusStatement` in `OpenStatements.lean` is consequently still uninhabited.

**The first-pass assertion that the numerical source was missing is obsolete.** `reference/exp31_lll_girth.py` and `reference/exp31.log` were supplied for this pass and were read. `TransferMatrix.lean` now implements their indexed 42-state matrix over the rationals. The supplied short-segment brute comparisons do not establish the correspondence for arbitrary lengths. An independent floating-point reconstruction of the 162 transitions reproduced RHS approximately `0.1841539517856228`; this is only a sanity check, not a kernel certificate and not a proof of the retained rational inequality.

**The tagged-versus-untagged degree distinction remains essential.** The corrected remark is proved for the actual geometric candidates in `ConcreteTagged.lean`. It assumes maximum degree one of the graph on tagged candidates `(problem edge, candidate)`. No implication from the untagged degree bound is claimed. The first-pass overlap counterexample remains valid. The supplied revised manuscript now makes this correction explicitly.

**The historical girth-8 version of Lemma 3.9(b) remains erroneous.** The second pass proves the corrected girth-9 statement. Part (a) is proved at girth 8, hence also at 9. Corollary 3.10 is proved at girth 6, as specified in the existing target. No statement already proved in the first pass was changed.

The status tables above describe the first pass. The following results supersede their “not proved” entries.

### Results and exact scope

| Requested target | Second-pass result | Main declaration / file |
|---|---|---|
| Theorem B, step 1 | Exact finite maximum-degree-two edge partition proved | `two_degree_decomposition : TwoDegreeDecompositionStatement`, `Decomposition.lean` |
| Steps 2–3 | Constructed cycle partition, Haxell selection, and four matching cover; see the explicit all-cycle variant below | `sparse_four_matching_cover`, `sparse_four_matching_cover_five`, `CycleSelection.lean` |
| Lemma 3.6 | Exact simultaneous statement, including layers 2/3 and pairwise endpoint-distance at least 4 | `local_dominators : LocalDominatorsStatement`, `LocalDominators.lean` |
| Theorem 3.5 / B | **Proved with exactly `Kostochka` and `Haxell`** | `theorem_B`, `theorem_B_statement : TheoremBStatement`, `TheoremB.lean` |
| Lemma 3.9(a), (b) | Exact existing statements proved, at girths 8 and 9 respectively | `dead_edge_a : DeadEdgeAStatement`, `dead_edge_b : DeadEdgeBStatement`, `DeadEdges.lean` |
| Corollary 3.10 | Exact existing statement proved | `no_dead_edges : NoDeadEdgesStatement`, `DeadEdges.lean` |
| Lemma 3.11 | Exact statement on the genuine `InfiniteFourTree`; no finite-ball substitution | `tree_lemma : TreeLemmaStatement`, `TreeLemma.lean` |
| Proposition 3.13 | Concrete option graph, direct pseudoforest orientation, facing-conflict exclusion, and twenty-colour conclusion | `pseudoforest_parent`, `proposition_3_13`, `Pseudoforest.lean`, `OptionGraph.lean` |
| Corrected Haxell remark | Tagged candidates, cardinality at least two proved for the actual candidate sets, seed constructed under tagged degree at most one | `geometric_tagged_haxell_seed`, `ConcreteTagged.lean`; general tagged selection in `TaggedSelection.lean` |
| Lemma 3.15 | Full finite spanning-family conclusion at girth at least 42, with actual nearest positions and depths | `lemma_3_15`, `SpanningFamily.lean` |
| Spanning-family reductions | At most one edge per position after thinning; depths 1–5; pairwise depth/position spacing inequality proved | `SpanningFamily.distinct_positions`, `SpanningFamily.pair_spacing` |
| Theorem 3.14 / B+ | Proved **conditionally on the explicitly retained matrix counting and numerical bounds** | `theorem_B_plus`, `TheoremBPlus.lean` |
| General asymmetric finite local lemma | **Proved**, with the exact joint non-neighbor independence hypothesis in `External.lean` | `lovasz_local_lemma : LovaszLocalLemma`, `LocalLemma.lean` |

For finite `G`, the main theorem types are:

```text
theorem_B:
  Kostochka → Haxell → MaxDegreeFour G →
  GirthAtLeast G 39360 → StrongColourable G 20

theorem_B_plus:
  Kostochka → LovaszLocalLemma → TransferMatrixSpanningFamilyBound →
  TransferMatrix5710Bound exp31Matrix5710 →
  MaxDegreeFour G → GirthAtLeast G 5710 → StrongColourable G 20

theorem_B_plus_of_transfer_bounds:
  Kostochka → TransferMatrixSpanningFamilyBound →
  TransferMatrix5710Bound exp31Matrix5710 →
  MaxDegreeFour G → GirthAtLeast G 5710 → StrongColourable G 20

lovasz_local_lemma : LovaszLocalLemma
```

The last B+ corollary uses the newly proved local lemma. `Haxell` is not a B+ hypothesis.

`proposition_3_13` takes `Kostochka`, degree at most four, girth at least 1452, a supplied four-matching cover together with the defect set, distance-five separation, disjointness of the defects from the fourth matching, and `IsPseudoforest (optionGraph G D (M 3))`. It concludes `StrongColourable G 20`. The existence of a distance-five matching cover under `Haxell` is separately proved by `sparse_four_matching_cover_five`; pseudoforestness of that particular Haxell selection is not asserted.

`lemma_3_15` takes a cycle `Z` of the actual option graph and a simple ambient path `Y` whose vertices and edges lie on `Z`, with `2 * Y.length < g`, `42 ≤ g`, and distance-five defects. It proves that `Y` is geodesic and constructs a finite family of defect edges spanning every edge of `Y`. Each edge has a nearest endpoint, nearest position, and depth between 1 and 5. `EdgeProjection.metric_minimal` identifies the walk-length minimum with the extended graph distance; `EdgeProjection.depth_pos_unique` proves uniqueness. The geometric proof uses a gate property for paths of length at most seven, not an assertion that the whole long path and all its surroundings lie in one bounded tree ball.

### Proof routes used

**Step 1 uses a regular completion and two Hall counting arguments.** Two copies of the graph are completed to a loopless 4-regular multigraph by adding `4 - degree(v)` parallel cross edges at each corresponding pair of vertices. A Hall condition, proved by uniform incidence counting, matches edges to two endpoint slots per vertex and yields a balanced orientation. A second uniform-fiber Hall argument splits the directed edges into two colors, with at most one incoming and one outgoing edge of each color at every vertex. Restricting to the original graph gives the required maximum-degree-two partition. The stronger directed form is also proved. Mathlib's proved finite Hall theorem is used; there is no Euler-tour, König, orientation, or decomposition assumption added to Theorem B.

**Steps 2–3 deliberately cut every cycle component, including even cycles.** This is a different proof of the same final cover statement, not a weakening of Theorem B. The directed decomposition gives a maximum-degree-two graph on the actual edges, with girth inherited from the ambient graph. Its cyclic connected components form disjoint eligible parts, each of size at least the girth. Haxell chooses one edge per part. Removing these edges leaves forests; their two-colorings, combined with the two factor labels, give four matchings. The thresholds remain 39360 for separation eight and 1452 for separation five. The implementation therefore does not separately prove the manuscript's literal odd-only deletion followed by alternating even-cycle coloring. The same all-cycle variant is used for B+, and the probabilistic bounds are stated for arbitrary disjoint eligible parts of the required size.

**The local and tree arguments are direct.** Short non-backtracking walks are proved simple and geodesic below the relevant girth bounds. Degree-six problem edges force degree four at their endpoints. These facts produce the local arms, their layers and separation, and the common-killer counting arguments. The infinite-tree proof constructs parent pointers on the actual infinite tree. Its intermediate `infinite_tree_seed` is stronger than the manuscript use: the extra two-factor and coverage premises are not needed for that intermediate result; the exact original `TreeLemmaStatement` is then discharged unchanged.

**The option graph is constructed, not assumed to come with an orientation.** `OptionArcAt` records genuine arm choices and their covering matching edges. `FacingCore` is the interior of a shortest defect-to-defect path of length 5, 6, or 7, with options at both ends. `optionGraph` is the union of these edges. Pseudoforest components are oriented by rooting tree components or deleting one cycle edge, rooting the resulting tree at an endpoint, and restoring the deleted edge. The facing-only conflict implication and the parent-map obstruction then construct the seed used by `twenty_of_dominating_seed`.

**The B+ probability bookkeeping is proved.** `VariableLocalLemma.lean` proves uniform cylinder probabilities and joint independence from all non-neighbor events, derives the variable product criterion, and proves the logarithmic budget estimate. `RandomTransversal.lean` turns weighted event bounds into a transversal. `BadFamilies.lean` defines both finite event classes and proves the first-class bound `726 β t` by counting pairs incident with each part. Same-part pairs are excluded explicitly. `TheoremBPlus.lean` proves that avoiding the pair events gives separation five and avoiding the chain events makes every resulting option graph acyclic. Thus the geometry, dependency graph, event probabilities, first-class counting, LLL application, and final colouring assembly are not retained as hypotheses.

Finally, `LocalLemma.lean` proves the general finite asymmetric local lemma by induction on conditioning sets and multiplicative avoidance bounds. The proof avoids division by an avoidance probability, so positivity is derived rather than assumed during the induction.

### Exact remaining transfer-matrix assumptions

`exp31Matrix t` is an explicit `Matrix (Fin 42) (Fin 42) ℚ`. Index `i` represents
`l = i / 7 + 1` and `s = i % 7 + 1`, except residue 6 represents `s = 99`.
Its destination-row/source-column entries sum exactly the transition rules in the supplied program: no outgoing transitions for `l > 5`; `l₁ = min(l+1,6)` and `s₁ = min(s,7-l)-1`; the empty-placement transition has weight 3; depth-`d` placements have weight `6 * 3^d * t` with the specified distance and pending-budget conditions. Matrix nonnegativity is proved. `exp31Matrix5710` evaluates it at `t = (1203/1000)/5710`.

The retained **numerical hypothesis** is the original rational predicate, now specialized to this concrete matrix:

```text
TransferMatrix5710Bound exp31Matrix5710 :
  (1-t)^(-1) * (726*β*t + S₂) ≤ 184154/1000000,
  β = 1203/1000, t = β/5710,
  S₂ = (9/4)*β*(Σ δ=1..5, 12*3^δ)*
       (Σ k=0..2854, u_k*u_(2854-k)),
  u_k = Σ i j, (exp31Matrix5710^k) i j.
```

The retained **counting hypothesis** `TransferMatrixSpanningFamilyBound` states: for any finite graph of maximum degree four and girth at least 5710, any eligible edge set partitioned into nonempty parts of size at least 5710, and each part `i`, the sum of

```text
weight(S) = ∏ C ∈ part(S), (1203/1000) / |C|
```

over `ChainBad` families meeting part `i` is at most `transferContribution5710 exp31Matrix5710`. A `ChainBad` family is a nonempty finite edge set meeting each part at most once, separated by distance five, and spanning a simple path of length 2854 with actual nearest projections, depths 1–5, and distinct positions. Families are indexed by their edge sets; multiple witnessing paths do not create duplicate events.

This is a precise weighted enumeration statement, **not** the assertion that a good defect set exists or that B+ holds. The obstruction to removing it is the unproved encoding/counting injection for embedded families, including the rooted two-sided extension bound and endpoint factors. `TransferMatrix.lean` also records the narrower, unused `TransferMatrixSpanningCorrespondence`: equality between its explicit scalar depth-pattern count and accepted matrix count for every length. Neither that identity nor its implication to the embedded-family bound is proved. Checking finitely many short lengths would not close either obligation.

No rational certificate for all matrix iterates through 2854 was imported into Lean in this pass. The independently proved logarithm lower bound and final slack comparison are reused once the concrete numerical hypothesis is supplied.

### Axioms, verification, and what remains

`AxiomAudit.lean` now prints the foundational dependencies of all main second-pass results, including B, the dead-edge lemmas, the infinite-tree lemma, Proposition 3.13, the concrete tagged remark, Lemma 3.15, the random-transversal reduction, B+, and the general local lemma. Their outputs contain only Lean's standard foundations:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, the audited declarations `theorem_B`, `tree_lemma`, `proposition_3_13`, `lemma_3_15`, `lovasz_local_lemma`, and `theorem_B_plus_of_transfer_bounds` all have this standard set. Ordinary hypotheses such as `Kostochka` and the two transfer bounds are theorem parameters, not axioms; `#print axioms` does not discharge them.

The complete default offline build of all 34 modules and the root library finished with **exit code 0 on 2026-11-06**. Final output is recorded in `build-output-second-pass.txt`. The original `build-output.txt` is retained as the first-pass record. No source declarations use `sorry`, `admit`, `native_decide`, `sorryAx`, or new project axioms. Minor style/deprecation linter warnings do not affect kernel checking. No packages were fetched or installed during this pass.

One earlier full-build attempt stopped on a read error for the existing Mathlib artifact `LinearAlgebra/Matrix/Charpoly/Coeff.olean.private`. The file was present and readable immediately afterwards. No dependency was changed; a fresh complete build succeeded. The failed attempt is preserved in `build-output-second-pass-first-attempt.txt`.

Within the requested second-pass targets, the remaining mathematical obligations are the two explicit B+ transfer bounds above, plus the unused scalar correspondence if it is to serve as a stepping stone to the counting bound. Theorems B, Lemmas 3.6/3.9/3.11/3.15, Corollary 3.10, Proposition 3.13, the corrected tagged remark, and the general finite local lemma are no longer open. The first-pass specifications are unchanged; all except the unqualified B+ specification now have proofs. The first-pass omission of exact ball-size equality in the infinite four-regular tree is not addressed by this pass's requested list.

## Third pass

### Flaws and qualifications first

**Kostochka remains an explicit literature hypothesis.** Neither B nor B+ is claimed without it. The 1978 proof is absent, and no proof of `Kostochka` was attempted. An axiom audit containing only standard foundational axioms does not discharge an ordinary theorem parameter.

**The overlapping-candidate defect in the manuscript's Haxell remark remains a defect of that argument.** Proving Haxell does not make it applicable to overlapping parts. The second-pass disjoint/tagged constructions and their proved degree bounds remain the valid replacement. The girth-8 version of Lemma 3.9(b) in the older reference also remains incorrect; the proved statement still uses 9.

**The original theorem declarations have not been changed.** In particular, the old `theorem_B` still accepts a Haxell parameter and the old `theorem_B_plus` still accepts its local-lemma, counting, and numerical parameters. The new, stronger corollaries below supply proofs of these propositions. This preserves the user's requirement not to change already-proved statements while exposing results with only Kostochka as a literature assumption.

The unused proposition `TransferMatrixSpanningCorrespondence`, an equality of accepted scalar pattern counts for every length and every nonnegative rational parameter, remains unproved. It is not used by any completed theorem. The needed weighted convolution inequality and the **full original** `TransferMatrixSpanningFamilyBound` are now proved. No restriction to minimal families, no change of bad events, and no weaker replacement of that specification was made.

### Completed targets and exact interfaces

```lean
exp31_transfer_bound : TransferMatrix5710Bound exp31Matrix5710

transfer_spanning_family_bound : TransferMatrixSpanningFamilyBound

haxell : Haxell

theorem_B_of_kostochka (kost : Kostochka)
    (G : SimpleGraph V) (hd : MaxDegreeFour G)
    (hg : GirthAtLeast G 39360) : StrongColourable G 20

theorem_B_plus_of_kostochka (kost : Kostochka)
    (G : SimpleGraph V) (hd : MaxDegreeFour G)
    (hg : GirthAtLeast G 5710) : StrongColourable G 20

theorem_B_plus_statement : TheoremBPlusStatement

infinite_four_tree_edgeBall_card (T : InfiniteFourTree)
    (e : T.graph.edgeSet) (k : ℕ) :
    Nat.card (edgeBall T.graph e k) = 3^(k+2)-3
```

The finite-graph declarations have the usual `{V : Type} [Fintype V]` parameters, omitted from this display. `TheoremBPlusStatement` is the unchanged first-pass specification; its now-unnecessary local-lemma parameter is accepted and ignored. The strongest B+ corollary is in `CompletedTheorems.lean`, and the strengthened B corollary is in `HaxellConsequences.lean`.

### Rational matrix certificate and margin

`CertificateEntries.lean` checks the explicit matrix entries against integer numerators with denominator **5,710,000**. `TransferCertificate.lean` checks the sparse numerator multiplication formula against the original `exp31Matrix5710`, so the certificate is connected to the matrix defined from the supplied program, not to a replacement matrix.

The final certificate uses

```text
rho = 9862789 / 10000000 = 0.9862789
scale = 10000000000
```

`TransferFineCertificate.lean` contains 101 explicit rational vectors for normalized times 0 through 100, followed by an explicit vector `fineVector`. It checks the initial all-ones vector, all 100 componentwise transitions, domination of the last transient vector, and `M * fineVector ≤ rho * fineVector`. The vector is nonnegative and has zero entries at states eliminated by the transient evolution; strict positivity is not needed because domination of the actual orbit has already been checked. Its scaled mass is at most **658.16**. These finite vector and envelope checks use ordinary kernel evaluation (`decide +kernel`); entry identities and final scalar comparisons use `norm_num` and algebraic proof. No native evaluator is trusted.

`TransferFineEstimate.lean` proves the induction connecting these certificates to every matrix iterate. For the scalar envelope `a_k`, with the first 100 masses explicit and the remaining masses bounded by the tail constant, it proves

```text
u_k ≤ rho^k * a_k / scale
Σ(k=0..2854) a_k*a_(2854-k)
  ≤ 123491640037283275676800000000
rho^2854 ≤ 750351 / 10^23.
```

These give a rational upper bound on the original LLL expression of approximately **0.1841539601666061**; the decimal is explanatory only. The kernel proves the original requested upper bound **184154/1000000**, without weakening it. The already-proved logarithm lower bound is **184818/1000000**, leaving the exact certified margin

```text
184818/1000000 - 184154/1000000 = 83/125000 = 0.000664.
```

Thus **g = 5710 and beta = 1203/1000 are unchanged**. There is no need to search for a larger girth. A separate, simpler six-step certificate in `TransferEstimate.lean` already gives `184410/1000000`, which would also fit the budget with margin `51/125000`; the finer certificate discharges the actual printed predicate.

### Embedded spanning-family count

The proof bounds every `ChainBad` family in the second-pass definition, indexed by its edge set. The following parts are all kernel-checked:

1. `SpanningPatterns.lean` extracts a depth pattern from actual nearest projections. Separation gives the spacing inequality, and geometric spanning gives the pending-budget conditions. `TransferAutomaton.lean` constructs a valid labelled state run for every such pattern.
2. `TransferRuns.lean` proves that the total weight of all valid labelled runs of length `n`, with free initial and final states, is exactly `transferMass exp31Matrix5710 n`. This includes summing distinct labels that lead to the same transition.
3. `RootedPatterns.lean` maps a pattern rooted at position `k` and fixed depth into a pair of valid runs, reading its left side in reverse and its right side forwards. The labels recover every position except the fixed root, so this map is injective. Its weighted sum is at most `u_k * u_(n-k)`.
4. `EmbeddingCounts.lean`, `PathCounting.lean`, and `SegmentCounting.lean` count actual graph embeddings. For a fixed root edge and depth `d`, there are at most `2*3^d` possible projection vertices. For each such vertex and fixed position, the number of oriented simple path supports is at most `3*3^n`. Thus the path count is at most `6*3^d*3^n`. Path supports determine their endpoints and walks, so these counts apply to the path objects used in the encoding.
5. At an interior position a depth-`d` projected edge has at most `2*3^d` choices, and at an endpoint at most `3*3^d`. `DecorationCounting.lean` bounds the two endpoint corrections together by 4. This deliberately loose factor still gives a combined coefficient **24**, below the original **27 = (9/4)*12**. `PatternProducts.lean` checks the product identity matching these choices and their powers of `t` to the run weights.
6. `FamilyEncoding.lean` chooses one witness for each family and encodes it by root position, root depth, pattern, path, and projected-edge choices. `codeEdges` recovers the original edge set. The number of nonroot occupied positions equals `|S|-1`, giving the exact rooted weight `t^(|S|-1)`. Multiple possible witnessing paths do not duplicate an event: one witness is chosen, and recovery proves the injection.
7. `EmbeddedFamilyBound.lean` sums the encoding. Uniformly for each root edge, the weighted count is at most **8712 times the convolution**, since `24*(3+9+27+81+243)=8712`. The original coefficient is **9801**. `TransferCounting.lean` then roots at the member of a specified part, uses part injectivity to remove exactly one weight factor, and sums over that part. The result is the original per-part bound with its original `transferContribution5710`.

The counting proof does not need the girth premise once the actual spanning-family witnesses are supplied. Girth is still needed in B+ to produce those witnesses from option-graph cycles. The original counting specification is therefore proved as stated, with no hidden geometric assumption added.

### Haxell and the remaining first-pass target

`Haxell.lean` gives an independent proof by finite lexicographic minimization of augmenting sequences. A configuration contains a partial independent transversal, chosen vertices, and their disjoint blocker sets. Its score first favors larger partial transversals and then smaller successive blocker sets. If a part is missing, degree counting and the lower bound `2*Delta` either permit an extension of the sequence or produce an unblocked vertex. The latter augments the partial transversal or performs an earlier swap that decreases its score. Each possibility contradicts minimality. Surjectivity of the partition also covers `Delta = 0` and empty vertex types without adding a positivity assumption.

The augmenting-sequence presentation was checked against the public mathematical treatment in [Buys, Kang and Ozeki, *Reconfiguration of Independent Transversals*](https://pure.uva.nl/ws/files/307132222/Reconfiguration_of_Independent_Transversals.pdf). The public [IndependentTransversals formalization](https://github.com/Pjotr5/IndependentTransversals/) was inspected for context; no source or package from it was imported. The project proof is in `Haxell.lean` and has no independent-transversal theorem as a parameter.

After the four priority targets were completed, `TreeBallCodes.lean` and `TreeBalls.lean` supplied the missing exact infinite-tree ball count. Recursive nonbacktracking branch codes have cardinality `branchBound n`, with exactly three choices at each step. Acyclicity makes the codes simple paths; a nonempty rooted path in a tree is determined by its last edge. This proves injectivity and disjointness of the two sides of the root edge. A shortest endpoint approach proves that their union is the whole edge ball. The result holds for every natural radius, including zero, on the actual `InfiniteFourTree.Vertex`; no finite truncation is substituted.

The first-pass named specifications are now all inhabited. The documented alternative proof of Theorem B steps 1–3 still cuts every cyclic component and uses Hall counting; the literal odd-cycle-only/Euler/Konig presentation is not separately formalized. The erroneous overlapping-part remark cannot be proved as stated. The unused all-parameter scalar transfer equality and historical counterexample constructions are not claimed.

### Verification and Kostochka assessment

`AxiomAudit.lean` includes the numerical certificates, automaton, convolution, embedding injection, per-part bound, Haxell, both strengthened colouring theorems, and the exact infinite-tree ball theorem. The checked main results use only

```text
[propext, Classical.choice, Quot.sound]
```

No project source uses `sorry`, `admit`, `native_decide`, `sorryAx`, or a new axiom declaration. No package was fetched or installed. **All 57 source modules and the root library were checked offline on 2026-11-06.** The final invocation, including `CompletedTheorems`, both tree-ball modules, `AxiomAudit`, and the root library, finished with **exit code 0**. The complete record is [build-output-third-pass.txt](build-output-third-pass.txt).

This check required resuming after transient reads of existing Mathlib artifacts failed: first at `TransferFineEstimate`, then twice while importing `CompletedTheorems`. Previously completed modules were retained, and checking resumed at each failure. The last four modules and root library succeeded with `-Threads 1`; `build.ps1` now accepts this optional parameter while preserving its previous default thread behavior. No dependency artifact was changed. The original attempt and each continuation are preserved as `build-output-third-pass-first-attempt.txt` and `build-output-third-pass-resume*.txt`, and the combined log records them all. These were import/read failures, not failed mathematical proof obligations. Minor style and deprecation warnings remain.

Proving `Kostochka` would be a separate substantial formalization, not another numerical certificate. Its exact interface quantifies over the maximum-degree bound, girth, and number of colours, uses `q = floor((g+1)/2)`, and concludes a colouring from the stated exponential inequality. The remaining obligation is the combinatorial implication producing that colouring. The two numerical specializations K6 and K5 are already proved and do not supply this implication. With the paper in hand, the first work would be to audit its precise hypotheses and integer conventions against `External.lean`, identify and formalize its central colouring/counting lemmas, and then prove that their estimates imply the displayed criterion. The local lemma and finite counting infrastructure now available may help if the source proof uses them, but that route cannot responsibly be asserted without the text. No attempt to reconstruct the missing 1978 proof, and no reliable effort estimate for it, is claimed.
