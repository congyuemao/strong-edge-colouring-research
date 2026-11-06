# Formalization report

**Reading guide:** the first-pass record below is retained as history. Its
unfinished-item list and missing-source statements are superseded by the
[Second pass](#second-pass), [Third pass](#third-pass),
[Fourth pass](#fourth-pass), [Fifth pass](#fifth-pass), and
[Sixth pass](#sixth-pass) sections below.
The sixth-pass section is the latest status record.

## Flaws and corrections found

1. **ROUTE_Q §1 omits a necessary hypothesis.** A 4-regular graph need not have a 24-regular conflict graph. For `G = K₅`, every edge conflicts with the other nine edges. `AuditExamples.complete_five_conflict_degree` proves both 4-regularity and conflict degree 9. The manuscript §2 correctly adds **girth ≥ 5**. The corrected statement is proved as `L2_degree_eq_twentyFour` in `GirthDegree.lean`.

2. **ROUTE_Q §6.2's displayed formula for an arbitrary degree potential is false.** If `n₀` is the number of isolated vertices in the monochromatic conflict graphs and `p` the number of nontrivial path components, the correct formula is

   `Σ h(d_own) = h(2) Φ₁ + (2h(1) − h(2)) p + h(0) n₀`.

   The printed formula omits `h(0)n₀`. A single isolated vertex with `h ≡ 1` gives left side 1 and printed right side 0; the arithmetic counterexample is kernel checked in `degree_potential_isolate_counterexample`. This does **not** invalidate invariance under a flip: the flip preserves the entire degree multiset, including the isolated-vertex count.

3. **ROUTE_Q §9.3, Lemma 10: the claimed degree-one conclusion is not justified by its stated Φ₁-only argument.** A zero-cost move and the degree-two bound give **at most one**, not equality. There is an abstract counterexample to that general argument: take `K₂₅` minus one edge, partition into five triples and five pairs, with the missing-edge endpoints forming one pair. The monochromatic edge count is 19 and is globally minimal: for any ten classes of sizes `sᵢ`, `Σ binom(sᵢ,2) ≥ Σ(2sᵢ−3) = 20`, and deleting one graph edge reduces this by at most one. A vertex in a triple has own degree 2 and two neighbours in the independent pair, whose own degrees are both **zero**. This is an abstract conflict-graph argument counterexample, **not a verified realization as `L²(G)` for a graph of maximum degree four**, and therefore is not asserted to refute the lemma under all its original geometric assumptions. The Lean theorem `zero_neighbour_degree_le_one` states exactly the implication proved by the exchange argument. Lemma 4.3 also uses odd-cycle minimality; its degree-one conclusion is not contradicted by this example.

4. **Citation mismatch in the task.** The supplied `NEW_DIRECTIONS_zh.md` Proposition 1.1 cites **Haxell's independent-transversal theorem**, not Kostochka. The formal independent-transversal step therefore has a hypothesis `hHaxell : Haxell`. No theorem is silently renamed Kostochka. The full Proposition 1.1 is not claimed below.

## Status and scope

This is a **partial formalization**, not a proof of all the requested targets. All included Lean proofs are checked; unfinished manuscript claims have neither placeholders nor replacement axioms. In particular, **R13, Lemmas 4.3/4.6/4.7/4.8, the full Theorems 4.9/4.11, and the full Proposition 1.1 are not proved here**.

All paths below are relative to this project. Source files are under `Se20Part/`. Main declarations have namespace `Se20Part`; `Partition.*` and `Packing.*` below are nested in that namespace.

| Requested item | Exact result present | File and status |
|---|---|---|
| Section 2 definitions | `L2 G` has vertex type `G.edgeSet`; conflicts use distinct edges with equal or adjacent endpoints **in G**. `MaxDegreeFour G := ∀ v, G.degree v ≤ 4`. | `Definitions.lean`; same forms as the supplied sister-project definitions. |
| Section 2 conflict bound | At most 24 conflicts per edge when `MaxDegreeFour G`; at most 20 on a triangle edge. | `ConflictBounds.lean`, proved. |
| Section 2 exact degree | `FourRegular G → 5 ≤ G.egirth → (L2 G).degree e = 24`. | `GirthDegree.lean`, proved. |
| Lemma 4.1 | Global Φ₁ minimum implies `d_own(x) ≤ d_c(x)` for every class; ten classes and degree ≤24 imply own degree ≤2. Also proved for nine classes. Existence of a global minimum is proved. | `Partitions.lean`, `RouteQ.lean`: `minimum_degreeIn_le`, `minimum_ten_degree_le_two`, `minimum_nine_degree_le_two`, `exists_minimum`, `routeQ_degree_bound`. **Degree assertions proved; the path/cycle component classification is not formalized.** |
| Lemma 4.2 | Own degree 2 at a global minimum gives `3k−1−deg(x) ≤ |Z(x)|`; ten classes and degree ≤24 give ≥5 zero classes. When degree is exactly 24, every class degree lies in 2,…,6, and the five exact profiles are `(z;n₃,n₄,n₅,n₆) = (5;4,0,0,0), (6;2,1,0,0), (7;1,0,1,0), (7;0,2,0,0), (8;0,0,0,1)`. | `RouteQ.lean`, `DegreeProfiles.lean`: `zeroClasses_bound`, `zeroClasses_ten`, `zeroClasses_profiles`, proved. `GirthDegree.lean` supplies degree 24 under the manuscript's hypotheses. |
| Lemma 4.3 | A neighbour in a zero-cost target class has prior class degree ≤1. | `zero_neighbour_degree_le_one`, proved as a **partial result only**. Equality, same-path membership and even vertex count are not proved. |
| Lemma 4.4 | Given a global minimum, distinct source/target classes, own and target degree 2 for `e`, and a target-class neighbour `x` of prior degree 1: `d_k(x) ≥2` for every other class and `d_source(x) ≥3`. No girth assumption is needed. | `RouteQ.lean`: `two_step_conditions`, proved. The degree-one premise is explicit, as supplied by the unformalized Lemma 4.3. |
| Lemma 4.5 | For any graph, `g ≤ G.egirth` and an induced conflict cycle of length `n ≥4` imply **`g ≤ 2*n`**. | `CycleLength.lean`: `induced_cycle_length_bound`, proved **without Cameron**. Forest elimination and chordality are in `ForestL2.lean`, `ChordalFan.lean`. |
| Lemma 4.6 | No full triangle exclusion theorem. | Blocked on odd-cycle/compact-component bookkeeping; see below. |
| Lemma 4.6′ | Nine classes give `2 + (24−deg(x)) ≤ |Z(x)|` when own degree is 2. | `zeroClasses_nine_deficit`, proved. **The geometric conclusion δ≤2 for compact triangles and its triangle-edge corollary are not proved.** |
| Lemma 4.7 | No full diffuse-triangle exclusion theorem. | Blocked; see below. |
| Lemma 4.8 | No even-path closure theorem. | Blocked; see below. |
| Theorem 4.9 | The induced-cycle length bound is available. | **Triangle elimination, and hence the full theorem, are not proved.** |
| Property Q ⇒20 colours | A ten-class partition with degree ≤2 and each induced class 2-colourable gives `StrongColourable G 20`. | `ColourAssembly.lean`: `PropertyQ`, `propertyQ_twenty`, proved. |
| Lovász argument in 4.2 | The weighted global minimum exists. If `degree(x) < Σ_c(d_c+1)`, every own-class degree is ≤its capacity. | `Partitions.lean`: `weightedEnergy_update`, `weighted_minimum_slack_le`, `exists_weighted_minimum`, `lovasz_degree_bound`, `lovasz_partition`. **Proved, not assumed.** |
| Lemma 4.10 | Only the primary weighted exchange inequality is proved. | The bad-component count and incidence-pair tie-breaker are not formalized. |
| Theorem 4.11 | Given an actual `(3⁴,1⁸)` partition whose first four classes have degree ≤3 and are K₄-free and whose final eight are independent, Brooks implies 20 colours. | `ColourAssembly.lean`: `brooks_partition_twenty`, with `hBrooks : Brooks`. **This is the assembly step, not the full no-remote-mark theorem.** |
| Lemma 4.12 | In any finite graph at a global weighted minimum, if distinct classes `p,j` have equal capacities and `y,z` are adjacent in class `p`, then in the two-class graph with `y` deleted, `z` reaches some class-`j` neighbour of `y`. | `MaximumCut.lean`: `monochromatic_edge_reaches_other_class`, proved. It applies to the two capacity-one classes in the manuscript and needs no girth or Brooks hypothesis. |
| Item 5.6, F=E | With the cited Joos/Nguyen hypothesis, no isolated vertices and no `C₅[2]` component, `|E(G)| ≤18 ν_s(E(G))`. | `Packing.lean`: `full_edge_eighteen_of_joos`. **Only this explicitly restricted case is present.** Isolated-vertex removal and addition of tight components are not formalized. |
| Item 5.6, ν≤1 and tightness | No full result. | The ν≤1 case uses the ≥19 strong-clique classification 5.5, whose finite certificate is outside this development. The 18-edge tight example is not formalized here. |
| Item 5.7 | With the actual `C₅[2]` component correction, `|F| ≤18ν_s^G(F)+τ_G(F)` implies `|F| ≤19ν_s^G(F)+t_G(F)`. | `Packing.lean`, `TightComponents.lean`: `packing18_implies19`, proved. |
| R13 / G05 | No ≤41-edge colouring theorem and no ≥42 critical-size theorem. | Missing proof chain; see below. |
| G09 triangle reducibility | A colouring of `F\T`, where all edges of `T⊆F` lie on ambient triangles, implies a colouring of `F`; a 21-critical edge set has no triangle edge. One triangle edge can be inserted while recolouring at most one previously coloured edge. | `Triangle.lean`, `TriangleInsertion.lean`, `Critical.lean`: `triangle_insertion`, `triangle_reducibility`, `critical21_no_triangle`, proved. **This does not claim extension while fixing every outside colour.** |
| Critical minimum degree | Every member of a 21-critical edge set has ≥20 neighbours within that set, with conflicts still evaluated in G. | `Critical.lean`: `critical21_min_degree`, proved. |
| Matching auxiliary bound | A matching in a maximum-degree-four graph has at most six ambient conflicts per edge and is strongly 7-colourable. | `Greedy.lean`: `matching_conflicts_le_six`, `matching_seven_colourable`, proved. This is auxiliary, not a replacement for a requested reducibility theorem. |
| Section 6.3 A02/A03/A04/A06 | None of these full colouring theorems is proved. | Missing proof text/definitions and critical/list-colouring machinery; see below. |
| Proposition 1.1 | Girth ≥96 gives an independent representative from each of any supplied disjoint induced conflict cycles of length ≥4, under `Haxell`. Separately, an independent defect set whose deletion makes each of nine classes bipartite gives 19 colours. | `Transversal.lean`, `ColourAssembly.lean`: `long_cycles_independent_transversal`, `nine_classes_one_defect`. **Cycle-family construction and the residual bipartiteness argument are missing, so this is not the full proposition.** |
| Local-injection pull-back | For a locally injective graph homomorphism `f : G →g H`, every strong k-colouring of H pulls back to one of G. Neither graph needs maximum degree four or finiteness. | `LocalInjection.lean`: `LocallyInjective`, `L2LocalMap`, `strongColourable_pullback`, proved. |

## Definitions and proof boundaries

`Partition.energy` is **twice** the number of monochromatic unordered conflict pairs. Its exact one-vertex change is `2*(d_target−d_source)`. `weightedEnergy` is twice Ψ. Both are integer valued; no truncated subtraction is used in exchange arguments. `degreeIn` is integer valued and is proved equal to the cardinality of the relevant neighbour set. Minima quantify over **all** partitions and are proved to exist by finite minimization.

`InducedCycle` explicitly records distinct vertices, consecutive adjacency, the closing edge and absence of other chords. `induced_cycle_length_bound` bounds the finite endpoint union by `2*n`, restricts G to it, proves it cannot be a forest using a simplicial elimination rank, and extracts a genuine cycle of length at most that endpoint count. `egirth` takes value infinity on forests. The result `g ≤2*n` expresses the rational half-length claim without introducing a weaker rounded natural-number division.

`packingRank H F` is the maximum size of a pairwise nonadjacent subset of F, implemented as a finite supremum over its powerset. Thus `packingRank (L2 G) F` uses **ambient** induced matchings. `PentagonDouble` is the graph on `Fin 5 × Fin 2` with adjacency inherited from the five-cycle on the first coordinate. Its 20-edge count is checked by kernel evaluation. `tightBlocks G` consists of the edge sets of those connected components of G whose induced graphs are isomorphic to `PentagonDouble`. The component edge sets are proved disjoint and mutually nonconflicting. `tauG` sums `max(0,|F∩block|−18)`; `fullTightCount` counts intersections of size 20, equivalently full tight components. The proof of 5.7 chooses one edge in each block with an intersection of size >18 and proves `τ≤ν+t`.

`Critical21 G F` means the induced ambient conflict graph on F is 21-colourable, is not 20-colourable, and becomes 20-colourable after deleting any member of F. This is not a claim that a critical set exists.

The only external mathematical hypotheses actually used in results are ordinary definitions of propositions:

- `Brooks`: for finite H and `k≥3`, maximum degree ≤k and no `(k+1)`-clique imply k-colourability. Used only by `brooks_partition_twenty`.
- `JoosNguyen`: a finite graph of maximum degree four, with no isolated vertices and no `C₅[2]` component, has `|V|≤9ν_s(E)`. Used only by `full_edge_eighteen_of_joos`.
- `Haxell`: finite disjoint nonempty vertex parts of size at least `2Δ` in a graph of maximum degree ≤Δ admit an independent transversal. Used only by `long_cycles_independent_transversal`.

There is **no Cameron hypothesis**, **no Lovász partition hypothesis**, and no imported hypothesis masquerading as a proved instance of R13 or one of the unfinished manuscript lemmas. Absence of Brooks/Haxell/JoosNguyen from `#print axioms` does **not** prove those statements: they are theorem arguments.

## Precise outstanding work

- **4.1 component classification; 4.3 and 4.8:** formalize the path/cycle decomposition of a finite graph of maximum degree two, the parity of the path left by deleting a cycle vertex, and the count of odd-cycle components under a zero-cost recolouring. `minimum_update` is proved, but no formal Φ₂ implementation or conservation theorem is supplied. For 4.8 one must additionally show that deleting an internal path vertex separates the two endpoints and that an open closure introduces no replacement odd cycle, including the case of moving into the original class.
- **4.6 and 4.6′:** after the previous work, formalize the three-edge compact-support classification, the existence of a pivot incident with both other edges, preservation/minimality of the compact-component count, and the injection from zero classes into the four remaining hub edges. Only the numerical zero-class lower bounds are currently proved.
- **4.7:** formalize the girth-seven diffuse-triangle geometry and the complete five-coordinate potential, including the relative comparison between the original minimum and a second move from a state which need not minimize the last three coordinates. The linked-K₂ count changes in cases A and B cannot be replaced by assuming each intermediate state is fully minimal.
- **4.9:** depends on those triangle exclusions. The cycle length half-bound is fully available.
- **4.10 and full 4.11:** implement the bad-component count and the monochromatic incident-edge-pair tie-breaker; prove what a tight move creates, then the hub-count inequality and the girth-seven exclusion of a matching triangle. The final Brooks/palette assembly is already proved with these structural conditions explicit.
- **5.6:** the full-edge case still needs removal of isolates and additive decomposition across tight components. The `ν≤1` case cannot be claimed without the strong-clique classification used in 5.5; no finite classification certificate was imported.
- **R13/G05:** the supplied references name but do not include `research/critical_size_continuation.md`, `critical_complement_connectivity.md`, `dense_complement41.md`, and `critical41_triangles.md`. A summary-table assertion does not supply the critical-size proof. No substitute theorem of the form “assume R13, therefore R13” was added.
- **Other older structural/reducibility results:** G06/G08, G10–G12, G13 (K₃,₃ and its 100 boundary checks), G14 (Petersen interface), and G16 (which itself uses the computational G15 Petersen-minus-edge theorem) are not proved. The referenced proof files are absent. G07 and G15 explicitly depend on finite computation and were not imported. The specialized F/S statements in §6.2 and RESULTS.md are likewise not formalized; the absent linked proofs are needed to recover their exact interface hypotheses and permitted recolourings.
- **6.3:** A02 needs the exact private-low-clique/unique-high condition from `private_clique_colour.md`; A03 needs `high_clique_low_clique_free.md`; A04 needs `five_critical_two_adjacent_general.md`; A06 needs the definition of incidence weights and the theorem in `weighted_nae_three.md`. The one-line summaries are insufficient to reconstruct A02/A06 unambiguously. A03/A04 have clear summary statements but their critical/list-colouring proofs are not supplied and were not rebuilt here. None was assumed as an external citation.
- **Proposition 1.1:** construct the disjoint odd-cycle components of the nine induced classes from degree ≤2, show they are induced cycles of the ambient conflict graph, and prove that selecting one vertex in each leaves each class bipartite. The 96→48 bound, independent-transversal application and final 19-colour assembly are already present. No Kostochka substitute was inserted for the Haxell citation actually used in the text.

The missing `research/` directory was requested during the run. Searches of the supplied project, the local Lean tree and the obvious `se20-data` locations did not find these linked proof files. This report does not interpret “proof” in the registration table as an axiom or a completed formal proof.

## Build, provenance and audit

Run `./build.ps1` from this directory. The script contains the complete module list and supports `-Only ModuleA,ModuleB` for a dependency-already-built development check. The full build checks the root `Se20Part.lean` after all modules.

The supplied script initially invoked `lake env`, which attempted to materialize/fetch `plausible`; the network connection failed and **nothing was fetched**. That behaviour has been removed. The current script calls the already installed Lean 4.35.0-rc4 executable on E: directly, sets `LEAN_PATH` to existing local dependency oleans plus this project's build directory, and never invokes Lake or elan. TEMP/TMP/cache are on E:. No installation was performed on C: or elsewhere. Other projects were only read, never edited.

`Definitions.lean` uses the supplied `reference/Definitions.insertion.lean` forms. `GraphBasics`, `ForestL2`, `ChordalFan`, `ConflictBounds`, `Kempe`, `Triangle`, `TriangleInsertion` and `Greedy` were copied/adapted from `E:/lean/se20-insertion/Se20Insertion/` into this namespace. `Recolour` extracts the independent-set recolouring definition from `Insertion.lean`; `Counting` extracts the finite-union equality and saturation arguments from `Counting.lean`. The small no-triangle/no-square part of `GirthDegree` adapts `GirthGeometry.lean` with the sufficient girth-five hypothesis. All such code is now local and compiled in this project; there are no imports of the sister project. The remaining modules were written here.

All main results are listed in `AxiomAudit.lean`. The complete build output is saved in `BUILD_LOG.txt`. The exact axiom output is appended below after the final build. A source scan checks for proof placeholders, new axiom declarations, `native_decide`, and cross-project imports.

Full build: **PASS**, exit code 0. All 25 project modules plus the root import were checked (26 source files). The 52 audited declarations use only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx` or evaluation oracle appears. Harmless linter/deprecation warnings remain in the log.

```text
'Se20Part.strongColourable_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.card_conflicts_le_twentyFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.card_conflicts_triangle_le_twenty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.L2_degree_eq_twentyFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.forest_L2_eliminates' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.forest_L2_chordal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.induced_cycle_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.energy_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.minimum_degreeIn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.exists_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.minimum_ten_degree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.minimum_nine_degree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.minimum_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.weightedEnergy_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.weighted_minimum_slack_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.exists_weighted_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.lovasz_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.lovasz_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.routeQ_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.zeroClasses_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.zeroClasses_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.zeroClasses_nine_deficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.zeroClasses_profiles' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.zero_neighbour_degree_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.two_step_conditions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Partition.monochromatic_edge_reaches_other_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.colourable_of_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.propertyQ_twenty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.brooksPalette_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.brooks_partition_twenty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.nine_classes_one_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.long_cycles_independent_transversal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Packing.tau_le_rank_add_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.Packing.eighteen_implies_nineteen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.pentagonDouble_twenty_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.componentEdges_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.componentEdges_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.packing18_implies19' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.full_edge_eighteen_of_joos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.triangle_local_repair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.triangle_insertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.triangle_edges_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.triangle_reducibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.critical21_no_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.critical21_min_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.matching_conflicts_le_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.matching_seven_colourable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.L2LocalMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.strongColourable_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.L2_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.complete_five_conflict_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Part.degree_potential_isolate_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Second pass

### Flaws, repairs and scope corrections first

1. **Lemma 4.10's proof, step 2, is too restrictive when the target capacity
   is two.** A tight move can produce an odd cycle longer than a triangle;
   its new bad component need not be `{x} ∪ N_j(x)` or a clique. This is a
   gap in that proof sentence, not a counterexample to the inequality.
   `weighted_component_hub_monotone` repairs the argument: it injects all
   new bad components avoiding the moved vertex into old bad components
   avoiding it, and accounts for at most one new bad component through the
   vertex. The actual bad-component potential includes capacity-two odd
   cycles. The repaired theorem does not assume that the new component is
   complete.
2. **The degree-one gap identified in the first pass is now repaired.**
   `zero_class_neighbour_degree_one` derives equality from the full even
   path and odd-component minimum. The earlier, weaker Φ₁-only theorem was
   retained unchanged.
3. **Appendix E's qualifications are substantive.** G12's minimality must
   range over all finite graphs of maximum degree four; it cannot silently
   mean minimality only among four-regular graphs. The definition of
   three-vertex-connectivity also needs at least four vertices. G13's 100
   boundary experiments are supplementary, not premises of its paper proof.
   G16 needs the no-triangle/no-square assumption and the G15 list theorem.
   The F09 endpoint lemma explicitly assumes the two paths are vertex
   disjoint. These qualifications were retained when assessing the targets.
4. **Independence and colouring are kept separate.** The registered G06
   statement (an independent triple in every 41-edge set) is proved below.
   The source also proves 20-colourability of every edge set of independence
   number at most two. That stronger colouring assertion is not inferred
   merely from the independent-triple bound and is still unfinished here.
5. **The supplied sources are now available and were read.** The old
   report's “missing research files” explanation no longer applies. The
   outstanding items below identify missing formal arguments, not missing
   files. No external-source statement has been promoted to a Lean axiom.

### Completed second-pass results

All declarations below are in namespace `Se20Part`, with the displayed
subnamespace where applicable. All conflicts use the unchanged ambient
graph `G`. Previous proved statements have not been changed.

| Target | Exact new result and principal files |
|---|---|
| Finite degree-two decomposition, parity, 4.1 | `exists_pathCycleOrder` and `component_pathCycleOrder` give an actual vertex ordering of each component as a path or a cycle, including isolated vertices and single edges. `PathCycleOrder.colourable_iff` identifies the bipartite cases. `deleteCycleIso`, `odd_cycle_deletion_even` and `deleteCycleIso_endpoints` give the path, even cardinality and endpoints after deleting a vertex of an odd cycle. `Partition.minimum_ten_components` and `minimum_nine_components` apply this to the two partition sizes. `DegreeTwo.lean`. |
| Formal Φ₂ | `Partition.phi2` counts non-bipartite monochromatic connected components once each. At degree at most two these are exactly odd cycles. `MinimumTwo` quantifies over all primary minima, and `exists_minimumTwo` proves existence. `DegreeTwo.lean`, `ComponentExchange.lean`. |
| 4.3 | `Partition.zero_class_even_path` returns `EvenPathClosure`: an injectively indexed induced even path, a whole target-class component, whose two ends are exactly the moved edge's target-class neighbours. `zero_class_neighbour_degree_one` supplies their degree-one conclusion explicitly. `ComponentExchange.lean`, `PathEndpointDegree.lean`. |
| 4.8 | `Partition.internal_zero_class_even_path` proves closure at every internal path vertex, including a move into the original class. The comparison uses component counts and does not assume that an arbitrary intermediate partition minimizes later coordinates. `EvenPathExchange.lean`. |
| NEW_DIRECTIONS Proposition 1.1 | `proposition_one_one` proves 19-colourability from a nine-class degree-two partition with no monochromatic triangle, maximum original degree four, girth at least 96 and `hHaxell : Haxell`. It constructs the disjoint odd-cycle family, obtains representatives, and proves the residual classes bipartite. `degreeTwo_residual_colourable` allows additional deletions as well. `Residual.lean`. |
| 4.6 | `no_compact_triangles_ten` proves that a global `(Φ₁, Φ₂, compact-triangle count)` minimum has no compact triangle. Maximum degree four suffices. The proof includes compact-support geometry, a pivot meeting the other two edges, preservation of the first two minima, replacement of the destroyed compact triangle, and the injection of zero classes into at most four available hubs. `CompactExchange.lean`, `CompactGeometry.lean`, `CompactTriangles.lean`. |
| 4.6′ | `compact_pivot_deficit_nine` proves `24 − degree_L2(e) ≤ 2` for every compact-triangle pivot in a nine-class three-coordinate minimum. No geometric replacement premise is assumed. `CompactTriangles.lean`. |
| 4.10 | `Partition.weighted_component_hub_monotone` proves `h_own(x) ≤ h_j(x)` at a tight target class from the actual three-coordinate weighted minimum. `WeightedBadComponent` and `weightedPhi2` use non-colourability at the class capacity, so capacity two is included. The first potential and the incident-pair tie-breaker are represented by twice their manuscript values; this preserves both order and exact differences. Existence is `exists_weightedComponentMinimumThree`. `WeightedComponents.lean`. The earlier clique-only development in `WeightedExchange.lean` is retained as a separate theorem, not substituted for this full result. |
| 4.11 | `component_minimum_conditional_twenty` proves the full no-remote-mark implication for the `(3⁴,1⁸)` minimum, girth at least seven and maximum degree four, with `hBrooks : Brooks`. Tight-class counting forces every bad clique to have zero same-class hub degree. `no_matching_clique_three` rules out a three-edge matching clique by restricting to at most six endpoints and using the forest proof. Thus the three-colour classes have no K₄, and absence of remote marks makes the one-colour classes independent. `WeightedHubs.lean`, `MatchingTriangle.lean`, `ComponentConditional.lean`. |
| 5.6, full edge set | `full_edge_packing_eighteen` proves the inequality for every finite maximum-degree-four graph, including isolates and tight components. Its exact cited premise is `hJoos : JoosVertexBound`, containing both correction terms in equation (5.1). `edge_bound_remove_isolates` and `tauG_univ` supply the remaining argument. `PackingCases.lean`. |
| 5.6, rank at most one | `packing_eighteen_rank_le_one` proves the assertion with the explicit hypothesis `h55 : StrongCliqueClassification55`. Rank zero, the clique characterization of rank at most one, and the small-set case are proved independently of 5.5. `PackingCases.lean`. |
| 5.6, all stated equality examples | `nineCirculant_tight` proves 18 edges, rank one and correction zero for C₉(1,3). `tight_component_subset_equality` covers every 19- or 20-edge subset of a C₅[2] component (and also 18-edge subsets). `circulant_component_equality` transfers the other example to an actual ambient component. `packingRank_union`, `tauG_union` and `packing_equality_biUnion` prove additivity and equality for arbitrary finite disjoint unions of these components. `PackingTightness.lean`, `PackingAdditivity.lean`, `PackingEqualityComponents.lean`. |
| G06 | `fortyOne_edges_independent_triple`: every ambient edge set of size at least 41 contains an independent subset of size exactly three. `rank_two_card_le_forty` is the equivalent packing-size consequence. This follows from the locally rebuilt unconditional 20-packing proof, not an assumed critical-size theorem. `LegacyBridge.lean`. |
| G08 | `high24_clique_seven`: a strong clique all of whose edges have ambient conflict degree exactly 24 has size at most seven. The copied old helper only bounded thirteen; the new joint branch/opposite-star argument proves the requested seven. No global girth condition is added. `High24Seven.lean`. |
| G09 | The first-pass `critical21_no_triangle` and `triangle_reducibility` are retained and included in the new build and audit. |
| F01 | `GirthClique.girth_clique_seven` proves the seven-edge bound under girth at least five. `girth_degreeTwo_clique_five` proves the five-edge bound when the selected edges have original degree at most two. `DegreeTwoEdgeSet` counts selected incident edges, not degree in the induced graph on their endpoints. Witness edges outside the selected set remain available. `GirthCliques.lean`, `DegreeTwoCliques.lean`, `F01.lean`. |
| F09, endpoints, forbidden shapes and independence | `GirthFive.disjoint_two_paths_centres_of_clique` proves endpoint lemma 1.1 with all six vertices distinct. `path_edge_attachment`, the two uniqueness lemmas, and the three A/B interaction lemmas prove 1.2 and its stated consequences. `no_five_edge_path_clique`, `no_three_two_paths_clique` and `no_path_three_edges_clique` exclude all three forbidden forest shapes. The last uses 64 explicit, kernel-checked orientation cases and the proved A/B lemmas. `commonExtensions_independent` proves the full independence assertion for common extensions of any four-edge strong clique. The full shape-isomorphism list and extension-count bounds are not claimed. `F09Endpoints.lean`. |
| S18, complete finite triple classification | `ThirteenKernel` is the explicit thirteen-vertex graph from `joint_thirteen_obstruction.md`, with four degree-five and nine degree-four vertices. `thirteenKernel_independent_card_le_three` and `thirteenKernel_triple_counts` prove independence number three and exactly 56 triples, split 8/32/16. `thirteenKernel_triple_normal_form_of_type` supplies an actual graph automorphism mapping the stated representative of each type to every triple of that type. `thirteenKernel_representatives_distinct` distinguishes the three orbits by their numbers of degree-five vertices. The 56 permutation witnesses, adjacency preservation, bijectivity and complete coverage are kernel checked. The subsequent potential-preserving rotations are not asserted. `ThirteenKernel.lean`. |

The G06 bridge copies 42 dependency modules from the existing local
`E:/lean/sep19/upstream/packing195/lean/StrongEdge` tree into
`Se20Part/Legacy`, with all namespaces/imports made project-local.
`LEGACY_PROVENANCE.json` records original paths and SHA-256 hashes;
`LEGACY_MODULES.txt` records build order. No upstream project was modified.
`legacy_conflictGraph_eq` proves that the copied line-graph-square
definition is exactly this project's endpoint definition. The copied
20-packing theorem is recompiled locally and its dependencies are included
in the audit of `ambient_packing_twenty`.

The new girth clique proofs adapt that local rigidity proof by replacing
degree-24 rigidity with proved no-triangle/no-square lemmas. The degree-two
selected-edge improvement is new local code. The generation scripts only
produce ordinary Lean source; they are not proof or evaluation oracles.

### Exact remaining obstructions, in the requested order

These are unfinished formalizations, not claims that the supplied paper
theorems are false or impossible to formalize.

1. **4.7, hence full 4.9.** Compact triangles and matching triangles are now
   excluded by proved lemmas, but the remaining diffuse configuration
   `α=pa, β=pb, γ=cd` needs the complete five-coordinate comparison, including
   the count of linked K₂ *components*. The unresolved step is to prove the
   zero-slack hub saturation of ROUTE_Q §6.5 and the relative comparison in
   §7.2 case B after the first move raises the compact-triangle count. The
   second move must be compared to the original minimum, not treated as a
   move from another five-coordinate minimum. The new component exchange
   proves preservation of the first two coordinates, but does not supply
   the linked-K₂ count changes `+1`, then at least `+1−1`. Thus no full 4.7
   or 4.9 theorem is claimed. The cycle-length half-bound remains fully
   proved without Cameron.
2. **G12.** `critical21_endpoint_degree` now proves that every endpoint of
   a critical edge has original degree at least three. The requested global
   three-vertex-connectivity and cut statements still need formal gluing of
   side colourings by a palette permutation: the non-star three-edge and
   bounded-multiplicity four-edge cut interfaces in
   `global_continuation.md`, plus the five matching-cut interface in
   `cut5_matching.md`. The latter's exceptional high-forbidden-row case
   needs the constrained choice of prescribed source/target colours before
   the remaining Hall matching. No hypothesis asserting G12 was introduced.
3. **G05 / R13 and the extra rank-two colouring clause.** The source chain
   is now known, including the previously omitted `critical25.md`.
   `CriticalSizeChecks.lean` kernel-checks the scalar contradictions for
   `26≤n≤40`, `0≤a≤12`, the three residual nontrivial odd-block cases, the
   all-singleton common-neighbour count, and the five-bag size patterns.
   These checks do not supply their graph-theoretic premises. The missing
   main infrastructure is the maximum-matching D/A/C decomposition with
   factor-critical odd blocks and its application to a critical complement;
   the small-saving cases for orders at most 25 and the structural five-bag
   classification at order 41 also remain. G08 is now available for the
   final degree-24 clique contradictions. No “assume R13” substitute and no
   unverified finite certificate were inserted.
4. **A03.** The obstacle is the formal degree-list block classification of
   the low-vertex graph and the one-step leaf-block extension argument.
   It must yield a complete block or an odd cycle, preserve the current
   degree information, and turn Hall failure into the forbidden K_k. The
   source explicitly warns against repeatedly deleting leaves while keeping
   old degree hypotheses. This machinery is not supplied by the new
   degree-two component theorem.
5. **A04.** In addition to that same low-block interface, its eight-port
   argument needs classification of the two surviving leaf-block chains,
   including the central K₄ case, and list extensions with the fixed colours
   of the two adjacent high vertices. Parity of the number of high vertices
   is insufficient by itself. The nonadjacent-high-vertex case is not being
   substituted for the stated theorem.
6. **A02.** The two graph transformations have not been formalized: deleting
   a private clique and identifying the nonadjacent high/low pair, or
   deleting it and adding a bridge between two low components. The proof
   must preserve *every other* private clique, unique high neighbour and
   exclusion of K_{k+1}, while strictly reducing the high-vertex count. The
   assumptions `k≥4` and unique high neighbour are retained.
7. **A06.** A formal incidence-weighted hypergraph interface and the
   representative-edge exchange are still missing. The key argument must
   handle repeated representative pairs, reduce odd representative cycles
   without creating new ones, and combine this with the weighted
   pseudoforest and two-part potential. The ordinary graph path/cycle result
   now supplies parity, but not these hypergraph transformations.
8. **G13.** The fixed-outside-colour extension still needs the six-spoke
   list accounting and the nine-edge core Hall argument, including repair
   of the common eight-colour failure by two independent spokes. The 100
   experimental boundary checks are not used as a replacement.
9. **G14.** The small-colour-pool reduction and the list-merging/Hall proofs
   for K_{3×3}, K_{3×4}, K_{3×5} have not been formalized. The mapping from
   the Petersen endpoint model and the boundary-list counts must then be
   connected to a fixed ambient partial colouring.
10. **G16.** The missing geometric step is extraction of the unique
    witnesses and opposite four-cycle orientations from two matching K₄s
    sharing a triangle, followed by identification of the induced Petersen
    or Petersen-minus-edge block. `PetersenMinusListTheoremG15` is now an
    explicit named hypothesis with the exact arbitrary-list 5/7/8 statement
    on the labelled 14-vertex graph from the source. Its degree sequence and
    74-edge count are kernel checked. The coefficient 12240 and the list
    theorem are **not** asserted proved. The G14 interface and the G15
    boundary extension are still needed before this can prove G16.
11. **F03.** The critical-complement decomposition required by G05 is also
    needed here. The `k=10,11`, `c=2,…,5` numerical contradiction is checked
    in `factor_component_obstruction`; the factor-critical order-19
    decomposition and its odd-block incidence inequalities remain. F01 now
    supplies the exact clique bound for the intended edge-set application.
12. **F09 and S.** F09's two disjoint two-edge-path centre lemma, A/B
    attachment alternatives, uniqueness and pair interactions are now proved,
    as are all three forbidden forest-shape exclusions and independence of all
    common extensions. What remains is assembling the degree-two component
    orders and the five-edge count into the complete shape-isomorphism list,
    proving the matching-four endpoint orientation model, and the
    shape-by-shape counts proving at most three extensions. The exclusions
    alone are not substituted for that full classification. S18's finite
    independent-triple classification, including all three automorphism
    orbits and the 8/32/16 counts, is proved. Its one- and two-step rotations
    still need the minimum-potential interface and preservation of the other
    designated bad cycles. No full S-group theorem was completed. In
    particular, the finite O₉/blocked-component
    identifications and synchronous list repairs cannot be inferred from
    a single movable representative or from the new degree-two decomposition.

### Hypotheses and validation

The only newly added named source-theorem hypothesis definitions are:

- `JoosVertexBound`, the full quoted equation (5.1), used by
  `full_edge_packing_eighteen`. The earlier restricted `JoosNguyen` definition
  and theorem are unchanged.
- `StrongCliqueClassification55`, the exact containment of a strong clique
  of at least 19 edges in a C₅[2] component, used by the rank-at-most-one case.
- `PetersenMinusListTheoremG15`, the labelled arbitrary-list theorem reserved
  for G16. No theorem in this pass claims to prove or instantiate it.

`Brooks` and `Haxell` remain explicit theorem arguments. There is no Cameron
or Lovász hypothesis. The small circulant, Petersen-minus degree/count
checks and numerical case splits use kernel reduction or proof-producing
arithmetic tactics, never `native_decide`.

`AxiomAudit.lean` includes the new principal declarations. `build.ps1`
contains the complete dependency order, including the local legacy modules,
and builds the root import. It invokes the installed compiler directly,
with one worker, a 64 MiB thread stack and no network/package-manager call. Windows runtime
import/memory failures receive at most three visible retries; actual proof
errors are never retried or ignored. Such transient import failures and one
`std::bad_alloc` occurred during development; later checks of those modules
succeeded. The first final-build attempt exposed a stack overflow in the
unchanged `Triangle.lean`; increasing the compiler thread stack resolved it
without changing any theorem or proof in that file.

**Final validation passed.** The full project build exited with code 0.
After the final S18 additions, the targeted command
`./build.ps1 -Only ThirteenKernel,AxiomAudit -CheckRoot` also exited with
code 0, recompiling that source, the complete audit and the root import.
Together these checks cover all **95 source modules plus the root import**;
the final build manifest contains every source module exactly once.
`-CheckRoot` also permits checking the root after a selected-module build;
the default full build continues to check it automatically.

All **136** `#print axioms` declarations produced results. Their combined
axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`; individual
declarations use subsets of that set. The complete output is in
[SECOND_PASS_AXIOM_OUTPUT.txt](SECOND_PASS_AXIOM_OUTPUT.txt), with compiler
logs in [SECOND_PASS_BUILD_LOG.txt](SECOND_PASS_BUILD_LOG.txt) and
[SECOND_PASS_FINAL_AUDIT_LOG.txt](SECOND_PASS_FINAL_AUDIT_LOG.txt).
The final source scan found no `sorry`, `admit`, `native_decide`, new axiom
declarations or unsafe declarations. All 42 copied modules also match the
recorded source hashes and exact namespace/import transformation.

These successful checks certify the declarations listed above, not the
unfinished targets in the obstruction list. In particular, neither the
full 4.9 theorem nor the 42-edge critical-size lower bound is claimed.

## Third pass

### Flaws and proof boundaries first

The first two passes above are retained as historical records. The statements
below supersede their remaining-obstruction entries only where explicitly stated.

No new counterexample to Lemma 4.7 was found. Its delicate point is genuine:
the intermediate partition in case B does not minimize the last three
coordinates. The new proof compares the second move with the original
minimum. It counts **whole linked K₂ components**, not all linked
monochromatic pairs. Their closure condition is part of `typedPairs`.

The G05 finite-check interfaces introduced in this pass are **unverified
hypotheses**, not successful computations. They concern arbitrary labelled
abstract graphs, not samples of original maximum-degree-four graphs.
No instance of an unexecuted check is asserted, and no resulting conditional
theorem should be described as an unconditional proof of G05.

### Completed proofs

* **Lemma 4.7:** `no_diffuse_triangles_ten` proves the diffuse-triangle
  exclusion for the actual five-coordinate global minimum. The result holds
  for maximum degree four, hence includes the stated four-regular case.
  `TrianglePotentials.lean` proves existence of the minimum, exact changes
  of both triangle counts and the linked-component count, and the relative
  two-flip comparison. `DiffuseGeometry.lean` constructs the actual common
  connector using the girth hypothesis. `DiffuseSaturation.lean` proves the
  five zero classes, coverage of every available hub, and injectivity of
  their colours. `DiffuseTriangles.lean` completes both cases.
* **Theorem 4.9:** `routeQ_reduction` and `exists_routeQ_reduction` give a
  complete path/cycle ordering of every non-bipartite monochromatic
  component, prove that it is an odd cycle of length at least five, and
  prove the exact unrounded inequality `g ≤ 2 * length`. Existence of the
  optimizing partition and its degree-two bound are included. No Cameron
  hypothesis or long-cycle-elimination claim is used.

### Validation record

The five Route Q modules have each compiled with the installed compiler.
The final combined build and audit record is appended below after the
remaining work of this pass.

### Recovery after the 11:07 memory failure

The existing short Third pass section above was present on disk when the
run resumed. It was a checkpoint, not a final validation report. The old
`THIRD_PASS_BUILD_LOG.txt` stops at `RouteReduction`; it does not establish
a successful full build. Some development logs contain earlier proof
errors or import failures even though their sources were subsequently
fixed. The recovery checks use separate logs and leave that evidence intact.

All five previously unlisted modules, `PaletteExtension`, `SmallColourPool`,
`MultipartiteLists`, `MultipartiteFour`, and `MultipartiteFive`, compiled
successfully in one serial recovery run. In particular, the final
`five_parts_eight_choosable` proof was complete: the old log recorded import
failures, not a mathematical failure of its Hall repair. All five are now
registered in `build.ps1` and imported and audited by `AxiomAudit.lean`.

Further checked results from the resumed work:

* `ListBlockExtension.lean`: `list_block_extension` and its isomorphism
  version extend an arbitrary fixed outside partial colouring whenever
  the actual induced block is list-colourable with the stated degree
  budgets. They preserve every outside colour. The graph has not been
  replaced by an edge-deleted ambient graph.
* `threePart_five_block_extension` proves the full eight-list extension
  interface for an induced `K_{3×5}` block in a graph of maximum degree 24.
  `petersenMinus_block_extension` proves the corresponding variable-list
  interface with the explicit argument `hG15 : PetersenMinusListTheoremG15`.
* `PetersenKernel.lean` constructs the ten two-subsets of a five-element
  set and their fifteen edges, proves cubicity, and identifies the actual
  conflict graph with `K_{3×5}`. The checks cover the fifteen edge labels,
  their injectivity, all 225 ordered edge pairs, and the ten vertex
  degrees using kernel reduction. `petersen_eight_choosable` applies to
  arbitrary lists, not only lists arising from an outside colouring.
* `PetersenExtension.lean`: `induced_petersen_extension` extends every
  partial colouring outside an induced Petersen block to all its internal
  edges for any ambient graph of maximum degree four, without a girth
  assumption. `critical21_disjoint_induced_petersen` proves that no internal
  edge of such a block belongs to a 21-critical edge set. The stronger
  assertion excluding a Petersen block from the entire support also
  requires treating the case in which none of its internal edges belongs
  to that edge set; that additional conclusion is not implicit here.

The resumed build uses `-j1` and a 6000 MiB Lean allocation limit. A named
mutex serializes this project's builds; a process check before each compiler
invocation refuses to start while any other `lean` process is present.
An unrelated `fourth_pass/FrozenBench.lean` job was observed and was not
terminated. Compiler checks resumed after it exited. A later overlapping
job was detected by the guard and no second compiler was started.

The final manifest, audit, conditional assumptions, and outstanding targets
are recorded below after the final serial validation.

### Additional third-pass results and exact hypotheses

The interrupted run also completed the following registered results, which
were absent from its short report checkpoint:

| Target | Exact proved result |
|---|---|
| G02 | `strong_clique_twenty`, `twenty_clique_closed`, and `twenty_clique_rigidity` in `CliqueTwenty.lean`. Equality gives five disjoint pairs with exact ambient neighbour sets, hence the whole isolated `C₅[2]` component. `critical21_clique_nineteen` excludes a 20-clique from a critical edge set. These are unconditional. |
| Critical extraction | `exists_critical21` extracts a 21-critical subset from any non-20-colourable edge set while retaining the ambient graph. |
| G05 | `critical21_no_abstract_obstruction` is unconditional. `critical21_fortyTwo_of_finite_checks` and `small_edge_set_twenty_of_finite_checks` require the three checks below. `rank_two_twenty_of_finite_checks` gives the independence-number-at-most-two colouring assertion using only the first two checks and the already proved 40-edge packing bound. |
| G12 palette steps | `palette_equiv_of_no_rectangle`, `palette_equiv_of_budgets`, `palette_cut_three`, `palette_cut_four`, `palette_cut_five`, and `palette_special_four` in `PaletteHall.lean`. These are universal matrix theorems, not sampled matrix tests. `merge_partial_palette` in `PaletteExtension.lean` performs the actual merging once the cross-conflict condition is established. |
| G13 list steps | `near_full_lists_sdr_or_uniform` proves the unique common-list obstruction for nine lists of at least eight colours (and the general n-list statement). `three_eight_lists_overlap` supplies the three-spoke pigeonhole step. The ambient geometric failure-state argument is still required. |
| G14 arbitrary-list proof | `small_colour_pool`, `three_parts_six_choosable`, `four_parts_seven_choosable`, and `five_parts_eight_choosable`. The five-part proof includes the exceptional four-colour merged-list case and its repair. The resumed Petersen kernel and extension results are described above. |
| G07 final reduction | `SmallComponentReduction.lean` proves conflict closure of every original connected component and its edge bound `|E(C)| ≤ 2|V(C)|`. `critical21_disjoint_component_sixteen` then excludes critical edges from a component with at most sixteen vertices, **conditional on the three G05 checks**. It does not assert that the G07 finite geometric search produces such a component. |
| S20 numerical step | `TwoRepresentativeSizeChecks.table` kernel-checks all entries of the displayed 3×7 table in section 7 of `factor_541_two_representatives.md`. `checked_bounds` covers all **448 = 2×2×4×4×7** parameter tuples, including both orders of the mixed row. `size_bound` derives 32, or 29 when a representative is low, from the explicit port inequality, admissibility constraints and parity. This is not a graph classification or a proof that every proposed critical kernel satisfies those premises. |

The G05 assumptions are precisely these `Prop` definitions in
`G05FiniteReduction.lean`:

| Named unexecuted check | Exact number of labelled simple-graph inputs before filtering |
|---|---|
| `G05SmallAbstractCheck` | `2^210 + 2^231 + 2^253 + 2^276 + 2^300` (orders 21–25) |
| `G05MiddleAbstractCheck` | `2^325 + 2^351 + 2^378 + 2^406 + 2^435 + 2^465 + 2^496 + 2^528 + 2^561 + 2^595 + 2^630 + 2^666 + 2^703 + 2^741 + 2^780` (orders 26–40) |
| `G05BoundaryAbstractCheck` | `2^820` (order 41) |

For every input graph with maximum degree at most 24 that is not
20-colourable, each check requires either a 20-clique or an eight-clique
whose vertices all have degree exactly 24. These obligations quantify over
**all** labelled abstract graphs of the indicated orders. They do not
include a criticality premise despite the helper name `AbstractCriticalCheck`.
They are much larger than the scalar parameter checks in
`CriticalSizeChecks.lean`; those earlier arithmetic checks do not discharge
them. No enumeration, certificate, or proved instance is claimed for any
of these three obligations. Their presence as ordinary theorem arguments
does not show up as a new axiom in `#print axioms`.

G15 likewise remains an ordinary explicit theorem argument. Its claimed
polynomial coefficient 12240 has not been recomputed here. No other new
source-theorem hypothesis was added in the resumed work.

### Remaining proof obligations, in BRIEF3 order

1. **4.7 and 4.9:** completed as stated above. This proves the odd-cycle
   reduction, not elimination of all remaining odd cycles or the general
   20-colour theorem.
2. **G05:** the three exact finite obligations remain unexecuted. The
   maximum-matching D/A/C decomposition, factor-critical odd blocks, and
   their colouring applications remain the missing route to unconditional
   results. Neither the 42-edge bound nor the rank-two colouring theorem
   is claimed unconditionally.
3. **G12:** the residual Hall matrices and palette merge are now proved.
   Still missing are the construction of compatible prescribed source and
   target colours, the exceptional five-cut row/column choice, and the
   endpoint counts proving those budgets for actual cuts. The global
   minimal-counterexample connectivity arguments are not formalized.
   **G13:** the Hall obstruction and overlap lemma do not yet supply the
   six-spoke accounting, equality-state geometry, same-side external-star
   argument, or the final fixed-outside recolouring construction.
   **G14:** the arbitrary-list theorem and induced internal-block extension
   are complete. The full incident-edge extension and the support case
   with no internal critical edge still require the external-edge count
   and support argument. **G16:** the variable-list block extension is
   available with G15; the matching-witness orientations, two-four-clique
   overlap classification, and identification of the actual induced
   Petersen-minus/Petersen block remain. **G02:** complete. **G07:** the
   small-component contradiction is formalized conditionally on G05;
   coverage and certificates for the high-star and subcubic sixteen-clique
   searches remain outside the formal development. The source reports
   nine subcubic branches, 63,118 type multisets and 20,623 recursive nodes;
   these reported computational totals are not Lean-verified certificates.
4. **A03, A04:** still require the degree-list block classification and a
   formal leaf-block extension that preserves current degrees. A04 also
   needs the complete eight-port chain analysis, including its central
   `K₃` case. **A02:** the identify-pair and add-bridge transformations
   must preserve every other private clique and the unique high-neighbour
   property while decreasing the high count. The new general Hall lemma
   handles its final near-full-list step only. **A06:** the incidence-weight
   hypergraph model, representative-pair exchange, pseudoforest argument,
   and two-stage minimum are still missing. None has been replaced by an
   assumed version of the target theorem.
5. **F03:** depends on the same unformalized critical-complement and
   maximum-matching decomposition, including the 19-vertex case.
   **F04, F05:** need actual arbitrary permutation-cover models and the
   unique-witness/Brooks interfaces for the selected fibre groups; the
   already proved local-injection pullback is insufficient because the
   base conflict graphs need more colours. **F07:** needs the affine
   matching normal form, monodromy, and spare-colour transition sequence,
   including the four-layer seven-colour lower bound. **F09:** the full
   five-edge forest-shape list, matching-four orientation model, and
   shape-by-shape extension counts remain beyond the existing endpoint,
   forbidden-shape and common-extension independence proofs.
6. **S02:** needs the high-clique critical-block classification and its
   endpoint realization. **S06:** needs the full twelve-neighbour model,
   bowtie converse and fourth-potential comparison. **S07:** needs the
   simultaneous list-repair constructions for whole full circles and long
   full runs. **S08:** needs the low-block port count, clique-separator
   gluing, and the disjoint radius-eight ball lower bound.
   **S17:** needs a representative-assignment construction preserving all
   named O₉ and thirteen-vertex exclusions. **S19:** needs the `(5,4,1)`
   exact profiles and zero exchanges followed by A03; an average-load
   bound is not an integer representative choice. **S20:** its full
   finite numerical table is now checked, but the low-block structure,
   disjointness of `K₄` blocks, geometric `t≤2` restriction when `sᵢ=3`,
   and port inequalities have not been derived for the actual joint
   critical graph. No full theorem from this S group is claimed.

### Source and provenance checks

The manifest has **136 source modules**, with every `Se20Part/**/*.lean`
file listed exactly once, plus the root `Se20Part.lean` import. The audit
contains **197** requested principal-declaration checks. A source scan
found no `sorry`, `admit`, `native_decide`, axiom declarations or unsafe
declarations. All **64** locally copied legacy modules match both their
recorded upstream SHA-256 hashes and the exact namespace/import
transformation. The additional 22 provenance entries are in
`THIRD_PASS_LEGACY_PROVENANCE.json`; the original 42-entry record is retained.
The upstream project was read only.

### Combined validation status

Individual recovery and resumed-development builds passed for all ten
modules covered by `THIRD_PASS_RECOVERY_LOG.txt`,
`LIST_BLOCK_EXTENSION_DEV_LOG.txt`, `PETERSEN_KERNEL_DEV_LOG.txt`,
`PETERSEN_EXTENSION_DEV_LOG.txt`, `SMALL_COMPONENT_DEV_LOG.txt`, and
`TWO_REPRESENTATIVE_SIZE_DEV_LOG.txt`.

The combined build and the expanded 197-declaration audit are **pending**.
The first attempt was refused by the one-process guard because another
task was running Lean. PID 1568 continued executing
`fourth_pass/RunStatistics.lean` for over ten minutes, through 11:56 on
2026-11-06. That unrelated process was not stopped. This task's waiting
PowerShell launcher was cancelled before returning, so no build remains
queued in the background. No combined success or new complete axiom output
is claimed. Once the other task has finished or paused, run `./build.ps1`
to check all 136 modules, the 197 audit requests, and the root import.

## Fourth pass

### Flaws and validation boundaries first

The inherited unnamed local decidable-equality instances were not safe to
combine through the audit import. They now have module-specific names,
including the two `Fin 10` instances. No proved theorem statement was changed.

The previous three G05 abstract checks remain unproved hypotheses. Their
statements have not been replaced by asserted computations. The parallel
Gallai degree-choosability development is not copied or reproved here.

This section is a work checkpoint. In particular, files written while the
other Lean process holds the compiler are not claimed to be verified. The
final whole-project build and audit will be recorded separately.

### Cut construction progress

`CutPaletteChoices`, `FiveCutChoices`, and `ExceptionalFiveCut` have passed
serial development builds. These prove the prescribed pairs for matching
cuts of size at most four, the ordinary five-source construction (at most
one twice-occurring source), its seven-repeated-colour failure count, and
the exceptional five-cut robust representative and candidate-count lemmas.
They are universal finite-set proofs, with no sampled matrices or new
theorem hypotheses.

`ForcedFiveCut`, `PaletteCompletion`, `FiveCutPalette`, `CutGeometry`,
`MatchingCutGeometry`, and `MatchingCutGluing` are being checked. Their
intended chain forces targets into the large opposite star union, completes
the remaining palette permutation, counts the actual ambient endpoint
neighbourhoods, and colours a labelled matching five-cut. Until those
checks pass, this paragraph records intended interfaces only.

`build.ps1 -WaitForLean` optionally waits for an existing compiler to exit.
The named build mutex, the refusal to start alongside another Lean process,
`-j1`, and the allocation limit remain enabled. No other process is stopped.

### Validation blocked by concurrent external compilers

The complete `./build.ps1` was invoked, without `-Only`. It reached
`Checking Se20Part.Definitions` and the process guard refused to launch
Lean because external PIDs **15808, 15972, 23020** were running. This is
**not** a successful build. The earlier serial check queue had waited
through several successive overlapping external jobs; that waiting
PowerShell session was interrupted before this full-build attempt.
**No fourth-pass build remains queued.** No external process was terminated.

The first development check of `CutGeometry` reported an incorrect
`Sym2.mk.inj_iff` name. The first check of `ForcedFiveCut` reported local
finite-subtype/cardinality elaboration errors. Those sources were corrected,
but the corrections have not yet been compiled. `SmallCutPalette` was also
written while compilation was blocked and is unverified. Accordingly,
the six pending modules listed above and `SmallCutPalette` are **drafts**;
their presence in the manifest and audit is not evidence of successful
checking. The expanded audit and root import remain uncompiled.

The manifest and source-only scan (`FOURTH_PASS_SOURCE_SCAN.txt`) found
**146 modules**, each listed once, **214 audit requests**, and no `sorry`,
`admit`, `native_decide`, axiom declarations, or unsafe declarations.
These source checks do not substitute for elaboration or axiom output.

### Exact remaining work

This is an incomplete fourth pass. No full G12 theorem is claimed.
First check the corrected cut chain in this order:
`ForcedFiveCut`, `PaletteCompletion`, `FiveCutPalette`, `SmallCutPalette`,
`CutGeometry`, `MatchingCutGeometry`, `MatchingCutGluing`.
The earlier renamed diffuse/route modules also need rebuilding before
the combined audit.

Beyond validation, G12 still needs the repeated-endpoint three- and
four-cut constructions, the transfer from induced-side colourings to the
ambient-side interfaces, and the minimal-counterexample connectivity and
regular-cut parity arguments. The new actual endpoint budgets include
the own-star subtraction `3d+u` and the budget summed over distinct
boundary endpoints, but their use in those remaining cases is unfinished.

G13, the remaining G14 and G16, replacement of the G05 abstract checks,
A03/A04/A02/A06, F09/F03/F04/F05/F07, and S02/S06/S07/S08/S17/S19 retain
their third-pass proof obligations. No new completion claim or replacement
hypothesis for these targets was introduced. In particular, this pass has
not yet reached an A03/A04 use of `GallaiDegreeChoosable`.

### Resumed verification and further proofs

This subsection supersedes the historical draft/blocked status above.
The resumed run uses the revised guard (at most two external Lean
processes), `-WaitForLean`, and `-j1`. Waiting polls more frequently near
the process threshold and reports every thirty seconds; the threshold,
named build mutex, and memory limit are unchanged. No external compiler
was stopped. Development output is in `FOURTH_PASS_RESUMED_CHECK_LOG.txt`.

All inherited cut drafts now pass development compilation, including
`ForcedFiveCut`, `PaletteCompletion`, `FiveCutPalette`, `SmallCutPalette`,
`CutGeometry`, `MatchingCutGeometry`, `CutSideColouring`,
`MatchingCutGluing`, `RepeatedCutPalette`, `LabelledCut`,
`RepeatedCutGeometry`, `LabelledCutGluing`, `CutBoundary`, and `CutMinimal`.
The corrections repair elaboration, finite-subtype cardinality arguments,
swapped-side conversions, and proof bodies; no theorem statement was
weakened. In particular, namespace hypotheses needed by the minimality
arguments are now explicitly included.

**G12 is complete in the checked modules.** `CutConnectivity` adds minimum
degree three, exclusion of matching five-cuts, the regular four-edge cut
bound, and connectedness after deleting any set of at most two vertices.
Together with the verified cut chain this includes the exceptional
five-cut palette, the repeated-endpoint three/four cuts, actual endpoint
counts, induced-side transfer, nontrivial cut bounds five/six, and regular
cut parity. Minimality is among all original graphs, not only regular ones.

The following additional modules have passed development compilation:

- `ExternalStars` and `K33Palette`: adjacent original vertices share at
  most one colour in their coloured stars; equal stars of size at least
  two force nonadjacency. Failure of the nine G13 lists forces the exact
  six-plus-three-plus-three disjoint equality state and equal stars on
  each side. Full G13 still needs the actual six-spoke accounting,
  equality-state endpoint geometry, and fixed-outside recolouring.
- `PetersenSupport`: selected conflicts are bounded by selected degrees
  on the ambient rim. The resulting bound fifteen completes the induced
  Petersen support exclusion without any ambient girth hypothesis.
- `PetersenMinusKernel`: the actual ten-vertex, fourteen-edge original
  model and its labelled G15 conflict graph are identified by kernel
  checks. Short paths show that the deleted edge is the only possible
  additional chord under girth at least five. Internal extension and
  disjointness from critical selected edges use the explicit named
  `PetersenMinusListTheoremG15` hypothesis. The coefficient 12240 has not
  been evaluated in Lean.
- `GallaiLowBlocks`: construction of uncolourable residual degree lists
  on a nonempty set of critical degree-k vertices, and classification of
  its connected induced blocks with no cut vertex as complete or odd
  cycles. The cited theorem is the ordinary named hypothesis
  `GallaiDegreeChoosable`, as requested; its proof is neither duplicated
  nor imported from the sister project.

The three further modules now also pass development compilation:

- `PetersenMinusSupport` completes the induced support exclusion using
  the bound eighteen and excludes every injected Petersen-minus-edge
  subgraph in girth at least five. Both statements retain the explicit
  G15 hypothesis. If the deleted edge is present, the proof identifies
  an induced Petersen block and uses its unconditional exclusion.
- `PetersenIncident` proves the full G14 incident-edge extension while
  preserving every outside colour. A kernel-checked common-neighbour
  lemma makes any injected Petersen subgraph induced under girth at least
  five. Its external spokes form a matching, have at most twelve fixed
  outside conflicts and at most six spoke conflicts, and can be greedily
  coloured before applying the internal eight-list extension. The
  critical-support subgraph corollary is also checked. No additional
  cited-theorem hypothesis is used in these G14 results.
- `CliqueSeparator` glues k-colourings across a complete separator by
  extending the two injective colour maps on the separator to a palette
  permutation. Consequently a vertex-minimal non-k-colourable graph has
  no such separator. This closes the complete-separator step of S08
  without a Gallai hypothesis; the other S08 arguments remain below.

### Remaining structural obligations after the resumed work

- **G13:** derive the full six-spoke equality geometry from actual
  original edges, construct the common-colour nonconflicting pair, and
  finish the extension while preserving every outside colour.
- **G16:** after the Petersen-minus block interface, formalize unique
  matching witnesses, the four-cycle orientation of each K4, and the
  opposite orientations forced by two K4s sharing a triangle. The source's
  explicit endpoint mapping still needs to be applied to those witnesses.
- **G05:** the three huge abstract checks remain unexecuted and have not
  been replaced by a claimed theorem. The local Mathlib contains Tutte's
  theorem, but not the required maximum-matching D/A/C decomposition.
  Still needed are its alternating-forest/blossom invariants or an
  equivalent derivation, factor-critical block and saving arguments,
  the small-saving classification through order 25, and the actual
  five-bag classification at order 41. Existing finite arithmetic checks
  do not establish those graph structures.
- **A03/A04:** connect the checked low-block classification to a leaf-block
  decomposition, prove its fixed-boundary list extensions, and finish the
  eight-port chain classification for A04, including the internal K3
  branch. **A02:** prove that the identify-pair/add-bridge transformations
  preserve every private clique and unique high neighbour. **A06:** build
  the weighted incidence model, representative multigraph exchange,
  pseudoforest orientation, and two-stage minimum argument.
- **F09:** classify all five-edge degree-two shapes and count extensions
  for each four-edge shape, including the matching orientation case.
  **F03:** use the missing matching decomposition for the 19-vertex
  factor-critical case. **F04/F05:** define arbitrary permutation covers
  and derive their selected-fibre conflict/Brooks interfaces.
  **F07:** prove affine matching normal form, monodromy, and spare-colour
  transitions, including the four-layer seven-colour lower bound.
- **S02:** finish the high-clique critical-block classification and
  endpoint realization. **S06:** build the twelve-neighbour model, prove
  the bowtie converse, and compare the fourth potential. **S07:** build
  simultaneous list repairs for full circles and seven-full runs.
  **S08:** after complete-separator gluing, derive the low-block port bound
  and disjoint radius-eight ball lower bound from actual distances.
  **S17:** construct the simultaneous representative assignment preserving
  all named exclusions. **S19:** derive exact (5,4,1) profiles and zero
  exchanges and apply the still-incomplete A03 theorem.

### Resumed combined validation

The first resumed whole-build queue was interrupted while waiting at
`Greedy`, to check the additional proof modules first. No external process
was interrupted. That partial log is not a successful whole build.
All development checks and the final whole build now pass. The command
`./build.ps1 -WaitForLean` rebuilt all 162 manifest modules and the root
`Se20Part.lean`, using `-j1`, and finished with exit code 0. The combined
audit and root import both compiled; the earlier combined-import failure
has not recurred. The full output is in
`FOURTH_PASS_RESUMED_FULL_BUILD_LOG.txt`. There are no build errors;
deprecation and unused-variable/tactic linter warnings remain. No local
build is left queued.

All 266 requested axiom results are present. Their complete output is
also extracted to `FOURTH_PASS_RESUMED_AXIOMS.txt`. The only axioms that
appear are `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx`, reduction-oracle axiom, or new declared axiom. Named theorem
hypotheses, including G15, `GallaiDegreeChoosable`, and the three unresolved
G05 checks, remain ordinary arguments: this audit does not prove them.

The source scan (`FOURTH_PASS_RESUMED_SOURCE_SCAN.txt`) finds 162 source
modules, each listed exactly once in dependency order, 266 audit requests,
and no forbidden proof placeholders, `native_decide`, axiom declarations,
or unsafe declarations, including the root module. All 64 legacy copies match both their recorded
upstream SHA-256 hashes and the exact namespace/import transformation.

## Fifth pass

### Flaws and proof boundaries first

This pass is still **partial**. Importing Gallai does not by itself prove
A03/A04, and a proof of an end-block list lemma does not identify the lists
arising from the actual high neighbours of a critical graph. In particular,
the lists reconstructed by `DegreeList.bad_induced_lists` are obstruction
lists; their existence must not be used as if they were a prescribed
outside colouring's residual lists. The new results below maintain that
distinction. No full A03/A04/A02/A06 theorem is claimed.

G05 still has no proved instance of any of its three old abstract-check
propositions. The real matching route has not been replaced by those
checks. Also, the supplied `critical41_triangles.md` explicitly rules out
the shortcut “factor-critical and sigma=nu implies triangle-free,” with
its seven-vertex example. This pass does not use that false shortcut or
claim a new Lean verification of that example.

`MatchingOverlapModel` checks the explicit normalized endpoint graph.
It does **not** prove that every pair of matching-conflict K4s sharing a
triangle has this normalization. Likewise, the new two-matching theorem
proves S17's abstract assignment step, **not** the geometric assertion that
all the actual O9/thirteen-vertex partner relations are those matchings.
Neither missing statement has been introduced as an axiom or as a new
hypothesis purporting to complete the corresponding target.

No counterexample to a requested headline statement was established in
this pass. The blocking items below are unclosed formal proof obligations,
not declarations that their mathematical statements are false.

### Gallai imported and the hypothesis removed

The following eight modules were copied from
`E:/lean/se20-insertion/Se20Insertion/`, changing only
`Se20Insertion` to `Se20Part`:

- `DegreeListTools`, `DegreeListReduction`, `NonseparatingPair`,
  `DegreeListInduced`, `DegreeListBrooks`, `FiniteNonseparating`,
  `RegularCycle`, and `Gallai`.

`DegreeListTools` also requires `CriticalLists`. Its proof was copied with
the same namespace transformation and its large `InfiniteForest` import
replaced by `GallaiPrerequisites`. That small local interface extracts
`CriticalSet`, partial-colouring restriction, coloured neighbours, and
available-colour counting from `CriticalStructure`, `HoleMoves`, `Counting`,
and `LowDegree`. No sister-project source was edited and there are no
remaining imports of the sister project.

`GALLAI_PROVENANCE.json` records the eight exact copies and upstream
SHA-256 hashes. `GALLAI_SUPPORT_PROVENANCE.json` records the additional
five source hashes and the different adaptation/extraction boundaries.
The source audit checks the exact eight transformations and the exact
`CriticalLists` import/namespace adaptation.

The complete `degree_list_obstruction_gallai_tree`, its critical-degree-20
corollary, and `corollary1140_five` now compile locally. The bridge
`gallaiDegreeChoosable` proves the existing `GallaiDegreeChoosable`
proposition, including conversion from an actual odd-cycle isomorphism
to the older intrinsic degree/order interface. The proposition definition
is retained for compatibility, but **no theorem takes it as a hypothesis**.
`minimal_low_block_classification` now calls the proved theorem directly.
Removing that argument is the explicitly requested strengthening; its
remaining premises and conclusion were not weakened or changed.

### Further checked results

- **`FiniteEndBlock`:** `finite_induced_separation` and `exists_end_block`
  construct a genuine nonempty end-block interior. All its neighbours
  lie in the block; the block has at most one extra boundary vertex, is
  connected, and has preconnected single-vertex deletions. The proof
  minimizes a finite region with at most one outside neighbour. It does
  not assume a block tree or a leaf-block existence theorem.
- **`CriticalColourTools`:** extracts a vertex-minimal non-k-colourable
  induced subgraph and proves its minimum-degree bound k.
- **`GallaiEndBlock`:** a connected degree-list obstruction has a complete
  or odd-cycle end block. `critical_regular_has_clique` and
  `colourable_of_degree_le_no_clique` prove the ordinary maximum-degree-k,
  no-(k+1)-clique colouring theorem for k>=3. This supplies the no-high
  branch of A02/A03/A04 and the ordinary colouring engine needed by
  F04/F05, without a new Brooks hypothesis. Older named Brooks interfaces
  are left unchanged.
- **`EndBlockLists`:** failure to colour a complete leaf after removing
  its fixed boundary colour forces identical lists before that removal.
  The common-spare-colour repair for the two-list case is also proved,
  with properness and avoidance of the boundary colour explicit.
- **`HighCliqueCritical`:** an induced degree-(k+1) vertex under ambient
  maximum degree k+1 retains every ambient neighbour; high-clique
  adjacency is inherited. For A04's actual critical graph, at most three
  high vertices implies exactly two. When the high set is a clique,
  these two vertices are adjacent and each has exactly four low
  neighbours. These are the actual eight ports, not a numerical
  assumption about an unconstructed block chain.
- **`MatchingOverlapModel`:** the five matching edges and nine normalized
  witnesses are identified with the original Petersen-minus-edge graph
  by `decide +kernel`. `matching_cross_witness_unique` excludes the other
  three possible cross witnesses using the ambient girth condition.
  `critical21_no_normalized_matching_overlap` applies the previously
  proved support exclusion with the explicit named
  `PetersenMinusListTheoremG15` hypothesis. No coefficient computation or
  proof of G15 is claimed; the permitted named-hypothesis route was used.
- **`TwoMatchings`:** the union of any two finite matchings is
  two-colourable, allowing shared edges. The proof uses the checked
  path/cycle decomposition and parity, and constructs the simultaneous
  two-part assignment used by S17. It does not assert the geometric
  partner-matching hypotheses for the original representatives.

### Exact disposition of every requested older target

The order below follows the request. “Blocked” means the specified proof
step remains unproved here; none of these rows is counted as a completed
headline theorem merely because a supporting lemma compiles.

| Target | Status and precise remaining proof |
|---|---|
| **A03** | **Blocked.** Gallai, an end block, the no-high case, and the two boundary-list mechanisms are now proved. Still needed: apply the end block to the actual degree-k low graph, derive the exact high-neighbour sets and their distinct colours, exclude the equal-list case by an actual K_k, and assemble the extension of the critical subgraph. The odd-cycle branch must derive the common spare and differing missing-high colours from the actual graph. |
| **A04** | **Blocked.** The two-high reduction and four-plus-four low ports are proved. The low-block incidence chain, all combinations of two leaves, exclusion of the internal K3 branch, and the colourings of the remaining bridge/K4 chains are still missing. |
| **A02** | **Blocked.** The critical high-vertex retention step is available. The identify-pair and add-bridge transformations are not implemented: they must preserve every surviving private clique and unique high neighbour, decrease the high count, and exclude a newly created K_(k+1), including the added low-bridge branch. |
| **A06** | **Blocked.** The weighted incidence model and minimal-counterexample reduction have not been formalized. Missing are representative multigraph exchanges that strictly reduce odd cycles, the indegree-one pseudoforest proof, and the primary/secondary minimum comparison. The source's weight budgets alone do not supply a four-colouring. |
| **G13** | **Blocked.** Existing Hall-failure and equal-external-star lemmas remain checked. The actual K3,3 incident-edge decomposition must still give the six-spoke bound, equality-state saturation/unique external endpoints, a genuinely nonconflicting common-colour pair, and the extension preserving every arbitrary outside colour. The 100 boundary examples are not a universal certificate. |
| **G16** | **Blocked.** Unique witnesses, the explicit normalized endpoint isomorphism, and the G15-based exclusion of that normalized graph are checked. Still missing: derive the four-cycle orientation of an arbitrary matching-conflict K4 and the opposite orientations for two K4s sharing a triangle, then relabel their actual endpoints into the checked normal form. G15 stays a named hypothesis. |
| **G05, real route** | **Blocked.** No maximum-matching D/A/C theorem has been formalized. The first missing interface must construct factor-critical odd components, separation from C, the matching structure, and exposure of every D vertex by a maximum matching. Subsequent gaps are optimal clique-saving replacement/additivity, the small-saving and order-25 cases, the order-41 triangle branch, and construction/reclassification of the actual five bags in the triangle-free branch. Existing finite arithmetic inequalities do not establish any of these graph structures. The three old abstract checks remain unexecuted hypotheses, not a substitute. |
| **F09** | **Blocked.** Existing endpoint exclusions and common-extension independence do not yet give the complete five-edge path/cycle shape classification or the five four-edge extension counts. In particular the matching-four orientation cases must be enumerated from actual endpoints and shown exhaustive. |
| **F03** | **Blocked.** It needs the critical-complement/matching decomposition also missing in G05, including the factor-critical order-19 equality case, its D/A/C blocks, and the cross-edge counting argument. The parameter contradictions alone cannot produce the nine-/ten-colour theorem. |
| **F04** | **Blocked.** The ordinary subcubic colouring engine is now proved. The arbitrary Z11 permutation-cover model, independent red fibres, the six unique conflict-witness matchings on the selected four fibres, and their ambient four-cycle exclusion are still absent. Local-injection pullback does not supply these statements. |
| **F05** | **Blocked.** The maximum-degree-five colouring engine is now proved. The six-cycle double-base arbitrary-cover model, two selected six-fibre graphs, unique witnesses, and the geometric K4 exclusion still need formalization. No finite sample of covers is being promoted to the arbitrary-cover statement. |
| **F07** | **Blocked.** Missing are the complete blue-matching reduction, affine normal form, conjugate red nonconflict matching, monodromy classification, spare-colour schedules for arbitrary length, and the four-layer lower bound. The 84 checked colour tables do not cover arbitrary chains. |
| **S02** | **Blocked.** The actual O9 uniqueness classification needs the four-high eight-port low-block analysis and its endpoint realization. A04's two-high case is also incomplete. Single-point insertion and the alternating labels on an odd C cycle therefore have not been assembled. |
| **S06** | **Blocked.** Missing are the twelve-neighbour model, full-end/bowtie equivalence, and preservation/comparison of all four potentials for the exchanges. No equivalence between geometric full ends and actual insertion failure has been assumed. |
| **S07** | **Blocked.** The path/cycle-plus-matching list-degeneracy count and its actual simultaneous neighbourhood interface are not proved. Both arbitrary collections of full circles and seven-full runs still need the shared list-repair construction; six-point weakening remains outside the requested theorem. |
| **S08** | **Blocked.** Complete-separator gluing and Gallai are checked. Still needed are the low-block port inequality, grouping all actual high vertices by representatives, and the disjoint radius-eight ball lower bound from actual graph distances. No distant representative selection is asserted. |
| **S17** | **Blocked.** The abstract union-of-two-matchings assignment is now proved. It must still be applied to constructed O9 and P3/K2 thirteen-vertex partner relations: prove each is a matching, prove the two kinds have disjoint support on each side, and classify all configurations removed by the assignment. Three-representative exceptions are not silently included. |
| **S19** | **Blocked.** The exact (6,5,1) and (5,5,2) profiles, the two-stage minimum and zero exchanges, and the high-clique conclusion for the actual inserted graph are missing; the final application also needs full A03. An expected-load calculation is not an integer choice or a colouring. |

### Validation and build behaviour

`build.ps1` now runs one local compiler at a time with `-j1`, retains the
6000 MB allocation limit, and does not wait for unrelated Lean jobs or
hold the former named global build mutex. It publishes each successfully
compiled olean from a process-specific temporary file. Transient
import/memory failures retry after two seconds; proof errors fail normally.
`-WaitForLean` remains accepted for command compatibility but no longer
enables a process-count gate. No other compiler was stopped.

All new modules passed development checks. The expanded combined import,
295-declaration axiom audit, and root import passed in
`FIFTH_PASS_COMBINED_CHECK_LOG.txt`. `audit_fifth_pass.ps1` verifies the
manifest's **179** source modules, each once in dependency order, and
scans them plus the root. Its output is `FIFTH_PASS_SOURCE_SCAN.txt`:
no proof placeholders, `native_decide`, axiom declarations, or unsafe
declarations; all **64** legacy copies and the **8** exact Gallai copies
match their recorded hashes and transformations.

The final whole-project `./build.ps1` run rebuilt all **179** manifest
modules and the root `Se20Part.lean` with `-j1`, and finished with **exit
code 0**. The complete 180-check sequence matches the manifest in order.
There were no build errors or runtime retries; linter warnings remain.
No local build is left running and no temporary compiler objects remain.
The full output is `FIFTH_PASS_FULL_BUILD_LOG.txt`, with the exit code in
`FIFTH_PASS_FULL_BUILD_EXIT.txt` and validation summary in
`FIFTH_PASS_FULL_BUILD_VALIDATION.txt`.

All **295** axiom results are present in exactly the requested order and
are extracted to `FIFTH_PASS_AXIOMS.txt`. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`, reduction
oracle, or new declared axiom. The source/provenance audit was rerun and
passed. G15 and the unresolved G05 checks remain ordinary named
hypotheses: their absence from the axiom list does not prove them. The
eighteen headline targets listed above remain blocked at their stated
proof obligations; a successful build does not close those obligations.

## Sixth pass

### Flaws and proof boundaries first

**A03 is now proved in full.** This changes the fifth-pass status of A03,
not the status of the other headline targets. No counterexample to a
requested headline statement was found in this pass. The remaining
blocks below are unfinished formal proofs, not claims that their
mathematical statements are false.

The prescribed-list distinction from the fifth pass is essential here.
`critical_prescribed_lists` constructs one actual colouring of the
complement of the selected block. Its lists are exactly the full palette
minus the colours of that vertex's outside neighbours. Uncolourability
is proved by gluing a hypothetical list colouring to that same fixed
outside colouring. The proof never substitutes reconstructed obstruction
lists for these prescribed lists.

The whole low block is deleted, including its possible boundary vertex.
Every vertex of this block is degree k in the critical graph, so its
prescribed list has size at least its degree inside the block. For a
nontrivial block, the already proved non-cut uniformity theorem therefore
forces all these actual lists to coincide. This avoids the separate
boundary-repair and spare-colour constructions in the manuscript. It
does not assume that the graph remains critical after deleting a leaf.

A04 does not follow by substituting k=4 into A03: A03 excludes K4,
whereas A04 only excludes K5 and must handle low K4 blocks. Similarly,
the numerical port count is not a construction of A04's block chain.
The normalized graph in G16 still does not classify arbitrary overlaps,
and the old G05 finite-check propositions remain unexecuted hypotheses.
No new hypothesis has been added to stand in for any of these gaps.

### Closed headline target: A03

`Se20Part/HighCliqueColouring.lean` proves
`high_clique_low_clique_free_colourable`:

```lean
theorem high_clique_low_clique_free_colourable {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 3 ≤ k)
    (hΔ : ∀ v, H.degree v ≤ k+1)
    (hfree : H.CliqueFree k)
    (hQ : H.IsClique (highVertices H k : Set W)) : H.Colorable k
```

These are exactly the hypotheses of
`reference/research/high_clique_low_clique_free.md`: finite graph,
k≥3, maximum degree at most k+1, no K_k, and all degree-(k+1) vertices
forming a clique. There is no Gallai, Brooks, list-extension, finite-check,
or other external mathematical theorem argument.

The proof extracts an actual vertex-minimal non-k-colourable induced
subgraph. Its high vertices retain all ambient neighbours, so they still
form a clique. `induced_set_end_block` supplies an end block in its actual
degree-k low graph, with a nonempty interior and at most one boundary
vertex. The checked Gallai theorem classifies that block.

At each interior vertex, every neighbour outside the block is high.
The high clique has distinct colours in the fixed outside colouring.
Equality of the prescribed palettes consequently gives equality of the
actual external neighbour sets, not merely equality of their sizes.

For a complete block of order r, each interior vertex has k-r+1 common
high neighbours. The interior has at least r-1 vertices, so its union
with those common neighbours is a clique of order at least k. This also
handles singleton blocks, without invoking nontrivial-block uniformity.
For an odd-cycle block, an interior vertex has two block neighbours;
since at most one block vertex is outside the interior, two adjacent
interior vertices exist. Their k-2 common high neighbours produce an
actual K_k. Both branches contradict the original clique-free premise.

The new module is in `build.ps1`, the root import, and `AxiomAudit.lean`.
No previously proved theorem statement or proof was changed. The only
edits to existing Lean files are the root import and audit import/requests.

### Remaining targets, in the requested order

After closing A03, the remaining source arguments and checked interfaces
were reviewed in order. No additional support-only modules were added,
and no F or S target was started.

| Target | Sixth-pass disposition and precise gap |
|---|---|
| **A03** | **Closed**, by the unconditional theorem above. |
| **A04** | **Blocked.** The actual two-high/eight-port reduction is checked. A proof still has to construct the low block–cut incidence tree, force exactly two leaves from the eight ports, exclude the mixed K3/K4 and internal K3 cases, and colour every remaining bridge/K4 chain. The new A03 proof does not resolve these K4-containing graphs. |
| **G13** | **Blocked.** The Hall obstruction and equal-star nonadjacency are checked. Missing are the decomposition of all edges incident to an arbitrary K3,3, the six-spoke and external-conflict bounds, the equality-state endpoint saturation and distinctness, and the actual nonconflicting repeated-colour pair followed by an extension preserving the arbitrary outside colouring. No sampled boundary check supplies this universal endpoint argument. |
| **A02** | **Blocked.** High-vertex retention is checked. Both graph transformations remain unconstructed: identify the nonadjacent endpoints in the enlarged low-clique case, or delete the private clique and add the low bridge. Preservation of every surviving private clique/unique high neighbour, strict decrease of high vertices, and exclusion of a new K_(k+1), especially across the added bridge, are still needed. |
| **A06** | **Blocked.** The weighted incidence model and its vertex-minimal counterexample have not been constructed. The representative multigraph exchange, indegree-one pseudoforest result, and the two successive potential minima must be proved for the actual hypergraph. A degree/weight budget alone is not the requested arbitrary-size four-colouring. |
| **G16** | **Blocked.** The fixed endpoint model and its G15-based exclusion are checked. Still missing are the four-cycle permutation of arbitrary K4 witnesses, opposite orientations of two K4s sharing a triangle, and an injective relabelling of their actual endpoints into the normalized model. G15 remains the explicit named hypothesis already permitted in earlier passes. |
| **G05, real route** | **Blocked.** The first missing graph theorem is still the maximum-matching D/A/C decomposition, with factor-critical odd components, separation, matching structure, and exposure of every D vertex. It must then be connected to optimal clique-saving replacement/additivity, the small-saving and order-25 cases, the order-41 triangle case, and the construction and reclassification of the five actual bags in the triangle-free case. The source's seven-vertex counterexample still rules out inferring triangle-freeness merely from factor-criticality and sigma=nu. |

The other F/S target statuses remain as in the fifth pass. In particular,
closing A03 supplies S19's final colouring theorem but does not prove its
profile, minimum, or exchange hypotheses, so S19 is not counted as closed.

### Validation

The development compile of the complete A03 module passed with `-j1`.
The combined audit and root import passed in
`SIXTH_PASS_COMBINED_CHECK_LOG.txt`. The seven new axiom requests all
report only `propext`, `Classical.choice`, and `Quot.sound`.

The source/provenance audit (`SIXTH_PASS_SOURCE_SCAN.txt`) checks all
**180** manifest modules, each once in dependency order, and the root,
with **302** axiom requests. It finds no proof placeholders, reduction
oracle, declared axioms, or unsafe declarations. All 64 legacy copies,
eight exact Gallai copies, and five Gallai support source hashes still
pass their existing provenance checks.

The final whole-project `./build.ps1` run rebuilt all **180** manifest
modules and the root `Se20Part.lean` with **`-j1`**, finishing with
**exit code 0**. There were no build errors or runtime retries; existing
linter warnings remain. The existing retry-on-import/read-failure
behaviour was retained. No compiler from this build is left running,
and no temporary compiler objects remain.

`audit_sixth_pass.ps1` verified the complete **181-check** sequence against
the manifest and root, and all **302** axiom results against their exact
requested order. The only axioms in the complete output are `propext`,
`Classical.choice`, and `Quot.sound`. Source and provenance checks were
rerun and passed. The final artifacts are:

- `SIXTH_PASS_FULL_BUILD_LOG.txt` and `SIXTH_PASS_FULL_BUILD_EXIT.txt`;
- `SIXTH_PASS_FULL_BUILD_VALIDATION.txt`;
- `SIXTH_PASS_AXIOMS.txt`;
- `SIXTH_PASS_SOURCE_SCAN.txt`.

This pass closes **one headline target, A03**. The six later priority
targets remain blocked at the obligations listed above; their successful
compilation is not counted as a proof of those targets.
