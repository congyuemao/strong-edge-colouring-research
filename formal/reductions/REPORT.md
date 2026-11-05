# Formalization report

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
