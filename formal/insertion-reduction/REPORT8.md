**Flaws first.** The pair-existence statement proposed in BRIEF8 is false without a degree restriction: an even cycle is two-connected, neither complete nor an odd cycle, but deleting two nonadjacent vertices disconnects it. The checked C4 witnesses are `square_connected`, `square_delete_connected`, `square_not_complete`, and `square_no_nonseparating_pair` in [EighthPassExamples.lean](Se20Insertion/EighthPassExamples.lean). The structural theorem assumes minimum degree at least three. The degree-two case is proved separately by a graph isomorphism with a cycle and an actual two-colouring of even cycles. The final Gallai conclusion has no minimum-degree restriction.

**Scope that remains explicit.** P6 constructs a simple graph from a supplied three-regular bipartite relation and assumes girth at least seven for that constructed graph. This is the conditional structural statement in the [source P6 report](../se20-gap/REPORT.md). It does not establish existence of high-girth relations for arbitrary parameters or validate the t=40 certificate. The hole lies outside C–L. The fixed-pair obstruction concerns donor colours outside the pair and swaps of that pair; the graph also has a strong 17-colouring. The mean-27 theorem retains the premise of 24 actual coloured neighbours. No existing theorem statement or manuscript text was weakened or changed.

**Completed and checked.** Gallai's degree-list obstruction theorem, Corollary 11.40(5), the abstract P6 construction and core computation, its colouring and route obstruction, and the 103/27/84 count corollaries have all passed Lean. **The complete build also passed: all 94 authored modules and the root module were rebuilt serially with `-j1`, exit code 0.** The previous waiting-only checkpoint is superseded by these checks.

**Gallai and 11.40(5).** The proof in [Gallai.lean](Se20Insertion/Gallai.lean) uses these checked steps:

1. [DegreeListInduced.lean](Se20Insertion/DegreeListInduced.lean): colour the complement of any nonempty induced set toward that set, remove the used outside-neighbour colours, and obtain uncolourable lists at least the internal degrees.
2. [DegreeListBrooks.lean](Se20Insertion/DegreeListBrooks.lean): bad lists in a connected graph with connected vertex deletions are uniform; their common size also obstructs ordinary degree-colouring.
3. [FiniteNonseparating.lean](Se20Insertion/FiniteNonseparating.lean): in a finite connected graph with connected single-vertex deletions, minimum degree at least three and non-completeness imply two distinct nonadjacent vertices with a common neighbour and connected pair-deletion. In the cut case of G−v, farthest marked vertices in two different branches are non-cut vertices and can be deleted together. A third neighbour of v connects the remaining graph back to v.
4. [RegularCycle.lean](Se20Insertion/RegularCycle.lean): a finite connected two-regular graph is isomorphic to an actual cycle. Even cycles are two-colourable. Together with the nonseparating-pair colouring lemma, this proves the complete-or-odd-cycle classification for bad lists on graphs with no cut vertex.
5. Apply the induced obstruction to each finite block. No general block-tree theory or classification premise is used.

`BlockEligible H B` means that H[B] is connected and every single-vertex deletion is preconnected. `FiniteBlock H U B` means that B is maximal among such subsets of U; this includes bridges and isolated vertices. `GallaiForestOn H U` means that every such block is complete or isomorphic to an odd cycle. `GallaiTree H` adds connectedness and takes U to be the full finite vertex set. Odd cycles mean `∃ n, Odd (n+3) ∧ Nonempty (H ≃g cycleGraph (n+3))`.

The principal statements, with the surrounding vertex and graph parameters written explicitly, are:

```lean
degree_list_obstruction_gallai_tree
    {W : Type*} [DecidableEq W] (H : SimpleGraph W)
    [Fintype W] {C : Type*}
    (L : W → Finset C) (hc : H.Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card)
    (hbad : ¬ DegreeList.ColourableOn H L Finset.univ) :
    GallaiTree H

critical_degree_twenty_gallai
    {W : Type*} [DecidableEq W] (H : SimpleGraph W)
    {F : Finset W} (hcrit : CriticalSet H F) :
    GallaiForestOn H (criticalDegreeTwenty H F)

corollary1140_five
    {V : Type*} (G : SimpleGraph V)
    {F : Finset G.edgeSet} (hcrit : CriticalSet (L2 G) F) :
    GallaiForestOn (L2 G) (criticalDegreeTwenty (L2 G) F)
```

Here `criticalDegreeTwenty H F := F.filter (fun x => (F.filter (H.Adj x)).card = 20)`. Degrees are taken inside the critical induced graph; adjacencies remain those of the ambient conflict graph. The corollary does not require the ambient vertex type to be finite. The final Gallai theorem permits an empty colour type and handles it separately. This is the requested obstruction direction, not a converse constructing bad lists on every Gallai tree.

**P6.** [P6Construction.lean](Se20Insertion/P6Construction.lean) defines `Leaf I := I × Fin 2` and `Vertex I := I ⊕ (Leaf I ⊕ Leaf I)`. A centre is adjacent to its two lower and two upper leaves. A lower leaf l is adjacent to an upper leaf u exactly when B(l,u). `ThreeRegular B` requires every row and column of B to have cardinality three. The vertex count is 5|I|, the part sizes are |I|, 2|I|, 2|I|, and the exact neighbour-count matrix is:

```text
       C  L  U
C      0  2  2
L      1  0  3
U      1  3  0
```

`pattern B hB` packages these counts; `Pattern.degree` proves four-regularity. [P6Geometry.lean](Se20Insertion/P6Geometry.lean), [P6Sizes.lean](Se20Insertion/P6Sizes.lean), and [P6Core.lean](Se20Insertion/P6Core.lean) prove the following exact counts at girth at least seven, with t = |I|:

| Edge class | Size | Selected-colour neighbours | Degree in S | Threshold |
| --- | --- | --- | --- | --- |
| C–U | 2t | 5 | 19 | 17 |
| L–U | 6t | 6 | 18 | 18 |

`PairClasses P φ a b` means precisely that `e ∈ F ∧ φ.colour e ∈ {a,b}` iff e is a C–L edge; in particular every C–L edge is coloured. For a one-hole colouring and distinct a,b, `pair_S_eq` identifies S with all C–U and L–U edges. At girth at least seven, `pair_core_eq` identifies the core with that same set, and `hole_in_pair_core` places the hole in it.

[P6Colouring.lean](Se20Insertion/P6Colouring.lean) proves `exists_seventeen_colouring` using disjoint palettes of sizes 2+2+13. It constructs the one-hole state in `exists_pair_state`; the draft's unused-context issue in `strongColourable_seventeen` was repaired by explicitly retaining its Pattern parameter. The final constructed-family statement is:

```lean
theorem propositionP6
    (B : Leaf I → Leaf I → Prop) (hB : ThreeRegular B)
    (hg : 7 ≤ (graph B).egirth)
    {h : (graph B).edgeSet} (hh : h ∈ (pattern B hB).outside) :
    ∃ φ : PartialColouring (L2 (graph B)) (Finset.univ.erase h),
      (pattern B hB).PairClasses φ 0 1 ∧
      φ.colourSetS h {0,1} = (pattern B hB).outside ∧
      φ.colourSetCore h {0,1} = (pattern B hB).outside ∧
      (φ.colourSetCore h {0,1}).card = 8 * Fintype.card I ∧
      h ∈ φ.colourSetCore h {0,1}
```

The surrounding parameters are `{I : Type*} [Fintype I]`. [P6Route.lean](Se20Insertion/P6Route.lean) defines `FixedPairStep a b` by actual legal hole moves whose donor colour avoids {a,b}, and swaps of that pair on Kempe-closed sets. `fixedPairRoute_blocked` quantifies over `Relation.ReflTransGen (FixedPairStep a b) s t` and proves that neither selected colour is free and the pair is not separable at t's actual hole. Thus arbitrary finite interleavings are covered, not only one move. The theorem works with arbitrary finite colouring domains once PairClasses holds.

**Numerical corollaries.** [LongChainCounts.lean](Se20Insertion/LongChainCounts.lean) defines L(v), `longPairCount v`, by counting unordered distinct-colour pairs that are tangled and have no direct witness. `long_pair_witness` supplies both properties for every counted pair. In every row below, φ is a partial 20-colouring of L²(G) on a finite edge set E, the ambient vertex type is finite, `MaxDegreeFour G`, and `7 ≤ G.egirth`.

| Checked declaration | Additional hypotheses | Conclusion |
| --- | --- | --- |
| `allPairsFail_long_at_hole` | `φ.AllGroupsFail h 2` | `103 ≤ φ.longPairCount h` |
| `allPairsFail_long_mean` | `φ.AllGroupsFail h 2`; `(φ.colouredNeighbours h).card = 24` | `27 * (φ.colouredNeighbours h).card ≤ ∑ f ∈ φ.colouredNeighbours h, φ.longPairCount f` |
| `allPairsFail_long_mean_rat` | Same premises | The rational arithmetic mean is at least 27. |
| `allNineteenFail_long_at_single` | `h ∉ E`; `φ.AllGroupsFail h 19`; `φ.Single h p f` | `84 ≤ φ.longPairCount f` |
| `allNineteenFail_sixteen_long_singles` | `h ∉ E`; `φ.AllGroupsFail h 19`; coloured-neighbour cardinality 24 | At least sixteen single colours, and every single representative has count at least 84. |

The arithmetic is 190−87=103, mean tangled count at least 114 minus 87 giving 27, and 171−87=84. The 24-neighbour premise is unnecessary for the first and fourth bounds. These statements use genuine girth at least seven, not the insufficient `LocallyTreeAt` predicate discussed in REPORT7.

**Validation and axiom output.** [build.ps1](build.ps1) rebuilds every project module and the root module from source using `lake env lean -j1`, serially. It reads the existing local dependency oleans without invoking a dependency build. As authorized in the resumed brief, it does not wait for unrelated Lean processes. Both it and [check8.ps1](check8.ps1) retry only `failed to read file`, after five seconds, and stop on proof/type errors, including tagged Lean errors.

The full build ran on 2026-11-06 from 14:15:18 to 14:35:24 Australia/Sydney (+11:00), completed all 95 checks, and required **zero dependency-read retries**. It emitted lint/deprecation warnings but no errors. The complete output is saved in [BUILD8.log](BUILD8.log), including the successful exit code. A separate manifest check found all 94 authored modules exactly once and no dependency-order errors.

The statement-dump command `./check8.ps1 Print8 -SourcePath Print8.lean` also exited 0. Every one of the 122 inventory names occurs exactly once in its output. All 609 audit commands likewise have corresponding output entries, including every eighth-pass declaration.

[AxiomAudit.lean](Se20Insertion/AxiomAudit.lean) includes all 122 eighth-pass declarations and the earlier audit. [audit8.ps1](audit8.ps1) regenerates that addition, the [declaration inventory](DECLARATIONS8.txt), and [Print8.lean](Print8.lean). [STATEMENTS8.txt](STATEMENTS8.txt) contains the actual elaborated `#check` output for all 122 declarations, including all inferred parameters; [AXIOMS8.txt](AXIOMS8.txt) contains the actual full-project `#print axioms` output from the successful build.

The union of all 609 reported axiom closures is exactly `{propext, Classical.choice, Quot.sound}`. Thus every eighth-pass closure is a subset of these standard axioms; five of the 122 new declarations depend on no axioms. There is no `sorryAx`, additional axiom, or native-evaluator axiom in the audit. Selected actual output:

```text
'Se20Insertion.degree_list_obstruction_gallai_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.corollary1140_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.P6.propositionP6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.P6.Pattern.fixedPairRoute_blocked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allPairsFail_long_at_hole' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allPairsFail_long_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.allNineteenFail_long_at_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The authored Lean source scan found no `sorry`, `admit`, `native_decide`, `ofReduceBool`, or new axiom declarations. The successful build and axiom output, rather than that scan alone, establish the validation claim. Repairs addressed dependent equality/finite-instance conversions, explicit connectivity fields, walk mappings, tactic syntax and API arguments. The intended theorem hypotheses and conclusions were retained.

**Not done.** There is no formalized high-girth P6 relation-existence theorem or checked concrete t=40 certificate, and no Gallai converse constructing bad lists on every Gallai tree. No insertion conjecture, independent-transversal assertion, or other outstanding target from REPORT7 is claimed proved. The three requested eighth-pass proof developments and their validation are complete within the explicit scopes above.
