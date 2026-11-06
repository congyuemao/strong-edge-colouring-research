**Flaws and unfinished primary target first.** This pass does **not** complete Gallai's degree-choosability theorem or Corollary 11.40(5). It proves the list-colouring and non-separating-pair colouring lemmas described below, but not the structural existence theorem or block decomposition needed to finish the classification. No classification theorem has been assumed, and no new axiom is introduced.

**The existing `LocallyTreeAt` predicate is insufficient for 11.5.** Its definition in `ShellCover.lean` excludes only triangles and squares through the hole. A six-cycle satisfies it, yet opposite far edges conflict through the opposite edge of the cycle. The new checked witnesses are `hexagon_locallyTreeAt` and `hexagon_opposite_far_conflict` in [SeventhPassExamples.lean](Se20Insertion/SeventhPassExamples.lean). The map-free theorem below uses the genuine girth assumption `7 ≤ G.egirth`, together with **FourRegular G**. It does not claim that the old predicate implies the pattern. Neither that predicate nor any existing theorem statement was changed. Global four-regularity is an explicit scope restriction of this bridge; a separate bridge for arbitrary maximum-degree-four graphs, padding missing positions, is not provided.

**P4 is missing a hypothesis in the manuscript's abbreviated sentence.** The source [gap report, P4](../se20-gap/REPORT.md) states: no completion by filling after at most two hole moves. It also specifies **static** singleton distance, computed in the original colouring. Without the obstruction premise even a single edge, with one endpoint coloured 0 and the other uncoloured, is a counterexample: the one-step target lacks colour 1. `raw_P4_needs_obstruction` checks this example. `propositionP4` below includes the source hypothesis explicitly. It asserts saturation in the original colouring, not saturation at arbitrary depth or along arbitrary dynamically changing walks.

**Inventory from the requested scan, before the new proof results.** I scanned all of manuscript sections 7 and 8.2 for headings tagged `【证明】` without an associated Lean name, and checked their surrounding text and current sources. The original manuscript is not edited.

| Location / claim | Status after this pass |
| --- | --- |
| §7.2, 11.35, unrestricted star insertion implies the strong 20-colouring theorem | New explicit extension-form theorem `strongColourable_of_unrestricted_star`. The interface records existence of the extended colouring, like the existing `StarInsertion`; it does not record a Kempe-swap history. The manuscript's operational premise implies this premise. |
| §7.3, existential state-neighbour equivalence for 11.9 | Proved as `conj119_iff_hole_neighbour`. |
| §7.3, universal form / no stuck-to-stuck move | Proved locally for all legal moves as `all_holeMoves_not_stuck_iff`, using the same exact one-move iff. |
| §7.5, P3, static conditions plus a reachable exposed configuration need not imply insertion | The seven-vertex, three-colour example **and its twenty-colour join-with-K17 lift** are checked, including saturation, singleton closure, the static double, the two actual moves, destruction of the double, and impossibility of a full colouring. |
| §7.5, P4, saturation through two static steps | Proved with the source report's missing obstruction hypothesis; failure at depth three is also checked with twenty colours. |
| §7.5, P7, class-size square potential | Exact gain, extremal inequality, equal-size balance, hole-move invariance, and existence of a maximum in the actual reachable class are proved. |
| §7.6, 11.27, strong form of the fragmentation implication | Proved explicitly as `strongColourable_of_conj1126Strong`; the conjecture remains a premise. |
| §7.7, P6, the C/L/U family with a permanently bad colour pair | Not formalized. |
| §7.7, numerical long-chain corollary: 103 at h, average 27 at its neighbours, and 84 at single members | Not added as named count corollaries. The earlier tangling and 87-edge bounds remain available. |
| §8.2.1, conditional Proposition 1.1: nine triangle-free degree-two classes and girth ≥96 imply 19 colours | Not formalized; this includes the independent-transversal step. |
| §8.2.1, dense-side assertion for degree deficit ≥3, including exclusion of compact triangles | Not formalized. |
| §8.2.2, incident-palette characterization | Proved as `strong_iff_incident_palettes`, for arbitrary graphs and arbitrary colour types. |
| §8.2.2, locally injective pullback | Already proved as `strongColourable_pullback` in `Covering.lean`. This is a missing manuscript annotation, not a missing Lean theorem. |

The explicitly requested 11.40(5) and map construction for 11.5 were also checked despite their partially annotated headings. Other displayed proofs in those sections already name Lean results. Untagged discussion, computational evidence, and conjectures were not reclassified as proved statements. The untagged numerical generalizations in §8.2.1 are not claimed here.

**What the list-colouring work actually establishes.** The colour type in the new general list lemmas is any nonempty type; individual lists are finite. `DegreeList.ColourableOn H L S` means an actual colour function on vertices that belongs to each list on S and is proper on every ambient H-edge with both ends in S.

1. `colourable_of_degenerate`: greedy induction whenever each nonempty induced subset has a vertex with more available list colours than neighbours in that subset.
2. `colourable_of_one_slack`: a finite connected graph with lists at least its degrees is list-colourable if one list is strictly larger. Consequently an uncolourable such assignment has every list exactly the vertex degree (`bad_degree_lists_tight`).
3. `colourable_of_list_difference`: if v is adjacent to w, deletion of v leaves a connected graph, and some colour belongs to L(v) but not L(w), precolour v with that colour and use the resulting slack at w. Thus a bad assignment satisfies L(v) ⊆ L(w) at every such non-cut vertex. If every vertex deletion is connected, adjacent lists agree; connectivity then makes every list the same and the graph regular (`bad_noncut_uniform`).
4. `colourable_of_independent_precolour`: precolour an independent set B with one colour common to all its lists. If the remaining induced graph is connected and a remaining vertex has at least two neighbours in B, residual degree lists have strict slack there and the colouring extends.
5. `colourable_of_nonseparating_pair`: the preceding argument specialized to two distinct nonadjacent vertices with a common neighbour and connected remainder. This is the actual colouring argument for a non-separating pair. **Its existence is an explicit hypothesis of this lemma; it is not a finished Gallai theorem.**

Files: [DegreeListTools.lean](Se20Insertion/DegreeListTools.lean), [DegreeListReduction.lean](Se20Insertion/DegreeListReduction.lean), [NonseparatingPair.lean](Se20Insertion/NonseparatingPair.lean). These use finite-set induction, induced-degree identities, and propagation along graph walks. No external classification or enumeration is used. `critical_low_degree_list_obstruction` is unchanged. The remaining structural work is to establish the appropriate pair/exception classification for the relevant blocks and the blockwise reduction, including the clique and odd-cycle exceptions. Therefore **11.40(5) is still not proved**.

**11.5 without a supplied map.** [PatternGeometry.lean](Se20Insertion/PatternGeometry.lean) constructs, for a finite four-regular G of girth at least seven and any edge e,

```text
∃ ι : TreePattern.Position ≃ ↥(conflicts G e),
  ∀ x y, (L2 G).Adj (ι x).val (ι y).val → TreePattern.graph.Adj x y.
```

It enumerates the actual three children other than a vertex's parent. The rim decomposition proves surjectivity onto the conflict neighbourhood; the already checked 24-edge cardinality makes it bijective. Triangle through hexagon exclusions prove the adjacency domination. [GeometricLoopChains.lean](Se20Insertion/GeometricLoopChains.lean), `sixty_six_chains_of_girth`, then gives at least **66 distinct unordered colour pairs**, each with distinct single representatives, nonadjacent to one another and in the same Kempe component. All pattern data and sixteen-single selection are constructed. The pre-existing generic internal-chain avoidance theorem in `ShellChains.lean` remains available; the new conclusion follows the existing `sixty_six_chains` interface and does not add a separately packaged walk/avoidance witness.

**P4 and the state-neighbour equivalence.** [TwoStepSaturation.lean](Se20Insertion/TwoStepSaturation.lean) defines `HoleFillWithin φ e k` by filling with a free colour now or making one legal singleton hole move and continuing with budget k−1. `HoleFillWithin.insert` proves that every such repair produces a proper colouring of the extended domain. Thus `¬ HoleFillWithin φ e 2` is the exact bounded obstruction, not global uncolourability. `StaticWithinTwo φ e x` means x=e, a static single target of e, or a static single target of such a target. `propositionP4` proves that every such x sees every colour other than its own; if x is uncoloured it sees all twenty. The theorem works on arbitrary conflict graphs and finite colouring domains, without a finite ambient vertex-type or one-hole hypothesis.

The depth-three limitation is also checked in `StaticDynamicExample.lean`. A second colouring of the twenty-colour lifted graph has the static singleton path 6→2→1→0, with three distinct donor colours 2,1,0, and vertex 0 originally lacks colour 2 (`depth_three_static`). No bounded hole repair can complete it (`depth_three_no_repair`), because the whole graph is not 20-colourable. The three moves really execute, and the recoloured hub supplies colour 2 at vertex 0 afterwards (`depth_three_missing_colour_changed`). This is a twenty-colour version of the source report's wheel obstruction, with the same extra vertex 5 retained and coloured compatibly.

[HoleStateEquivalence.lean](Se20Insertion/HoleStateEquivalence.lean) proves that, for a stuck uncoloured e and a single p-member f,

```text
¬ (φ.holeMove hs).Stuck f
  ↔ ∃ a b, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b.
```

The proof uses unchanged non-p colour classes, the existing blockedness theorem, and the existing theorem excluding pairs involving p. `conj119_iff_hole_neighbour` quantifies over exactly the finite graph models, degree bound, domains and holes of the unchanged `Conj119`. Neither equivalent conjecture is asserted. The universal version quantifies over every legal move. The earlier reverse-move theorem still identifies colourings on their coloured domain; unused values outside that domain have no mathematical meaning. No claim of literal symmetry of raw colour functions with those unused values is made.

**P7 uses actual finite class counts and actual reachable states.** Define nₐ = |{x∈F : φ(x)=a}|, Φ=Σₐnₐ², and, for a closed two-colour set S, d=|S∩colour⁻¹(a)|−|S∩colour⁻¹(b)|. Counts and differences are cast to integers. [ClassSquarePotential.lean](Se20Insertion/ClassSquarePotential.lean) proves

```text
Φ(swap S) − Φ(φ) = 2*d*(d − (nₐ − n_b)).
```

If the swap cannot increase Φ and nₐ≥n_b, then 0≤d≤nₐ−n_b. Equal-size classes have balanced components. Hole moves preserve Φ. [PotentialReachability.lean](Se20Insertion/PotentialReachability.lean) defines marked-hole states and steps consisting of legal hole moves or swaps of actual nonempty Kempe components. For finite W, `exists_reachable_maximum` chooses a maximum reachable from the supplied initial state and proves that every state reachable from that maximum has no larger potential. `maximal_component_imbalance` applies the inequality to every actual component there. No uncolourability assumption is needed for this extremal statement.

**Additional checked claims.** [IncidentPalettes.lean](Se20Insertion/IncidentPalettes.lean) proves that a given edge-colour function is strong iff it is proper at each incident star and the palettes at the ends of every edge intersect in exactly that edge's colour. [RemainingImplications.lean](Se20Insertion/RemainingImplications.lean) adds the explicit 11.35 extension implication and the strong 11.27 implication. [StaticDynamicExample.lean](Se20Insertion/StaticDynamicExample.lean) checks the seven-vertex P3 example with colours renumbered 0,1,2, including the legal moves 6→1→0 and the failure of the old double after those moves. It also constructs the twenty-colour lift on `Fin 7 ⊕ Fin 17`, of maximum degree at most 23. `propositionP3` states saturation, singleton closure, the static double, and non-20-colourability together; `lifted_first_single`, `lifted_second_single`, and `lifted_transport_destroyed` check the actual moves and destruction. To prove non-20-colourability, the new clique and the hub consume eighteen distinct colours, leaving at most two colours for the old five-cycle, a contradiction. This is a counterexample for arbitrary conflict graphs, not a claimed counterexample within the requested high-girth L² geometry. Finite facts use kernel-checked `decide` and `omega`; no native evaluator is used as a proof oracle.

**Exact declarations.** The following is the actual `#check` output for all 108 new audited declarations, also saved in [STATEMENTS7.txt](STATEMENTS7.txt). Definitions have their bodies in the linked source modules; [DECLARATIONS7.txt](DECLARATIONS7.txt) is the inventory and [Print7.lean](Print7.lean) regenerates the statements.

```text
Se20Insertion.PartialColouring.holeMove_same_other_classes.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) : φ.SameYClasses (φ.holeMove hs) (Finset.univ.erase p)
Se20Insertion.PartialColouring.holeMove_separable_iff.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f v : W} {p a b : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) (ha : a ≠ p) (hb : b ≠ p) : (φ.holeMove hs).Separable v a b ↔ φ.Separable v a b
Se20Insertion.PartialColouring.separable_comm.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (v : W) (a b : Se20Insertion.Colour) : φ.Separable v a b ↔ φ.Separable v b a
Se20Insertion.PartialColouring.holeMove_not_stuck_iff.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) (hst : φ.Stuck e) : ¬(φ.holeMove hs).Stuck f ↔ ∃ a b, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b
Se20Insertion.PartialColouring.all_holeMoves_not_stuck_iff.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e : W} (he : e ∉ F) (hst : φ.Stuck e) :
  (∀ (p : Se20Insertion.Colour) (f : W) (hs : φ.Single e p f), ¬(φ.holeMove hs).Stuck f) ↔
    ∀ (p : Se20Insertion.Colour) (f : W), φ.Single e p f → ∃ a b, a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b
Se20Insertion.Conj119HoleNeighbour : Prop
Se20Insertion.conj119_iff_hole_neighbour : Se20Insertion.Conj119 ↔ Se20Insertion.Conj119HoleNeighbour
Se20Insertion.PartialColouring.HoleFillWithin.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W} :
  Se20Insertion.PartialColouring H F → W → ℕ → Prop
Se20Insertion.PartialColouring.HoleFillWithin.insert.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} {φ : Se20Insertion.PartialColouring H F} {e : W} {k : ℕ} (h : φ.HoleFillWithin e k) :
  Nonempty (Se20Insertion.PartialColouring H (Insert.insert e F))
Se20Insertion.PartialColouring.holeFillWithin_blocked.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e : W} {k : ℕ} (hn : ¬φ.HoleFillWithin e k)
  (c : Se20Insertion.Colour) : ∃ x, φ.Neighbour e c x
Se20Insertion.PartialColouring.holeMove_single_other.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f g v : W} {p q : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) (hq : q ≠ p) (ht : φ.Single v q g) : (φ.holeMove hs).Single v q g
Se20Insertion.PartialColouring.holeMove_free_other.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f v : W} {p c : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) (hc : c ≠ p) (hf : φ.Free v c) : (φ.holeMove hs).Free v c
Se20Insertion.PartialColouring.one_step_static_saturated.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} (he : e ∉ F)
  (hn : ¬φ.HoleFillWithin e 2) (hs : φ.Single e p f) (c : Se20Insertion.Colour) : c ≠ p → ∃ x, φ.Neighbour f c x
Se20Insertion.PartialColouring.two_step_static_saturated.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f g : W} {p q : Se20Insertion.Colour} (he : e ∉ F)
  (hn : ¬φ.HoleFillWithin e 2) (hs : φ.Single e p f) (ht : φ.Single f q g) (c : Se20Insertion.Colour) :
  c ≠ q → ∃ x, φ.Neighbour g c x
Se20Insertion.PartialColouring.StaticWithinTwo.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (e x : W) : Prop
Se20Insertion.PartialColouring.propositionP4.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {e : W} (he : e ∉ F) (hn : ¬φ.HoleFillWithin e 2) {x : W}
  (hx : φ.StaticWithinTwo e x) (c : Se20Insertion.Colour) : x ∉ F ∨ c ≠ φ.colour x → ∃ y, φ.Neighbour x c y
Se20Insertion.PartialColouring.classSize.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (a : Se20Insertion.Colour) : ℤ
Se20Insertion.PartialColouring.classSquare.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) : ℤ
Se20Insertion.PartialColouring.imbalance.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (a b : Se20Insertion.Colour) (S : Set W) : ℤ
Se20Insertion.PartialColouring.classSize_swap_left.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b : Se20Insertion.Colour} (hab : a ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) : (φ.swap a b S hS).classSize a = φ.classSize a - φ.imbalance a b S
Se20Insertion.PartialColouring.classSize_swap_right.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b : Se20Insertion.Colour} (hab : a ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) : (φ.swap a b S hS).classSize b = φ.classSize b + φ.imbalance a b S
Se20Insertion.PartialColouring.classSize_swap_other.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b c : Se20Insertion.Colour} (ha : c ≠ a) (hb : c ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) : (φ.swap a b S hS).classSize c = φ.classSize c
Se20Insertion.PartialColouring.classSquare_swap.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b : Se20Insertion.Colour} (hab : a ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) :
  (φ.swap a b S hS).classSquare - φ.classSquare =
    2 * φ.imbalance a b S * (φ.imbalance a b S - (φ.classSize a - φ.classSize b))
Se20Insertion.PartialColouring.propositionP7.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b : Se20Insertion.Colour} (hab : a ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) (hmax : (φ.swap a b S hS).classSquare ≤ φ.classSquare)
  (hsize : φ.classSize b ≤ φ.classSize a) : 0 ≤ φ.imbalance a b S ∧ φ.imbalance a b S ≤ φ.classSize a - φ.classSize b
Se20Insertion.PartialColouring.equal_classes_balanced.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {a b : Se20Insertion.Colour} (hab : a ≠ b) {S : Set W}
  (hS : φ.KempeClosed a b S) (hmax : (φ.swap a b S hS).classSquare ≤ φ.classSquare)
  (hsize : φ.classSize a = φ.classSize b) : φ.imbalance a b S = 0
Se20Insertion.PartialColouring.holeMove_classSquare.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  [DecidableEq W] (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} (he : e ∉ F)
  (hs : φ.Single e p f) : (φ.holeMove hs).classSquare = φ.classSquare
Se20Insertion.HoleState.{u_1} {W : Type u_1} (H : SimpleGraph W) : Type u_1
Se20Insertion.HoleState.make.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (e : W) (he : e ∉ F) : Se20Insertion.HoleState H
Se20Insertion.HoleState.potential.{u_1} {W : Type u_1} {H : SimpleGraph W} (s : Se20Insertion.HoleState H) : ℤ
Se20Insertion.HoleState.Step.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} :
  Se20Insertion.HoleState H → Se20Insertion.HoleState H → Prop
Se20Insertion.HoleState.Reachable.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  (s t : Se20Insertion.HoleState H) : Prop
Se20Insertion.HoleState.exists_reachable_maximum.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} [Finite W]
  (s : Se20Insertion.HoleState H) :
  ∃ t, s.Reachable t ∧ ∀ (z : Se20Insertion.HoleState H), t.Reachable z → z.potential ≤ t.potential
Se20Insertion.HoleState.maximal_component_imbalance.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (e : W) (he : e ∉ F)
  (hmax :
    ∀ (z : Se20Insertion.HoleState H), (Se20Insertion.HoleState.make φ e he).Reachable z → z.potential ≤ φ.classSquare)
  {a b : Se20Insertion.Colour} (hab : a ≠ b) (hsize : φ.classSize b ≤ φ.classSize a) (x : W)
  (hx : x ∈ φ.Bicoloured a b) :
  0 ≤ φ.imbalance a b {y | φ.SameComponent a b x y} ∧
    φ.imbalance a b {y | φ.SameComponent a b x y} ≤ φ.classSize a - φ.classSize b
Se20Insertion.TreePattern.opposite_near_far_not_close.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  (hg : 7 ≤ G.egirth) {u v x y z : V} (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y) (hyz : G.Adj y z)
  (hxv : x ≠ v) (hyu : y ≠ u) (hzv : z ≠ v) : ¬Se20Insertion.GirthGeometry.Close u x y z
Se20Insertion.TreePattern.same_side_far_close.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V} (hg : 7 ≤ G.egirth)
  {u x y z t : V} (hux : G.Adj u x) (huy : G.Adj u y) (hxz : G.Adj x z) (hyt : G.Adj y t) (hzu : z ≠ u) (htu : t ≠ u)
  (hc : Se20Insertion.GirthGeometry.Close x z y t) : x = y
Se20Insertion.TreePattern.opposite_far_not_close.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  (hg : 7 ≤ G.egirth) {u v x y z t : V} (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y) (hxz : G.Adj x z)
  (hyt : G.Adj y t) (hxv : x ≠ v) (hyu : y ≠ u) (hzu : z ≠ u) (htv : t ≠ v) : ¬Se20Insertion.GirthGeometry.Close x z y t
Se20Insertion.TreePattern.children.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  (hreg : Se20Insertion.FourRegular G) (a b : V) (hab : G.Adj a b) : Fin 3 ≃ ↥((G.neighborFinset a).erase b)
Se20Insertion.TreePattern.exists_geometric_label.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  (hreg : Se20Insertion.FourRegular G) (hg : 7 ≤ G.egirth) (e : ↑G.edgeSet) :
  ∃ ι,
    ∀ (x y : Se20Insertion.TreePattern.Position),
      (Se20Insertion.L2 G).Adj ↑(ι x) ↑(ι y) → Se20Insertion.TreePattern.graph.Adj x y
Se20Insertion.TreePattern.sixty_six_chains_of_girth.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  (hreg : Se20Insertion.FourRegular G) (hg : 7 ≤ G.egirth) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e : ↑G.edgeSet} (hstop : φ.Stuck e) :
  ∃ P,
    66 ≤ P.card ∧
      ∀ t ∈ P,
        ∃ a b f g,
          t = s(a, b) ∧
            a ≠ b ∧ φ.Single e a f ∧ φ.Single e b g ∧ ¬(Se20Insertion.L2 G).Adj f g ∧ φ.SameComponent a b f g
Se20Insertion.incidentPalette.{u_1, u_2} {V : Type u_1} {C : Type u_2} (G : SimpleGraph V) (c : ↑G.edgeSet → C)
  (u : V) : Set C
Se20Insertion.IncidentProper.{u_1, u_2} {V : Type u_1} {C : Type u_2} (G : SimpleGraph V) (c : ↑G.edgeSet → C) : Prop
Se20Insertion.strong_iff_incident_palettes.{u_1, u_2} {V : Type u_1} {C : Type u_2} (G : SimpleGraph V)
  (c : ↑G.edgeSet → C) :
  (∀ (e f : ↑G.edgeSet), (Se20Insertion.L2 G).Adj e f → c e ≠ c f) ↔
    Se20Insertion.IncidentProper G c ∧
      ∀ (u v : V) (huv : G.Adj u v),
        Se20Insertion.incidentPalette G c u ∩ Se20Insertion.incidentPalette G c v = {c (Se20Insertion.edge G huv)}
Se20Insertion.DegreeList.ColourableOn.{u_1, u_2} {W : Type u_1} {C : Type u_2} (H : SimpleGraph W) (L : W → Finset C)
  (S : Finset W) : Prop
Se20Insertion.DegreeList.colourable_of_degenerate.{u_1, u_2} {W : Type u_1} {C : Type u_2} [DecidableEq W] [Nonempty C]
  (H : SimpleGraph W) (L : W → Finset C) (S : Finset W)
  (hd : ∀ T ⊆ S, T.Nonempty → ∃ x ∈ T, (Finset.filter (H.Adj x) T).card < (L x).card) :
  Se20Insertion.DegreeList.ColourableOn H L S
Se20Insertion.DegreeList.colourable_of_one_slack.{u_1, u_2} {W : Type u_1} {C : Type u_2} [DecidableEq W] [Nonempty C]
  (H : SimpleGraph W) [Fintype W] (L : W → Finset C) (hconn : H.Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (r : W) (hr : H.degree r < (L r).card) : Se20Insertion.DegreeList.ColourableOn H L Finset.univ
Se20Insertion.DegreeList.bad_degree_lists_tight.{u_1, u_2} {W : Type u_1} {C : Type u_2} [DecidableEq W] [Nonempty C]
  (H : SimpleGraph W) [Fintype W] (L : W → Finset C) (hconn : H.Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (hbad : ¬Se20Insertion.DegreeList.ColourableOn H L Finset.univ) (x : W) : (L x).card = H.degree x
Se20Insertion.DegreeList.degree_delete.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (v : W)
  (x : { x // x ≠ v }) : ((SimpleGraph.induce {x | x ≠ v} H).degree x + if H.Adj (↑x) v then 1 else 0) = H.degree ↑x
Se20Insertion.DegreeList.colourable_of_list_difference.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W]
  [DecidableEq W] [Nonempty C] (H : SimpleGraph W) (L : W → Finset C) {v w : W} (hvw : H.Adj v w)
  (hconn : (SimpleGraph.induce {x | x ≠ v} H).Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card) {a : C}
  (hav : a ∈ L v) (haw : a ∉ L w) : Se20Insertion.DegreeList.ColourableOn H L Finset.univ
Se20Insertion.DegreeList.bad_lists_subset_at_noncut.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W] [DecidableEq W]
  [Nonempty C] (H : SimpleGraph W) (L : W → Finset C) {v w : W} (hvw : H.Adj v w)
  (hconn : (SimpleGraph.induce {x | x ≠ v} H).Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (hbad : ¬Se20Insertion.DegreeList.ColourableOn H L Finset.univ) : L v ⊆ L w
Se20Insertion.DegreeList.bad_lists_equal_on_edges.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W] [DecidableEq W]
  [Nonempty C] (H : SimpleGraph W) (L : W → Finset C)
  (hdelete : ∀ (v : W), (SimpleGraph.induce {x | x ≠ v} H).Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (hbad : ¬Se20Insertion.DegreeList.ColourableOn H L Finset.univ) {v w : W} (hvw : H.Adj v w) : L v = L w
Se20Insertion.DegreeList.bad_noncut_uniform.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W] [DecidableEq W]
  [Nonempty C] (H : SimpleGraph W) (L : W → Finset C) (hconn : H.Connected)
  (hdelete : ∀ (v : W), (SimpleGraph.induce {x | x ≠ v} H).Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (hbad : ¬Se20Insertion.DegreeList.ColourableOn H L Finset.univ) (r x : W) : L x = L r ∧ H.degree x = (L r).card
Se20Insertion.DegreeList.degree_delete_set.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
  (B : Finset W) (x : { x // x ∉ B }) :
  (SimpleGraph.induce {x | x ∉ B} H).degree x + (H.neighborFinset ↑x ∩ B).card = H.degree ↑x
Se20Insertion.DegreeList.colourable_of_independent_precolour.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W]
  [DecidableEq W] [Nonempty C] (H : SimpleGraph W) (L : W → Finset C) (B : Finset W)
  (hconn : (SimpleGraph.induce {x | x ∉ B} H).Connected) (hd : ∀ (x : W), H.degree x ≤ (L x).card)
  (hB : ∀ x ∈ B, ∀ y ∈ B, ¬H.Adj x y) {a : C} (ha : ∀ x ∈ B, a ∈ L x) (r : { x // x ∉ B })
  (hr : 2 ≤ (H.neighborFinset ↑r ∩ B).card) : Se20Insertion.DegreeList.ColourableOn H L Finset.univ
Se20Insertion.DegreeList.colourable_of_nonseparating_pair.{u_1, u_2} {W : Type u_1} {C : Type u_2} [Fintype W]
  [DecidableEq W] [Nonempty C] (H : SimpleGraph W) (L : W → Finset C) {u v r : W} (huv : u ≠ v) (hn : ¬H.Adj u v)
  (hru : H.Adj r u) (hrv : H.Adj r v) (hconn : (SimpleGraph.induce {x | x ∉ {u, v}} H).Connected)
  (hd : ∀ (x : W), H.degree x ≤ (L x).card) {a : C} (hau : a ∈ L u) (hav : a ∈ L v) :
  Se20Insertion.DegreeList.ColourableOn H L Finset.univ
Se20Insertion.UnrestrictedStarInsertion : Prop
Se20Insertion.strongColourable_of_unrestricted_star.{u_1} (h : Se20Insertion.UnrestrictedStarInsertion) {V : Type u_1}
  [Fintype V] (G : SimpleGraph V) (hd : Se20Insertion.MaxDegreeFour G) : Se20Insertion.StrongColourable G 20
Se20Insertion.Conj1126Strong : Prop
Se20Insertion.conj1126Weak_of_strong (h : Se20Insertion.Conj1126Strong) : Se20Insertion.Conj1126Weak
Se20Insertion.strongColourable_of_conj1126Strong.{u_1} (h : Se20Insertion.Conj1126Strong) {V : Type u_1} [Fintype V]
  (G : SimpleGraph V) (hd : Se20Insertion.MaxDegreeFour G) : Se20Insertion.StrongColourable G 20
Se20Insertion.SeventhPassExamples.hexagon : SimpleGraph (Fin 6)
Se20Insertion.SeventhPassExamples.hexagon_locallyTreeAt :
  Se20Insertion.LocallyTreeAt Se20Insertion.SeventhPassExamples.hexagon 0 1
Se20Insertion.SeventhPassExamples.farLeft : ↑Se20Insertion.SeventhPassExamples.hexagon.edgeSet
Se20Insertion.SeventhPassExamples.farRight : ↑Se20Insertion.SeventhPassExamples.hexagon.edgeSet
Se20Insertion.SeventhPassExamples.hexagon_opposite_far_conflict :
  Se20Insertion.SeventhPassExamples.hexagon.Adj 0 5 ∧
    Se20Insertion.SeventhPassExamples.hexagon.Adj 1 2 ∧
      (Se20Insertion.L2 Se20Insertion.SeventhPassExamples.hexagon).Adj Se20Insertion.SeventhPassExamples.farLeft
        Se20Insertion.SeventhPassExamples.farRight
Se20Insertion.SeventhPassExamples.oneEdge : SimpleGraph (Fin 2)
Se20Insertion.SeventhPassExamples.oneColoured :
  Se20Insertion.PartialColouring Se20Insertion.SeventhPassExamples.oneEdge {1}
Se20Insertion.SeventhPassExamples.raw_P4_needs_obstruction :
  Se20Insertion.SeventhPassExamples.oneColoured.Single 0 0 1 ∧ Se20Insertion.SeventhPassExamples.oneColoured.Free 1 1
Se20Insertion.StaticDynamicExample.graph : SimpleGraph (Fin 7)
Se20Insertion.StaticDynamicExample.colour : Fin 7 → Fin 3
Se20Insertion.StaticDynamicExample.domain : Finset (Fin 7)
Se20Insertion.StaticDynamicExample.colouring :
  Se20Insertion.Parametric.PartialColouring 3 Se20Insertion.StaticDynamicExample.graph
    Se20Insertion.StaticDynamicExample.domain
Se20Insertion.StaticDynamicExample.saturated (x : Fin 7) (a : Fin 3) :
  x = 6 ∨ a ≠ Se20Insertion.StaticDynamicExample.colour x →
    ∃ y, Se20Insertion.StaticDynamicExample.colouring.Neighbour x a y
Se20Insertion.StaticDynamicExample.static_double :
  Se20Insertion.StaticDynamicExample.colouring.Single 0 1 1 ∧
    Se20Insertion.StaticDynamicExample.colouring.Single 2 1 1 ∧
      Se20Insertion.StaticDynamicExample.colouring.Single 1 2 2 ∧ ¬Se20Insertion.StaticDynamicExample.graph.Adj 0 2
Se20Insertion.StaticDynamicExample.first_single : Se20Insertion.StaticDynamicExample.colouring.Single 6 1 1
Se20Insertion.StaticDynamicExample.afterFirst :
  Se20Insertion.Parametric.PartialColouring 3 Se20Insertion.StaticDynamicExample.graph
    (Insert.insert 6 (Se20Insertion.StaticDynamicExample.domain.erase 1))
Se20Insertion.StaticDynamicExample.second_single : Se20Insertion.StaticDynamicExample.afterFirst.Single 1 0 0
Se20Insertion.StaticDynamicExample.afterSecond :
  Se20Insertion.Parametric.PartialColouring 3 Se20Insertion.StaticDynamicExample.graph
    (Insert.insert 1 ((Insert.insert 6 (Se20Insertion.StaticDynamicExample.domain.erase 1)).erase 0))
Se20Insertion.StaticDynamicExample.transported_double_destroyed :
  6 ∉ Se20Insertion.StaticDynamicExample.domain ∧
    1 ∉ Insert.insert 6 (Se20Insertion.StaticDynamicExample.domain.erase 1) ∧
      Se20Insertion.StaticDynamicExample.afterSecond.colour 6 = 1 ∧
        Se20Insertion.StaticDynamicExample.afterSecond.colour 1 = 0 ∧
          ¬Se20Insertion.StaticDynamicExample.afterSecond.Single 2 1 1
Se20Insertion.StaticDynamicExample.not_three_colourable : ¬Se20Insertion.StaticDynamicExample.graph.Colorable 3
Se20Insertion.StaticDynamicExample.liftedGraph : SimpleGraph (Fin 7 ⊕ Fin 17)
Se20Insertion.StaticDynamicExample.liftedColour : Fin 7 ⊕ Fin 17 → Se20Insertion.Colour
Se20Insertion.StaticDynamicExample.liftedDomain : Finset (Fin 7 ⊕ Fin 17)
Se20Insertion.StaticDynamicExample.liftedColouring :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    Se20Insertion.StaticDynamicExample.liftedDomain
Se20Insertion.StaticDynamicExample.lifted_saturated :
  Se20Insertion.StaticDynamicExample.liftedColouring.SaturatedOn Finset.univ
Se20Insertion.StaticDynamicExample.lifted_single_closed :
  Se20Insertion.StaticDynamicExample.liftedColouring.SingleClosed Finset.univ
Se20Insertion.StaticDynamicExample.lifted_double :
  Se20Insertion.StaticDynamicExample.liftedColouring.DoubleHoleConfig (Sum.inl 0) (Sum.inl 1) (Sum.inl 2)
Se20Insertion.StaticDynamicExample.lifted_first_single :
  Se20Insertion.StaticDynamicExample.liftedColouring.Single (Sum.inl 6) 1 (Sum.inl 1)
Se20Insertion.StaticDynamicExample.liftedAfterFirst :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    (Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 1)))
Se20Insertion.StaticDynamicExample.lifted_second_single :
  Se20Insertion.StaticDynamicExample.liftedAfterFirst.Single (Sum.inl 1) 0 (Sum.inl 0)
Se20Insertion.StaticDynamicExample.liftedAfterSecond :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    (Insert.insert (Sum.inl 1)
      ((Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 1))).erase
        (Sum.inl 0)))
Se20Insertion.StaticDynamicExample.lifted_transport_destroyed :
  Sum.inl 6 ∉ Se20Insertion.StaticDynamicExample.liftedDomain ∧
    Sum.inl 1 ∉ Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 1)) ∧
      Sum.inl 0 ∉
          Insert.insert (Sum.inl 1)
            ((Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 1))).erase
              (Sum.inl 0)) ∧
        ¬Se20Insertion.StaticDynamicExample.liftedAfterSecond.Single (Sum.inl 2) 1 (Sum.inl 1)
Se20Insertion.StaticDynamicExample.five_cycle_not_two.{u_1} {C : Type u_1} [DecidableEq C] (A : Finset C)
  (hA : A.card ≤ 2) (c : Fin 5 → C) (hc : ∀ (i : Fin 5), c i ∈ A) (h01 : c 0 ≠ c 1) (h12 : c 1 ≠ c 2) (h23 : c 2 ≠ c 3)
  (h34 : c 3 ≠ c 4) (h40 : c 4 ≠ c 0) : False
Se20Insertion.StaticDynamicExample.lifted_not_twenty_colourable :
  ¬Se20Insertion.StaticDynamicExample.liftedGraph.Colorable 20
Se20Insertion.StaticDynamicExample.lifted_degree_bound (x : Fin 7 ⊕ Fin 17) :
  Se20Insertion.StaticDynamicExample.liftedGraph.degree x ≤ 23
Se20Insertion.StaticDynamicExample.propositionP3 :
  Se20Insertion.StaticDynamicExample.liftedColouring.SaturatedOn Finset.univ ∧
    Se20Insertion.StaticDynamicExample.liftedColouring.SingleClosed Finset.univ ∧
      Se20Insertion.StaticDynamicExample.liftedColouring.DoubleHoleConfig (Sum.inl 0) (Sum.inl 1) (Sum.inl 2) ∧
        ¬Se20Insertion.StaticDynamicExample.liftedGraph.Colorable 20
Se20Insertion.StaticDynamicExample.depthThreeColour : Fin 7 ⊕ Fin 17 → Se20Insertion.Colour
Se20Insertion.StaticDynamicExample.depthThreeColouring :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    Se20Insertion.StaticDynamicExample.liftedDomain
Se20Insertion.StaticDynamicExample.depth_three_static :
  Se20Insertion.StaticDynamicExample.depthThreeColouring.Single (Sum.inl 6) 2 (Sum.inl 2) ∧
    Se20Insertion.StaticDynamicExample.depthThreeColouring.Single (Sum.inl 2) 1 (Sum.inl 1) ∧
      Se20Insertion.StaticDynamicExample.depthThreeColouring.Single (Sum.inl 1) 0 (Sum.inl 0) ∧
        Se20Insertion.StaticDynamicExample.depthThreeColouring.Free (Sum.inl 0) 2
Se20Insertion.StaticDynamicExample.depth_three_no_repair (k : ℕ) :
  ¬Se20Insertion.StaticDynamicExample.depthThreeColouring.HoleFillWithin (Sum.inl 6) k
Se20Insertion.StaticDynamicExample.depthAfterFirst :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    (Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 2)))
Se20Insertion.StaticDynamicExample.depth_second_single :
  Se20Insertion.StaticDynamicExample.depthAfterFirst.Single (Sum.inl 2) 1 (Sum.inl 1)
Se20Insertion.StaticDynamicExample.depthAfterSecond :
  Se20Insertion.PartialColouring Se20Insertion.StaticDynamicExample.liftedGraph
    (Insert.insert (Sum.inl 2)
      ((Insert.insert (Sum.inl 6) (Se20Insertion.StaticDynamicExample.liftedDomain.erase (Sum.inl 2))).erase
        (Sum.inl 1)))
Se20Insertion.StaticDynamicExample.depth_third_single :
  Se20Insertion.StaticDynamicExample.depthAfterSecond.Single (Sum.inl 1) 0 (Sum.inl 0)
Se20Insertion.StaticDynamicExample.depth_three_missing_colour_changed :
  (Se20Insertion.StaticDynamicExample.depthAfterSecond.holeMove
        Se20Insertion.StaticDynamicExample.depth_third_single).Neighbour
    (Sum.inl 0) 2 (Sum.inl 6)
Se20Insertion.PartialColouring.HoleFillWithin.fill.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (e : W) (k : ℕ) {c : Se20Insertion.Colour} (hc : φ.Free e c) :
  φ.HoleFillWithin e k
Se20Insertion.PartialColouring.HoleFillWithin.move.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} {k : ℕ} (he : e ∉ F)
  (hs : φ.Single e p f) (ht : (φ.holeMove hs).HoleFillWithin f k) : φ.HoleFillWithin e (k + 1)
Se20Insertion.HoleState.Step.hole.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {e f : W} {p : Se20Insertion.Colour} (he : e ∉ F) (hs : φ.Single e p f) :
  (Se20Insertion.HoleState.make φ e he).Step (Se20Insertion.HoleState.make (φ.holeMove hs) f ⋯)
Se20Insertion.HoleState.Step.kempe.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (e : W) (he : e ∉ F) (a b : Se20Insertion.Colour) (hab : a ≠ b) (x : W)
  (hx : x ∈ φ.Bicoloured a b) :
  (Se20Insertion.HoleState.make φ e he).Step
    (Se20Insertion.HoleState.make (φ.swap a b {y | φ.SameComponent a b x y} ⋯) e he)
```

**Actual axiom output for the additions.** The complete audit, including earlier passes, is [AXIOMS7.txt](AXIOMS7.txt); the following is [AXIOMS7_ADDITIONS.txt](AXIOMS7_ADDITIONS.txt).

```text
'Se20Insertion.PartialColouring.holeMove_same_other_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_separable_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.separable_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_not_stuck_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.all_holeMoves_not_stuck_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.Conj119HoleNeighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.conj119_iff_hole_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.HoleFillWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.HoleFillWithin.insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeFillWithin_blocked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_single_other' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_free_other' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.one_step_static_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.two_step_static_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.StaticWithinTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.propositionP4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSize' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.imbalance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSize_swap_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSize_swap_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSize_swap_other' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.classSquare_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.propositionP7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.equal_classes_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_classSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.make' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.potential' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.Step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.Reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.exists_reachable_maximum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.maximal_component_imbalance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.opposite_near_far_not_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.same_side_far_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.opposite_far_not_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.children' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.exists_geometric_label' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixty_six_chains_of_girth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.incidentPalette' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.IncidentProper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strong_iff_incident_palettes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.ColourableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.colourable_of_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.colourable_of_one_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.bad_degree_lists_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.degree_delete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.colourable_of_list_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.bad_lists_subset_at_noncut' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.bad_lists_equal_on_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.bad_noncut_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.degree_delete_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.DegreeList.colourable_of_independent_precolour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.DegreeList.colourable_of_nonseparating_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.UnrestrictedStarInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_unrestricted_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.Conj1126Strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.conj1126Weak_of_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1126Strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.hexagon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.hexagon_locallyTreeAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.farLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.farRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.hexagon_opposite_far_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.SeventhPassExamples.oneEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.oneColoured' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.SeventhPassExamples.raw_P4_needs_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.colour' depends on axioms: [propext]
'Se20Insertion.StaticDynamicExample.domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.colouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.static_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.first_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.afterFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.second_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.afterSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.transported_double_destroyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.StaticDynamicExample.not_three_colourable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedColour' depends on axioms: [propext, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedColouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_single_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_first_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedAfterFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_second_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.liftedAfterSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_transport_destroyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.StaticDynamicExample.five_cycle_not_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_not_twenty_colourable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.StaticDynamicExample.lifted_degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.propositionP3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depthThreeColour' depends on axioms: [propext, Quot.sound]
'Se20Insertion.StaticDynamicExample.depthThreeColouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depth_three_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depth_three_no_repair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depthAfterFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depth_second_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depthAfterSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depth_third_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.StaticDynamicExample.depth_three_missing_colour_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.HoleFillWithin.fill' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.HoleFillWithin.move' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.Step.hole' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.HoleState.Step.kempe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Validation.**

The complete `./build.ps1` run exited with code **0**. It rebuilt every project module, all thirteen additions, the expanded audit and the root module. The log is [BUILD7.final.log](BUILD7.final.log), with status in [BUILD7.final.exitcode](BUILD7.final.exitcode). All **487 audit entries**, including **108 additions**, use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets including no axioms. The source scan for `sorry`, `admit`, `axiom`, `native_decide`, and `ofReduceBool` returned no matches. Statement printing also exited 0. Linter and deprecation warnings remain; no proof/type errors remain. The build used one retry for a transient dependency-file read failure, preserving its diagnostics. The toolchain is `leanprover/lean4:v4.35.0-rc4`. Validation completed at 2026-11-06 10:46:17 +11:00.

[build.ps1](build.ps1) includes the thirteen new modules in dependency order, then the expanded [AxiomAudit.lean](Se20Insertion/AxiomAudit.lean) and root module. [audit7.ps1](audit7.ps1) regenerates the audit additions and statement printer; [finalize-report7.ps1](finalize-report7.ps1) checks the outputs before producing this report. Pre-existing mathematical declarations were not edited.

**What is not done.**

1. **Gallai / 11.40(5): unfinished.** The structural pair/exception theorem and block reduction are missing. The checked non-separating-pair colouring lemma and non-cut uniform-list reduction do not replace them.
2. **Broader geometric bridge:** the new map-free 11.5 corollary assumes finite four-regular G and girth ≥7. An arbitrary maximum-degree-four version with partially occupied positions, and a suitable local no-short-cycle predicate, are not supplied. The old `LocallyTreeAt` cannot be used for this purpose.
3. **Scanned claims still missing:** P6; the 103/27/84 long-chain count corollaries; §8.2.1's conditional 19-colour theorem and dense-side statement.
4. This pass proves neither Conjecture 11.9, the insertion conjectures, the global strong-colouring theorem, nor saturation at arbitrary static distance. The infinite-colouring-domain limitation recorded in REPORT6 also remains.
