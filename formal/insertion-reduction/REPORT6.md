**Flaws and scope qualifications first.** No new counterexample to a numbered result was found in this pass. The triangle-example objection at the start of `REPORT5.md` applies to the old text, not to the corrected example in `reference/MANUSCRIPT_zh.md` §7. The corrected example subtracts the overlapping edge; this pass uses that manuscript and its corrected direct proof of 11.22. The single-edge gain formula still requires the explicit hypothesis `b ≠ p`; the new theorem includes it. The old `b = p` counterexample is not being dismissed or hidden.

**11.40(5) remains unproved.** The new critical-graph reduction produces an actual noncolourable degree-list assignment on any nonempty induced set of degree-20 vertices. It does **not** prove that its blocks are cliques or odd cycles. The exact missing classification and the work completed toward it are recorded below. No Gallai theorem has been assumed as an axiom.

**Infinite-tree and tree-pattern scope is explicit.** The infinite-tree theorem has no `Fintype V` assumption, but retains the existing finite colouring domain `F : Finset G.edgeSet`. This is enough to state and prove a nonvacuous finite-domain version of 11.1 on an infinite 4-regular tree. It is not a claim about every colouring with infinite domain. For the 66-pair bound, the result is the user-authorized finite statement on the exact 24-vertex conflict graph, now connected to its actual induced edge set. A separate theorem transfers the count to 66 distinct colour pairs and Kempe chains under an explicit injective map of those positions into the ambient graph with adjacency domination. An automatic construction of that map from an informal phrase such as “tree-like neighbourhood” is not asserted.

**Results, in the requested order.** All colourings use ambient conflicts. `Colour = Fin 20`. None of the pre-existing theorem statements was changed.

| Target | Checked result and files |
| --- | --- |
| 11.22(2), (3), full operational statement | [DegreeThreeRigidity.lean](Se20Insertion/DegreeThreeRigidity.lean), `degree_three_rigidity`, with [StarGeometry.lean](Se20Insertion/StarGeometry.lean). `SwapSingleRepair` means zero or one actual component swap, followed by an extension that changes at most one old edge relative to the swapped colouring. Failure implies the complete 20-edge saturation, both 9-edge shell permutations, unique representatives, and both families of cross-shell component conditions. **No tree-like or girth hypothesis.** |
| 11.25(2), ambient overlaps | [ShortCycleReduction.lean](Se20Insertion/ShortCycleReduction.lean), `minimal_counterexample_degree_three_no_short_cycle`. A degree-3 vertex in a vertex-minimal counterexample lies on neither a triangle nor a four-cycle. The proof works with ambient set unions and incidence counts, allowing chords and overlap; triangle conflict bound 16 and square bound 19 give the reductions. The only minimality premise needed is colourability after deleting each vertex. |
| Tree-like corollary of 11.24 | [StarListRigidity.lean](Se20Insertion/StarListRigidity.lean), `degree_three_star_list_rigidity`, supported by [ListRigidity.lean](Se20Insertion/ListRigidity.lean). Failure of zero/one component swap followed by filling the three edges forces the common 2-element list, the 9+9 distinct-colour decomposition, identical shell palettes and the 18 free-colour/shell-colour component conditions. The obstruction forces the required equalities **without a tree hypothesis**, so the stated tree-like corollary follows. |
| 11.41(2), (3), (4) | [CliqueBoundary.lean](Se20Insertion/CliqueBoundary.lean) and [CliqueReduction.lean](Se20Insertion/CliqueReduction.lean): `strongColourable_of_delete_K4`, `counterexample_no_K4`, `triangle_boundary_rigidity`. K4 deletion and reinsertion are proved. In a counterexample, any colouring outside a triangle has exactly six pairwise-conflicting boundary edges with the same 5-element list; each sees exactly 15 distinctly coloured old edges, and all unique blocked-colour representatives lie in one component for every free/blocked colour pair (5×15 conditions). |
| Single-edge recolouring gain | [ComponentInsertion.lean](Se20Insertion/ComponentInsertion.lean), `count_insert`, and [RecolourGain.lean](Se20Insertion/RecolourGain.lean), `recolour_gain`. The exact component deletion/insertion identity is proved from the quotient of the actual induced graph, including the zero-neighbour case. The full unordered-pair sum formula assumes `f ∈ F`, `colour f = p`, `b ≠ p`, and `Free f b`. |
| 11.4 | [ShellCover.lean](Se20Insertion/ShellCover.lean), `single_shell_cover_opposite`, proves the opposite-side-only colour statement for partial colourings under local absence of triangles and squares through the hole. `locallyTreeAt_of_girth` supplies those conditions when girth ≥7. [ShellChains.lean](Se20Insertion/ShellChains.lean), `shell_branch_conflicts`, proves every shell edge conflicts with every edge at its branch root; `single_chain_avoids_closed_neighbourhood` proves the internal-edge avoidance assertion. |
| 11.5 / 66 pairs | [TreePattern.lean](Se20Insertion/TreePattern.lean), [PatternVerification.lean](Se20Insertion/PatternVerification.lean), and [LoopChains.lean](Se20Insertion/LoopChains.lean). `sixteen_induced_edges` states that every 16-element subset of the exact 24-position graph has at most 54 induced edges and at least 66 nonedges. `sixty_six_chains` transfers these to **distinct unordered colour pairs** with nonadjacent single representatives in the same Kempe component. The generic avoidance theorem applies to every other edge of each such two-colour chain. |
| 11.1 on infinite trees | [InfiniteForest.lean](Se20Insertion/InfiniteForest.lean), `infinite_forest_separable` and `infinite_four_regular_tree_separable`. Arbitrary vertex type, local degree ≤4, acyclic ambient graph, finite partial colouring, uncoloured hole: a separable colour pair exists. Blockedness is unnecessary. An actual infinite 4-regular tree is covered by `InfiniteFourRegular`; finite domain is an explicit limitation. |
| 11.40(5) | [CriticalLists.lean](Se20Insertion/CriticalLists.lean), `critical_low_degree_list_obstruction`, proves the criticality-to-degree-list reduction. The Gallai block classification remains open in this development. |
| §7.5 P2 | [MultiplicityIdentity.lean](Se20Insertion/MultiplicityIdentity.lean), [P2Identity.lean](Se20Insertion/P2Identity.lean), [P2Geometry.lean](Se20Insertion/P2Geometry.lean): `p2_identity` proves the exact arithmetic from actual finite counts; `propositionP2` supplies the girth/4-regular geometry and proves `L ≥ 0` together with the requested identity. No saturation or absence of exposed pairs is assumed. |
| §7.6 hole-move Δβ | [HoleCycleRank.lean](Se20Insertion/HoleCycleRank.lean), `holeMove_cycleRank`. Cycle rank is the integer `E − V + C` of the actual induced graph, summed once over each unordered colour pair. A legal single-colour hole move satisfies the exact deletion/insertion formula. |

**The two component formulas.** Write `C_H(S)` for the number of components of `H[S]`, and `t_H(S,f)` for the number of those components containing a neighbour of `f`. The proved basic identity, for `f ∉ S`, is

```text
C_H(S ∪ {f}) + t_H(S,f) = C_H(S) + 1.
```

For recolouring `f` from `p` to a distinct free colour `b`, this gives

```text
C(new) − C(old)
  = Σ_{x ∉ {p,b}} ( t_H(V_px \ {f}, f) − t_H(V_bx, f) ).
```

Properness and freeness ensure that the touched components here are exactly the manuscript's components reached by the x-coloured neighbours. For a legal hole move `h → f_p`, put `S_x = V_px \ {f_p}`. The second formula is

```text
β(new) − β(old)
  = Σ_{x ≠ p} [ (|N_x(h)| − t_H(S_x,h))
                 − (|N_x(f_p)| − t_H(S_x,f_p)) ].
```

All subtractions in these formulas are integer subtractions. In particular, the proof does not silently truncate a negative gain.

**The P2 quantities are actual counts.** In `propositionP2`, `F = univ \ {h}`, `S = R.erase h`, `n = |S|`, and ε(x) indicates conflict with h. `D` sums `19 − seenColours(x).card`; `M` sums ε; `T` counts ordered conflicts from S to coloured edges outside S; `E` sums `max(μ−2,0)`; `Z` counts unordered edges of the induced graph whose two directions are both nonsingle. `B` counts ordered mutually-single partners exposed by an actual `DoubleHoleConfig` with some g∈R. The stored slack is Σ(24−incomingSingles−3c₀); `p2_slack_eq` proves that it equals the manuscript's Σ(s+ε−3c₀). The geometry bounds each unexposed-partner count, hence L≥0. The final checked equality is

```text
14D + 3B = 2n + 10M + 3T + 7E + 6Z + L.
```

**The finite 66-pair proof.** The position type is `(Bool × Fin 3) ⊕ ((Bool × Fin 3) × Fin 3)`: six near positions, and eighteen far positions. The near positions form a clique; a near and far position conflict exactly on the same side; two distinct far positions conflict exactly on the same branch. For near counts n₀,n₁ and branch counts qᵢ, the exact induced edge count is

```text
choose(n₀+n₁,2) + n₀ Σ_i q_(0,i) + n₁ Σ_i q_(1,i) + Σ_i choose(q_i,2).
```

The bound uses a structured case split on n₀+n₁≤6. In the last case, ten selected far positions contribute at most nine same-branch edges: equality at ten would force every occupied branch to have three positions, contradicting divisibility by three. `actual_edge_count` proves that this expression equals the edge cardinality of the actual induced graph by checking its adjacency matrix with rational polynomial identities. `sixty_six_chains_of_stuck` obtains the sixteen single positions automatically from blockedness when the pattern labels the whole conflict neighbourhood; they are not an additional hypothesis in that corollary. No external enumeration result is imported; the small uses of `decide` are kernel checked, and there is no `native_decide`.

**Exact declarations.** The following is the actual `#check` output for all 130 audited additions, including definitions, supporting lemmas and the eight projections of `P2Terms`. It is also [STATEMENTS6.txt](STATEMENTS6.txt), generated by [Print6.lean](Print6.lean). Definition bodies are in the source files above; the complete declaration inventory is [DECLARATIONS6.txt](DECLARATIONS6.txt).

```text
Se20Insertion.branch.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (u v : V) : Finset ↑G.edgeSet
Se20Insertion.starBase.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (u : V) : Finset ↑G.edgeSet
Se20Insertion.shell.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (u v : V) : Finset ↑G.edgeSet
Se20Insertion.branch_card_le.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hΔ : Se20Insertion.MaxDegreeFour G)
  {u v : V} (h : G.Adj u v) : (Se20Insertion.branch G u v).card ≤ 3
Se20Insertion.starBase_card_le.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hΔ : Se20Insertion.MaxDegreeFour G)
  (u : V) : (Se20Insertion.starBase G u).card ≤ 3 * G.degree u
Se20Insertion.shell_card_le.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hΔ : Se20Insertion.MaxDegreeFour G)
  {u v : V} (h : G.Adj u v) : (Se20Insertion.shell G u v).card ≤ 9
Se20Insertion.conflicts_star_decomposition.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (e : ↑G.edgeSet)
  {u v : V} (he : ↑e = s(u, v)) :
  Se20Insertion.conflicts G e =
    (Se20Insertion.incident G u).erase e ∪ Se20Insertion.starBase G u ∪ Se20Insertion.shell G u v
Se20Insertion.shell_conflicts_branch.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
  {f g : ↑G.edgeSet} (hf : f ∈ Se20Insertion.shell G u v) (hg : v ∈ ↑g) (hne : g ≠ f) : (Se20Insertion.L2 G).Adj g f
Se20Insertion.PartialColouring.SwapSingleRepair.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (e : W) : Prop
Se20Insertion.PartialColouring.repair_of_free.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {e : W} (he : e ∉ F) {c : Se20Insertion.Colour} (hc : φ.Free e c) :
  φ.SwapSingleRepair e
Se20Insertion.PartialColouring.palette_split.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (K S : Finset W) (hK : K.card ≤ 11) (hS : S.card ≤ 9)
  (hall : ∀ (c : Se20Insertion.Colour), ∃ x ∈ K ∪ S, x ∈ F ∧ φ.colour x = c) :
  K.card = 11 ∧
    S.card = 9 ∧
      Disjoint K S ∧
        (∀ x ∈ K ∪ S, x ∈ F) ∧
          Set.InjOn φ.colour ↑(K ∪ S) ∧ Finset.image φ.colour S = Finset.univ \ Finset.image φ.colour K
Se20Insertion.degree_three_rigidity.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {u v : V} (huv : G.Adj u v) (hu : G.degree u = 3)
  (he : Se20Insertion.edge G huv ∉ F) (hno : ¬φ.SwapSingleRepair (Se20Insertion.edge G huv)) :
  have e := Se20Insertion.edge G huv;
  have K := (Se20Insertion.incident G u).erase e ∪ Se20Insertion.starBase G u;
  have A := Finset.image φ.colour (Se20Insertion.shell G u v);
  (Se20Insertion.conflicts G e).card = 20 ∧
    (∀ f ∈ Se20Insertion.conflicts G e, f ∈ F) ∧
      Set.InjOn φ.colour ↑(Se20Insertion.conflicts G e) ∧
        (∀ f ∈ Se20Insertion.conflicts G e, ∀ (c : Se20Insertion.Colour), c ≠ φ.colour f → ∃ x, φ.Neighbour f c x) ∧
          A.card = 9 ∧
            K.card = 11 ∧
              ∀ (w : V) (huw : G.Adj u w),
                w ≠ v →
                  (Se20Insertion.shell G u w).card = 9 ∧
                    Finset.image φ.colour (Se20Insertion.shell G u w) = A ∧
                      (∀ x ∈ Se20Insertion.shell G u w, x ∈ F) ∧
                        Set.InjOn φ.colour ↑(Se20Insertion.shell G u w) ∧
                          (∀ c ∈ A, ∃! x, x ∈ Se20Insertion.shell G u w ∧ φ.colour x = c) ∧
                            ∀ (z : V),
                              G.Adj u z →
                                z ≠ v →
                                  z ≠ w →
                                    ∀ c ∈ A,
                                      ∀ x ∈ Se20Insertion.shell G u z,
                                        φ.colour x = c →
                                          φ.SameComponent (φ.colour (Se20Insertion.edge G huw)) c
                                            (Se20Insertion.edge G huw) x
Se20Insertion.star_coloured_conflicts_subtract.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  {F : Finset ↑G.edgeSet} (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (u : V)
  (hF : Disjoint F (Se20Insertion.incident G u)) (e : ↑G.edgeSet) (he : u ∈ ↑e) :
  (φ.colouredNeighbours e).card + G.degree u ≤ (Se20Insertion.conflicts G e).card + 1
Se20Insertion.degree_three_triangle_conflicts.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {u v w : V} (hu : G.degree u = 3) (huv : G.Adj u v) (huw : G.Adj u w)
  (hvw : G.Adj v w) : (Se20Insertion.conflicts G (Se20Insertion.edge G huv)).card ≤ 16
Se20Insertion.degree_three_square_conflicts.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {u v w x : V} (hu : G.degree u = 3) (huv : G.Adj u v) (hvw : G.Adj v w)
  (hwx : G.Adj w x) (hxu : G.Adj x u) (huw : u ≠ w) (hvx : v ≠ x) :
  (Se20Insertion.conflicts G (Se20Insertion.edge G huv)).card ≤ 19
Se20Insertion.degree_three_extension_of_small_conflicts.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {u : V} (hu : G.degree u = 3) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (hF : Disjoint F (Se20Insertion.incident G u))
  {e : ↑G.edgeSet} (he : u ∈ ↑e) (hn : (Se20Insertion.conflicts G e).card ≤ 19) : ∃ ψ, ∀ x ∈ F, ψ.colour x = φ.colour x
Se20Insertion.degree_three_short_cycle_reducible.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {u : V} (hu : G.degree u = 3)
  (hc : Se20Insertion.StrongColourable (SimpleGraph.induce {x | x ≠ u} G) 20)
  (hshort :
    (∃ v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) ∨
      ∃ v w x, G.Adj u v ∧ G.Adj v w ∧ G.Adj w x ∧ G.Adj x u ∧ u ≠ w ∧ v ≠ x) :
  Se20Insertion.StrongColourable G 20
Se20Insertion.minimal_counterexample_degree_three_no_short_cycle.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) (hno : ¬Se20Insertion.StrongColourable G 20)
  (hdel : ∀ (u : V), Se20Insertion.StrongColourable (SimpleGraph.induce {x | x ≠ u} G) 20) {u : V}
  (hu : G.degree u = 3) :
  (∀ (v w : V), G.Adj u v → G.Adj u w → ¬G.Adj v w) ∧
    ∀ (v w x : V), G.Adj u v → G.Adj v w → G.Adj w x → G.Adj x u → u ≠ w → v ≠ x → False
Se20Insertion.PartialColouring.OneSwapListRepair.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (U : Finset W) : Prop
Se20Insertion.PartialColouring.available_complement.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (v : W) :
  Finset.image φ.colour (φ.colouredNeighbours v) = Finset.univ \ φ.available v
Se20Insertion.PartialColouring.tight_list_neighbours.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (v : W)
  (hn : (φ.colouredNeighbours v).card + (φ.available v).card ≤ 20) :
  (φ.colouredNeighbours v).card + (φ.available v).card = 20 ∧
    Set.InjOn φ.colour ↑(φ.colouredNeighbours v) ∧ ∀ c ∉ φ.available v, ∃! x, φ.Neighbour v c x
Se20Insertion.PartialColouring.swap_unique_list.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {v m : W} {a b : Se20Insertion.Colour} (ha : a ∈ φ.available v)
  (hs : φ.Single v b m) {S : Set W} (hS : φ.KempeClosed a b S) :
  (φ.swap a b S hS).available v = if m ∈ S then Insert.insert b ((φ.available v).erase a) else φ.available v
Se20Insertion.PartialColouring.one_swap_list_rigidity.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (U : Finset W) (hdis : Disjoint F U) (hne : U.Nonempty)
  (hL : ∀ v ∈ U, U.card - 1 ≤ (φ.available v).card) (hN : ∀ v ∈ U, (φ.colouredNeighbours v).card + (U.card - 1) ≤ 20)
  (hno : ¬φ.OneSwapListRepair U) :
  ∃ L,
    L.card = U.card - 1 ∧
      (∀ v ∈ U, φ.available v = L) ∧
        (∀ v ∈ U, (φ.colouredNeighbours v).card + L.card = 20 ∧ ∀ b ∉ L, ∃! m, φ.Neighbour v b m) ∧
          ∀ a ∈ L,
            ∀ b ∉ L, ∀ v ∈ U, ∀ w ∈ U, ∀ (m n : W), φ.Neighbour v b m → φ.Neighbour w b n → φ.SameComponent a b m n
Se20Insertion.PartialColouring.eighteen_split.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (K S : Finset W) (A : Finset Se20Insertion.Colour) (hA : A.card = 18)
  (hK : K.card ≤ 9) (hS : S.card ≤ 9) (hall : ∀ c ∈ A, ∃ x ∈ K ∪ S, x ∈ F ∧ φ.colour x = c) :
  K.card = 9 ∧
    S.card = 9 ∧
      Disjoint K S ∧
        (∀ x ∈ K ∪ S, x ∈ F) ∧ Set.InjOn φ.colour ↑(K ∪ S) ∧ Finset.image φ.colour S = A \ Finset.image φ.colour K
Se20Insertion.degree_three_star_list_rigidity.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {u : V} (hu : G.degree u = 3) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (hF : Disjoint F (Se20Insertion.incident G u))
  (hno : ¬φ.OneSwapListRepair (Se20Insertion.incident G u)) :
  ∃ L A,
    L.card = 2 ∧
      A.card = 9 ∧
        (Se20Insertion.starBase G u).card = 9 ∧
          (∀ e ∈ Se20Insertion.incident G u, φ.available e = L) ∧
            ∀ (v : V),
              G.Adj u v →
                (Se20Insertion.shell G u v).card = 9 ∧
                  Disjoint (Se20Insertion.starBase G u) (Se20Insertion.shell G u v) ∧
                    (∀ x ∈ Se20Insertion.starBase G u ∪ Se20Insertion.shell G u v, x ∈ F) ∧
                      Set.InjOn φ.colour ↑(Se20Insertion.starBase G u ∪ Se20Insertion.shell G u v) ∧
                        Finset.image φ.colour (Se20Insertion.starBase G u ∪ Se20Insertion.shell G u v) =
                            Finset.univ \ L ∧
                          Finset.image φ.colour (Se20Insertion.shell G u v) = A ∧
                            ∀ a ∈ L,
                              ∀ c ∈ A,
                                ∀ x ∈ Se20Insertion.shell G u v,
                                  φ.colour x = c →
                                    ∀ (w : V),
                                      G.Adj u w →
                                        ∀ y ∈ Se20Insertion.shell G u w, φ.colour y = c → φ.SameComponent a c x y
Se20Insertion.outsideEdges.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Finset ↑G.edgeSet
Se20Insertion.boundaryEdges.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Finset ↑G.edgeSet
Se20Insertion.CliqueSet.{u_1} {V : Type u_1} (G : SimpleGraph V) (S : Finset V) : Prop
Se20Insertion.outside_colouring.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V)
  (hc : Se20Insertion.StrongColourable (SimpleGraph.induce {x | x ∉ S} G) 20) :
  Nonempty (Se20Insertion.PartialColouring (Se20Insertion.L2 G) (Se20Insertion.outsideEdges G S))
Se20Insertion.boundary_disjoint.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
  Disjoint (Se20Insertion.outsideEdges G S) (Se20Insertion.boundaryEdges G S)
Se20Insertion.boundary_pairwise_conflict.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {S : Finset V}
  (hS : Se20Insertion.CliqueSet G S) {e f : ↑G.edgeSet} (he : e ∈ Se20Insertion.boundaryEdges G S)
  (hf : f ∈ Se20Insertion.boundaryEdges G S) (hne : e ≠ f) : (Se20Insertion.L2 G).Adj e f
Se20Insertion.clique_outside_neighbours.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {S : Finset V} (hS : Se20Insertion.CliqueSet G S) {u : V} (hu : u ∈ S) :
  (G.neighborFinset u \ S).card + S.card ≤ 5
Se20Insertion.boundary_card.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hΔ : Se20Insertion.MaxDegreeFour G)
  {S : Finset V} (hS : Se20Insertion.CliqueSet G S) : (Se20Insertion.boundaryEdges G S).card ≤ S.card * (5 - S.card)
Se20Insertion.boundary_coloured_conflicts.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {S : Finset V} (hS : Se20Insertion.CliqueSet G S)
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) (Se20Insertion.outsideEdges G S)) {e : ↑G.edgeSet}
  (he : e ∈ Se20Insertion.boundaryEdges G S) : (φ.colouredNeighbours e).card ≤ 3 * (5 - S.card) + 9
Se20Insertion.PartialColouring.fill_of_list_card.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (U : Finset W) (hdis : Disjoint F U)
  (hL : ∀ x ∈ U, U.card ≤ (φ.available x).card) : ∃ ψ, ∀ x ∈ F, ψ.colour x = φ.colour x
Se20Insertion.boundary_iff.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V) (e : ↑G.edgeSet) :
  e ∈ Se20Insertion.boundaryEdges G S ↔ (∃ x ∈ ↑e, x ∈ S) ∧ ∃ y ∈ ↑e, y ∉ S
Se20Insertion.outside_boundary_partition.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
  Se20Insertion.outsideEdges G S ∪ Se20Insertion.boundaryEdges G S =
    Finset.univ \ Se20Insertion.internalEdges G Finset.univ S
Se20Insertion.clique_internal_triangle.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {S : Finset V}
  (hS : Se20Insertion.CliqueSet G S) (hcard : 3 ≤ S.card) {e : ↑G.edgeSet}
  (he : e ∈ Se20Insertion.internalEdges G Finset.univ S) : Se20Insertion.OnTriangle G e
Se20Insertion.clique_finish.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hΔ : Se20Insertion.MaxDegreeFour G)
  {S : Finset V} (hS : Se20Insertion.CliqueSet G S) (hcard : 3 ≤ S.card)
  (hc :
    Nonempty
      (Se20Insertion.PartialColouring (Se20Insertion.L2 G)
        (Se20Insertion.outsideEdges G S ∪ Se20Insertion.boundaryEdges G S))) :
  Se20Insertion.StrongColourable G 20
Se20Insertion.strongColourable_of_delete_K4.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {S : Finset V} (hS : Se20Insertion.CliqueSet G S) (hcard : S.card = 4)
  (hc : Se20Insertion.StrongColourable (SimpleGraph.induce {x | x ∉ S} G) 20) : Se20Insertion.StrongColourable G 20
Se20Insertion.counterexample_no_K4.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) (hno : ¬Se20Insertion.StrongColourable G 20)
  (hdel : ∀ (S : Finset V), S.card = 4 → Se20Insertion.StrongColourable (SimpleGraph.induce {x | x ∉ S} G) 20)
  (S : Finset V) : S.card = 4 → ¬Se20Insertion.CliqueSet G S
Se20Insertion.triangle_boundary_rigidity.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) {S : Finset V} (hS : Se20Insertion.CliqueSet G S) (hcard : S.card = 3)
  (hno : ¬Se20Insertion.StrongColourable G 20)
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) (Se20Insertion.outsideEdges G S)) :
  (Se20Insertion.boundaryEdges G S).card = 6 ∧
    (∀ e ∈ Se20Insertion.boundaryEdges G S,
        ∀ f ∈ Se20Insertion.boundaryEdges G S, e ≠ f → (Se20Insertion.L2 G).Adj e f) ∧
      ∃ L,
        L.card = 5 ∧
          (∀ e ∈ Se20Insertion.boundaryEdges G S,
              φ.available e = L ∧
                (φ.colouredNeighbours e).card = 15 ∧
                  Set.InjOn φ.colour ↑(φ.colouredNeighbours e) ∧
                    Finset.image φ.colour (φ.colouredNeighbours e) = Finset.univ \ L ∧
                      ∀ b ∉ L, ∃! m, φ.Neighbour e b m) ∧
            ∀ a ∈ L,
              ∀ b ∉ L,
                ∀ e ∈ Se20Insertion.boundaryEdges G S,
                  ∀ f ∈ Se20Insertion.boundaryEdges G S,
                    ∀ (m n : ↑G.edgeSet), φ.Neighbour e b m → φ.Neighbour f b n → φ.SameComponent a b m n
Se20Insertion.ComponentInsertion.count.{u_1} {W : Type u_1} (H : SimpleGraph W) (S : Finset W) : ℕ
Se20Insertion.ComponentInsertion.Touches.{u_1} {W : Type u_1} (H : SimpleGraph W) (S : Finset W) (f : W)
  (c : (SimpleGraph.induce (↑S) H).ConnectedComponent) : Prop
Se20Insertion.ComponentInsertion.touchingCount.{u_1} {W : Type u_1} (H : SimpleGraph W) (S : Finset W) (f : W) : ℕ
Se20Insertion.ComponentInsertion.count_insert.{u_1} {W : Type u_1} [DecidableEq W] (H : SimpleGraph W) (S : Finset W)
  (f : W) (hf : f ∉ S) :
  Se20Insertion.ComponentInsertion.count H (Insert.insert f S) + Se20Insertion.ComponentInsertion.touchingCount H S f =
    Se20Insertion.ComponentInsertion.count H S + 1
Se20Insertion.sum_pair_star (p : Se20Insertion.Colour) (t : Se20Insertion.Colour → ℤ) (ht : t p = 0) :
  (∑ a, ∑ b, if a < b then if a = p then t b else if b = p then t a else 0 else 0) = ∑ x, t x
Se20Insertion.sum_pair_two_stars (p q : Se20Insertion.Colour) (hpq : p ≠ q)
  (d : Se20Insertion.Colour → Se20Insertion.Colour → ℤ) (hsym : ∀ (a b : Se20Insertion.Colour), d a b = d b a)
  (hpq0 : d p q = 0) (hzero : ∀ (a b : Se20Insertion.Colour), a ≠ p → a ≠ q → b ≠ p → b ≠ q → d a b = 0) :
  (∑ a, ∑ b, if a < b then d a b else 0) = ∑ x ∈ Finset.univ \ {p, q}, (d p x + d q x)
Se20Insertion.PartialColouring.pairVertices.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (a b : Se20Insertion.Colour) : Finset W
Se20Insertion.PartialColouring.pairComponents.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (a b : Se20Insertion.Colour) : ℤ
Se20Insertion.PartialColouring.pairComponents_eq.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (a b : Se20Insertion.Colour) :
  φ.pairComponents a b = ↑(Nat.card (φ.KempeGraph a b).ConnectedComponent)
Se20Insertion.PartialColouring.componentCount_sum.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) :
  ↑φ.componentCount = ∑ a, ∑ b, if a < b then φ.pairComponents a b else 0
Se20Insertion.PartialColouring.pairComponents_symm.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) (a b : Se20Insertion.Colour) :
  φ.pairComponents a b = φ.pairComponents b a
Se20Insertion.PartialColouring.recolourOne.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (f : W) (b : Se20Insertion.Colour) (hb : φ.Free f b) :
  Se20Insertion.PartialColouring H F
Se20Insertion.PartialColouring.recolour_gain.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {f : W} (hf : f ∈ F) {p b : Se20Insertion.Colour} (hp : φ.colour f = p)
  (hbp : b ≠ p) (hb : φ.Free f b) :
  ↑(φ.recolourOne f b hb).componentCount - ↑φ.componentCount =
    ∑ x ∈ Finset.univ \ {p, b},
      (↑(Se20Insertion.ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) f) -
        ↑(Se20Insertion.ComponentInsertion.touchingCount H (φ.pairVertices b x) f))
Se20Insertion.TreePattern.Branch : Type
Se20Insertion.TreePattern.Position : Type
Se20Insertion.TreePattern.graph : SimpleGraph Se20Insertion.TreePattern.Position
Se20Insertion.TreePattern.positions_card : Fintype.card Se20Insertion.TreePattern.Position = 24
Se20Insertion.TreePattern.three_choose_le (q : Fin 4) : (↑q).choose 2 ≤ ↑q
Se20Insertion.TreePattern.three_choose_eq_dvd (q : Fin 4) (h : (↑q).choose 2 = ↑q) : 3 ∣ ↑q
Se20Insertion.TreePattern.ten_far_edges (q : Se20Insertion.TreePattern.Branch → Fin 4) (h : ∑ i, ↑(q i) = 10) :
  ∑ i, (↑(q i)).choose 2 ≤ 9
Se20Insertion.TreePattern.edgeNumber (n : Bool → Fin 4) (q : Se20Insertion.TreePattern.Branch → Fin 4) : ℕ
Se20Insertion.TreePattern.sixteen_positions_bound (n : Bool → Fin 4) (q : Se20Insertion.TreePattern.Branch → Fin 4)
  (hsize : ↑(n Bool.false) + ↑(n Bool.true) + ∑ i, ↑(q i) = 16) : Se20Insertion.TreePattern.edgeNumber n q ≤ 54
Se20Insertion.TreePattern.sixteen_positions_nonadjacent (n : Bool → Fin 4)
  (q : Se20Insertion.TreePattern.Branch → Fin 4) (hsize : ↑(n Bool.false) + ↑(n Bool.true) + ∑ i, ↑(q i) = 16) :
  66 ≤ 120 - Se20Insertion.TreePattern.edgeNumber n q
Se20Insertion.TreePattern.Near (N : Bool → Finset (Fin 3)) : Type
Se20Insertion.TreePattern.Far (B : Se20Insertion.TreePattern.Branch → Finset (Fin 3)) : Type
Se20Insertion.TreePattern.SelectedEdges (N : Bool → Finset (Fin 3))
  (B : Se20Insertion.TreePattern.Branch → Finset (Fin 3)) : Type
Se20Insertion.TreePattern.selected_edges_bound (N : Bool → Finset (Fin 3))
  (B : Se20Insertion.TreePattern.Branch → Finset (Fin 3))
  (hsize : Fintype.card (Se20Insertion.TreePattern.Near N) + Fintype.card (Se20Insertion.TreePattern.Far B) = 16) :
  Fintype.card (Se20Insertion.TreePattern.SelectedEdges N B) ≤ 54 ∧
    66 ≤
      (Fintype.card (Se20Insertion.TreePattern.Near N) + Fintype.card (Se20Insertion.TreePattern.Far B)).choose 2 -
        Fintype.card (Se20Insertion.TreePattern.SelectedEdges N B)
Se20Insertion.single_shell_cover.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e f : ↑G.edgeSet} {u v : V} (hf : ↑f = s(u, v))
  (hs : φ.Single e (φ.colour f) f) (hnt : ∀ (a b : Se20Insertion.Colour), a ≠ b → ¬φ.TriviallySeparable e a b)
  {c : Se20Insertion.Colour} (hc : c ≠ φ.colour f)
  (hinner : c ∉ Finset.image φ.colour ((Se20Insertion.incident G u).erase f ∪ Se20Insertion.starBase G u)) :
  ∃ x ∈ Se20Insertion.shell G u v, x ∈ F ∧ φ.colour x = c
Se20Insertion.shell_branch_conflicts.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
  {s f : ↑G.edgeSet} (hs : s ∈ Se20Insertion.shell G u v) (hf : v ∈ ↑f) : (Se20Insertion.L2 G).Adj f s
Se20Insertion.PartialColouring.single_chain_avoids_closed_neighbourhood.{u_1} {V : Type u_1} {G : SimpleGraph V}
  {F : Finset ↑G.edgeSet} (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e f g z : ↑G.edgeSet} {u v : V}
  (he : ↑e = s(u, v)) (heF : e ∉ F) {a b : Se20Insertion.Colour} (hf : φ.Single e a f) (hg : φ.Single e b g)
  (hz : z ∈ φ.Bicoloured a b) (hzf : z ≠ f) (hzg : z ≠ g) (w : V) : w ∈ ↑z → w ≠ u ∧ w ≠ v ∧ ¬G.Adj u w ∧ ¬G.Adj v w
Se20Insertion.PartialColouring.stuck_single_chain.{u_1} {V : Type u_1} {G : SimpleGraph V} {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e f g : ↑G.edgeSet} (hs : φ.Stuck e)
  {a b : Se20Insertion.Colour} (hab : a ≠ b) (hf : φ.Single e a f) (hg : φ.Single e b g) : φ.SameComponent a b f g
Se20Insertion.LocalMaxDegreeFour.{u_1} {V : Type u_1} (G : SimpleGraph V) : Prop
Se20Insertion.InfiniteFourRegular.{u_1} {V : Type u_1} (G : SimpleGraph V) : Prop
Se20Insertion.InfiniteFourRegular.localMaxDegreeFour.{u_1} {V : Type u_1} {G : SimpleGraph V}
  (hG : Se20Insertion.InfiniteFourRegular G) : Se20Insertion.LocalMaxDegreeFour G
Se20Insertion.localMaxDegreeFour_induce.{u_1} {V : Type u_1} {G : SimpleGraph V}
  (hG : Se20Insertion.LocalMaxDegreeFour G) (S : Finset V) : Se20Insertion.MaxDegreeFour (SimpleGraph.induce (↑S) G)
Se20Insertion.PartialColouring.infinite_forest_separable.{u_1} {V : Type u_1} {G : SimpleGraph V}
  {F : Finset ↑G.edgeSet} (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (hG : G.IsAcyclic)
  (hΔ : Se20Insertion.LocalMaxDegreeFour G) {e : ↑G.edgeSet} (he : e ∉ F) : ∃ a b, a ≠ b ∧ φ.Separable e a b
Se20Insertion.PartialColouring.infinite_four_regular_tree_separable.{u_1} {V : Type u_1} {G : SimpleGraph V}
  {F : Finset ↑G.edgeSet} (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (hG : G.IsTree)
  (hreg : Se20Insertion.InfiniteFourRegular G) {e : ↑G.edgeSet} (he : e ∉ F) : ∃ a b, a ≠ b ∧ φ.Separable e a b
Se20Insertion.critical_low_degree_list_obstruction.{u_1} {W : Type u_1} [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (hcrit : Se20Insertion.CriticalSet H F) (U : Finset W) (hU : U ⊆ F) (hne : U.Nonempty)
  (hdeg : ∀ x ∈ U, (Finset.filter (H.Adj x) F).card = 20) :
  ∃ L,
    (∀ x ∈ U, (Finset.filter (H.Adj x) U).card ≤ (L x).card) ∧
      ¬∃ c, (∀ (x : ↥U), c x ∈ L ↑x) ∧ ∀ (x y : ↥U), H.Adj ↑x ↑y → c x ≠ c y
Se20Insertion.ComponentInsertion.edges.{u_1} {W : Type u_1} (H : SimpleGraph W) (S : Finset W) : ℕ
Se20Insertion.ComponentInsertion.twice_edges.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
  (S : Finset W) : 2 * Se20Insertion.ComponentInsertion.edges H S = ∑ x ∈ S, (Finset.filter (H.Adj x) S).card
Se20Insertion.ComponentInsertion.edges_insert.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
  (S : Finset W) (f : W) (hf : f ∉ S) :
  Se20Insertion.ComponentInsertion.edges H (Insert.insert f S) =
    Se20Insertion.ComponentInsertion.edges H S + (Finset.filter (H.Adj f) S).card
Se20Insertion.ComponentInsertion.cycleRank.{u_1} {W : Type u_1} (H : SimpleGraph W) (S : Finset W) : ℤ
Se20Insertion.ComponentInsertion.cycleRank_insert.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
  (S : Finset W) (f : W) (hf : f ∉ S) :
  Se20Insertion.ComponentInsertion.cycleRank H (Insert.insert f S) - Se20Insertion.ComponentInsertion.cycleRank H S =
    ↑(Finset.filter (H.Adj f) S).card - ↑(Se20Insertion.ComponentInsertion.touchingCount H S f)
Se20Insertion.PartialColouring.totalCycleRank.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) : ℤ
Se20Insertion.PartialColouring.holeMove_cycleRank.{u_1} {W : Type u_1} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
  {F : Finset W} (φ : Se20Insertion.PartialColouring H F) {h f : W} {p : Se20Insertion.Colour} (hh : h ∉ F)
  (hs : φ.Single h p f) :
  (φ.holeMove hs).totalCycleRank - φ.totalCycleRank =
    ∑ x ∈ Finset.univ.erase p,
      (↑{y ∈ φ.colouredNeighbours h | φ.colour y = x}.card -
          ↑(Se20Insertion.ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) h) -
        (↑{y ∈ φ.colouredNeighbours f | φ.colour y = x}.card -
          ↑(Se20Insertion.ComponentInsertion.touchingCount H ((φ.pairVertices p x).erase f) f)))
Se20Insertion.multiplicity_identity.{u_1} {W : Type u_1} (N : Finset W) (c : W → Se20Insertion.Colour) :
  {x ∈ N | {y ∈ N | c y = c x}.card ≠ 1}.card + 2 * (Finset.image c N).card + ∑ a, ({y ∈ N | c y = a}.card - 2) =
    2 * N.card
Se20Insertion.PartialColouring.seenColours.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (x : W) : Finset Se20Insertion.Colour
Se20Insertion.PartialColouring.deficit.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (x : W) : ℕ
Se20Insertion.PartialColouring.excess.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (x : W) : ℕ
Se20Insertion.PartialColouring.single_iff_multiplicity_one.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {x y : W} (hy : y ∈ φ.colouredNeighbours x) :
  φ.Single x (φ.colour y) y ↔ {z ∈ φ.colouredNeighbours x | φ.colour z = φ.colour y}.card = 1
Se20Insertion.PartialColouring.seenColours_le_nineteen.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {x : W} (hx : x ∈ F) : (φ.seenColours x).card ≤ 19
Se20Insertion.PartialColouring.nonsingle_exact.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) {x : W} (hx : x ∈ F) :
  {y ∈ φ.colouredNeighbours x | ¬φ.Single x (φ.colour y) y}.card + 38 + φ.excess x =
    2 * (φ.colouredNeighbours x).card + 2 * φ.deficit x
Se20Insertion.PartialColouring.Exposed.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (R : Finset W) (f w : W) : Prop
Se20Insertion.PartialColouring.unexposedPartners.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (R S : Finset W) (f : W) : Finset W
Se20Insertion.PartialColouring.bothNonsingleGraph.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) : SimpleGraph W
Se20Insertion.PartialColouring.P2Terms : Type
Se20Insertion.PartialColouring.p2Terms.{u_1} {W : Type u_1} {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (R S : Finset W) (ε : W → ℕ) : Se20Insertion.PartialColouring.P2Terms
Se20Insertion.PartialColouring.p2_slack_eq.{u_1} {W : Type u_1} [Fintype W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (R S : Finset W) (ε : W → ℕ) (hSF : S ⊆ F)
  (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card + ε x = 24) :
  (φ.p2Terms R S ε).L =
    ∑ x ∈ S,
      (↑((φ.colouredNeighbours x).card - (φ.singleTargets S x).card + ε x) - 3 * ↑(φ.unexposedPartners R S x).card)
Se20Insertion.PartialColouring.p2_identity.{u_1} {W : Type u_1} [Fintype W] {H : SimpleGraph W} {F : Finset W}
  (φ : Se20Insertion.PartialColouring H F) (R S : Finset W) (ε : W → ℕ) (hSF : S ⊆ F) (hclosed : φ.SingleClosed S)
  (hdegree : ∀ x ∈ S, (φ.colouredNeighbours x).card + ε x = 24) :
  have v := φ.p2Terms R S ε;
  14 * v.D + 3 * v.B = 2 * v.n + 10 * v.M + 3 * v.T + 7 * v.E + 6 * v.Z + v.L
Se20Insertion.regular_girth_conflicts_card.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hreg : Se20Insertion.FourRegular G) (hg : 7 ≤ G.egirth) (e : ↑G.edgeSet) : (Se20Insertion.conflicts G e).card = 24
Se20Insertion.PartialColouring.unexposed_partner_bound.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hΔ : Se20Insertion.MaxDegreeFour G) (hg : 7 ≤ G.egirth) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) (R S : Finset ↑G.edgeSet) (hSR : S ⊆ R) (hSF : S ⊆ F)
  {f : ↑G.edgeSet} (hf : f ∈ S) : (φ.singleTargets S f).card + 3 * (φ.unexposedPartners R S f).card ≤ 24
Se20Insertion.PartialColouring.propositionP2.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V)
  (hreg : Se20Insertion.FourRegular G) (hg : 7 ≤ G.egirth) (h : ↑G.edgeSet)
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) (Finset.univ \ {h})) (R : Finset ↑G.edgeSet) (hhR : h ∈ R)
  (hblocked : ∀ (a : Se20Insertion.Colour), ∃ f, φ.Neighbour h a f) (hclosed : φ.SingleClosed R) :
  have S := R.erase h;
  have ε := fun x => if (Se20Insertion.L2 G).Adj x h then 1 else 0;
  have v := φ.p2Terms R S ε;
  0 ≤ v.L ∧ 14 * v.D + 3 * v.B = 2 * v.n + 10 * v.M + 3 * v.T + 7 * v.E + 6 * v.Z + v.L
Se20Insertion.TreePattern.weight (S : Finset Se20Insertion.TreePattern.Position)
  (x : Se20Insertion.TreePattern.Position) : ℚ
Se20Insertion.TreePattern.weight_sq (S : Finset Se20Insertion.TreePattern.Position)
  (x : Se20Insertion.TreePattern.Position) :
  Se20Insertion.TreePattern.weight S x ^ 2 = Se20Insertion.TreePattern.weight S x
Se20Insertion.TreePattern.sum_members.{u_1} {X : Type u_1} [Fintype X] (S : Finset X) (f : X → ℚ) :
  ∑ x ∈ S, f x = ∑ x, if x ∈ S then f x else 0
Se20Insertion.TreePattern.nearCount (S : Finset Se20Insertion.TreePattern.Position) (s : Bool) : Fin 4
Se20Insertion.TreePattern.farCount (S : Finset Se20Insertion.TreePattern.Position)
  (i : Se20Insertion.TreePattern.Branch) : Fin 4
Se20Insertion.TreePattern.nearCount_cast (S : Finset Se20Insertion.TreePattern.Position) (s : Bool) :
  ↑↑(Se20Insertion.TreePattern.nearCount S s) = ∑ i, Se20Insertion.TreePattern.weight S (Sum.inl (s, i))
Se20Insertion.TreePattern.farCount_cast (S : Finset Se20Insertion.TreePattern.Position)
  (i : Se20Insertion.TreePattern.Branch) :
  ↑↑(Se20Insertion.TreePattern.farCount S i) = ∑ j, Se20Insertion.TreePattern.weight S (Sum.inr (i, j))
Se20Insertion.TreePattern.selection_card (S : Finset Se20Insertion.TreePattern.Position) :
  ↑(Se20Insertion.TreePattern.nearCount S Bool.false) + ↑(Se20Insertion.TreePattern.nearCount S Bool.true) +
      ∑ i, ↑(Se20Insertion.TreePattern.farCount S i) =
    S.card
Se20Insertion.TreePattern.weighted_edges (S : Finset Se20Insertion.TreePattern.Position) :
  2 * ↑(Se20Insertion.ComponentInsertion.edges Se20Insertion.TreePattern.graph S) =
    ∑ x,
      ∑ y,
        if Se20Insertion.TreePattern.graph.Adj x y then
          Se20Insertion.TreePattern.weight S x * Se20Insertion.TreePattern.weight S y
        else 0
Se20Insertion.TreePattern.actual_edge_count (S : Finset Se20Insertion.TreePattern.Position) :
  Se20Insertion.ComponentInsertion.edges Se20Insertion.TreePattern.graph S =
    Se20Insertion.TreePattern.edgeNumber (Se20Insertion.TreePattern.nearCount S) (Se20Insertion.TreePattern.farCount S)
Se20Insertion.TreePattern.sixteen_induced_edges (S : Finset Se20Insertion.TreePattern.Position) (hS : S.card = 16) :
  Nat.card ↑(SimpleGraph.induce (↑S) Se20Insertion.TreePattern.graph).edgeSet ≤ 54 ∧
    66 ≤ S.card.choose 2 - Nat.card ↑(SimpleGraph.induce (↑S) Se20Insertion.TreePattern.graph).edgeSet
Se20Insertion.LocallyTreeAt.{u_1} {V : Type u_1} (G : SimpleGraph V) (u v : V) : Prop
Se20Insertion.locallyTreeAt_of_girth.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) (hg : 7 ≤ G.egirth) {u v : V}
  (huv : G.Adj u v) : Se20Insertion.LocallyTreeAt G u v
Se20Insertion.opposite_shell_disjoint.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {u v : V}
  (ht : Se20Insertion.LocallyTreeAt G u v) :
  Disjoint (Se20Insertion.shell G u v) (Se20Insertion.incident G u ∪ Se20Insertion.starBase G u)
Se20Insertion.single_shell_cover_opposite.{u_1} {V : Type u_1} [Fintype V] (G : SimpleGraph V) {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e f : ↑G.edgeSet} {u v x : V} (he : ↑e = s(u, v))
  (hf : ↑f = s(u, x)) (heF : e ∉ F) (ht : Se20Insertion.LocallyTreeAt G u v) (hs : φ.Single e (φ.colour f) f)
  (hnt : ∀ (a b : Se20Insertion.Colour), a ≠ b → ¬φ.TriviallySeparable e a b) {c : Se20Insertion.Colour}
  (honly : ∀ (z : ↑G.edgeSet), φ.Neighbour e c z → z ∈ Se20Insertion.shell G u v) :
  ∃ z ∈ Se20Insertion.shell G u x, z ∈ F ∧ φ.colour z = c
Se20Insertion.TreePattern.sixteen_nonedge_card (S : Finset Se20Insertion.TreePattern.Position) (hS : S.card = 16) :
  66 ≤ (SimpleGraph.induce (↑S) Se20Insertion.TreePattern.graph)ᶜ.edgeFinset.card
Se20Insertion.TreePattern.sixty_six_chains.{u_1} {V : Type u_1} {G : SimpleGraph V} {F : Finset ↑G.edgeSet}
  (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e : ↑G.edgeSet} (hstop : φ.Stuck e)
  (ι : Se20Insertion.TreePattern.Position → ↑G.edgeSet) (hinj : Function.Injective ι)
  (hpattern :
    ∀ (x y : Se20Insertion.TreePattern.Position),
      (Se20Insertion.L2 G).Adj (ι x) (ι y) → Se20Insertion.TreePattern.graph.Adj x y)
  (S : Finset Se20Insertion.TreePattern.Position) (hS : S.card = 16) (hs : ∀ x ∈ S, φ.Single e (φ.colour (ι x)) (ι x)) :
  ∃ P,
    66 ≤ P.card ∧
      ∀ t ∈ P,
        ∃ a b f g,
          t = s(a, b) ∧
            a ≠ b ∧ φ.Single e a f ∧ φ.Single e b g ∧ ¬(Se20Insertion.L2 G).Adj f g ∧ φ.SameComponent a b f g
Se20Insertion.TreePattern.sixty_six_chains_of_stuck.{u_1} {V : Type u_1} [Fintype V] {G : SimpleGraph V}
  {F : Finset ↑G.edgeSet} (φ : Se20Insertion.PartialColouring (Se20Insertion.L2 G) F) {e : ↑G.edgeSet}
  (hstop : φ.Stuck e) (ι : Se20Insertion.TreePattern.Position ≃ ↥(Se20Insertion.conflicts G e))
  (hpattern :
    ∀ (x y : Se20Insertion.TreePattern.Position),
      (Se20Insertion.L2 G).Adj ↑(ι x) ↑(ι y) → Se20Insertion.TreePattern.graph.Adj x y) :
  ∃ P,
    66 ≤ P.card ∧
      ∀ t ∈ P,
        ∃ a b f g,
          t = s(a, b) ∧
            a ≠ b ∧ φ.Single e a f ∧ φ.Single e b g ∧ ¬(Se20Insertion.L2 G).Adj f g ∧ φ.SameComponent a b f g
Se20Insertion.PartialColouring.P2Terms.n (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.D (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.B (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.M (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.T (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.E (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.Z (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
Se20Insertion.PartialColouring.P2Terms.L (self : Se20Insertion.PartialColouring.P2Terms) : ℤ
```

**Actual `#print axioms` output for the additions.** The audit is [AxiomAudit.lean](Se20Insertion/AxiomAudit.lean). [AXIOMS6_ADDITIONS.txt](AXIOMS6_ADDITIONS.txt) contains this same output, while [AXIOMS6.txt](AXIOMS6.txt) also includes the 249 earlier audit entries.

```text
'Se20Insertion.branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.starBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.shell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.branch_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.starBase_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.shell_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.conflicts_star_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.shell_conflicts_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.SwapSingleRepair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.repair_of_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.palette_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.star_coloured_conflicts_subtract' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_triangle_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_square_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_extension_of_small_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_short_cycle_reducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.minimal_counterexample_degree_three_no_short_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.OneSwapListRepair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.available_complement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.tight_list_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.swap_unique_list' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.one_swap_list_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.eighteen_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.degree_three_star_list_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.outsideEdges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundaryEdges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.CliqueSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.outside_colouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundary_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundary_pairwise_conflict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.clique_outside_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundary_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundary_coloured_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.fill_of_list_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.boundary_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.outside_boundary_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.clique_internal_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.clique_finish' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_delete_K4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.counterexample_no_K4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.triangle_boundary_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.Touches' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.touchingCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.count_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.sum_pair_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.sum_pair_two_stars' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.pairVertices' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.pairComponents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.pairComponents_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.componentCount_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.pairComponents_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.recolourOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.recolour_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.Branch' does not depend on any axioms
'Se20Insertion.TreePattern.Position' does not depend on any axioms
'Se20Insertion.TreePattern.graph' does not depend on any axioms
'Se20Insertion.TreePattern.positions_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.three_choose_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.three_choose_eq_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.ten_far_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.edgeNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixteen_positions_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixteen_positions_nonadjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.Near' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.Far' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.SelectedEdges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.selected_edges_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.single_shell_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.shell_branch_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.single_chain_avoids_closed_neighbourhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.stuck_single_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.LocalMaxDegreeFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.InfiniteFourRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.InfiniteFourRegular.localMaxDegreeFour' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.localMaxDegreeFour_induce' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.infinite_forest_separable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.infinite_four_regular_tree_separable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.critical_low_degree_list_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.twice_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.edges_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.cycleRank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ComponentInsertion.cycleRank_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.totalCycleRank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.holeMove_cycleRank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.multiplicity_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.seenColours' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.deficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.single_iff_multiplicity_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.seenColours_le_nineteen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.nonsingle_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.Exposed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.unexposedPartners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.bothNonsingleGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.P2Terms' does not depend on any axioms
'Se20Insertion.PartialColouring.p2Terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.p2_slack_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.p2_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.regular_girth_conflicts_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.unexposed_partner_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.propositionP2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.weight_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sum_members' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.nearCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.farCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.nearCount_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.farCount_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.selection_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.weighted_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.actual_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixteen_induced_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.LocallyTreeAt' does not depend on any axioms
'Se20Insertion.locallyTreeAt_of_girth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.opposite_shell_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.single_shell_cover_opposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixteen_nonedge_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixty_six_chains' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.TreePattern.sixty_six_chains_of_stuck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.P2Terms.n' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.D' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.B' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.M' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.T' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.E' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.Z' does not depend on any axioms
'Se20Insertion.PartialColouring.P2Terms.L' does not depend on any axioms
```

**Validation.**

The final `./build.ps1` run exited with code **0**, rebuilding every project module, all 20 additions, the expanded audit and the root module. The log is [BUILD6.final.log](BUILD6.final.log), with exit status in [BUILD6.final.exitcode](BUILD6.final.exitcode). The toolchain is `leanprover/lean4:v4.35.0-rc4`. All 379 audit entries (130 additions) depend only on `propext`, `Classical.choice`, and `Quot.sound`, or a subset including no axioms. The source scan for `sorry`, `admit`, `axiom`, `native_decide`, and `ofReduceBool` returned no matches. The statement-printing run also exited with code 0. Linter and deprecation warnings remain; there are no proof or type errors. The final run needed 0 retries for transient dependency-file read errors; diagnostics are retained in the log, and every module ultimately returned success. Earlier read failures on unchanged modules also succeeded on direct retry. Validation completed at 2026-11-06 09:49:33 +11:00.

[build.ps1](build.ps1) includes all 20 new modules in dependency order, followed by the expanded audit and the root module. It retries only dependency `.olean`/`.olean.private` read failures, at most three times, preserving diagnostics; proof/type errors fail immediately and no module is skipped. [audit6.ps1](audit6.ps1) regenerates the addition inventory, audit commands and statement printer. [finalize-report6.ps1](finalize-report6.ps1) validates the build and axiom logs and embeds the actual outputs into this report from [REPORT6.template.md](REPORT6.template.md).

**What is not done, and the precise blockers.**

1. **Gallai / 11.40(5).** What remains is the degree-list classification: a finite connected graph that admits an uncolourable list assignment with every list at least as large as the vertex degree has every block a clique or an odd cycle. Applying this to the degree-20 induced components would finish the target. `critical_low_degree_list_obstruction` already constructs the required bad lists by colouring the critical graph outside the selected low-degree set, and proves that an admissible list colouring would contradict criticality. The missing step is therefore the classification of connected non-degree-choosable graphs, including its block decomposition and the colouring argument for a block that is neither a clique nor an odd cycle. The installed SimpleGraph library supplies no Gallai, Brooks, or degree-choosability classification to instantiate; a source search was made. The obstacle is an unformalized general graph theorem, not a missing numerical inequality, finite search, or an assumed axiom. No claim is made that the reduction alone proves 11.40(5).
2. **Infinite colouring domains.** The theorem accepts genuinely infinite ambient trees but finite `F`. Extending it to an arbitrary set of coloured edges would require a set-domain colouring interface and a finite-witness extraction/transfer for the finitely many relevant two-colour connections, or a direct infinite-domain version of the forest separation argument. No such extension is claimed. The choice made for the requested infinite-tree target is explicitly the finite-domain statement.
3. **Automatic geometric labelling for 11.5.** The requested finite bound is fully proved for the exact pattern, and the ambient chain-transfer theorem is fully proved with its map and adjacency hypothesis visible. A separate theorem constructing this map from a geometric tree-like-neighbourhood definition has not been added. The numeric result is not merely a count surrogate: `sixteen_induced_edges` is about `Nat.card (graph.induce S).edgeSet`, and `sixty_six_chains` explicitly counts distinct unordered colour pairs. The omitted labelling bridge is not silently assumed in either theorem.

The pass proves necessary obstruction conditions, not that they are impossible. In particular, it does not prove triangle-free minimal counterexamples, resolve the 18-chain rigidity obstruction, or establish the global insertion conjectures.
