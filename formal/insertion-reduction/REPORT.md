**A flaw was found in the proof of Lemma 11.17.** Even in the saturated case, an edge of `Z` can belong to `N(e)`. Consequently the claim that `uw` has exactly 13 conflicts in `N(e)` is also false. This is a flaw in the supplied proof, not a counterexample to the lemma: the repaired lemma, including its at-most-one-recolouring conclusion, is proved in Lean and used in the main reduction.

Here is the full counterexample. Vertices are `0,...,19`, with
`u=0`, `v=1`, `w=2`, `x₂=3`, `x₃=4`, `y₂=5`, `y₃=6`, `z₁=7`, `z₂=8`.
The complete edge list, in order, is:

```text
01, 02, 12, 03, 04, 15, 16, 27, 28,
39, 3-10, 3-11, 4-12, 4-13, 4-14,
57, 5-15, 5-16, 6-17, 6-18, 6-19.
```

Leave edge `01` uncoloured. Give the remaining edges, in the displayed order, colours `0,...,19`. This is a proper partial strong colouring because all coloured edges have different colours. Vertices `0,...,6` have degree four, vertex `7` has degree two, and vertices `8,...,19` have degree one. All 20 coloured edges conflict with `01`. Here `Z={57}`, and `57` belongs to `Y` and to `N(01)`. It also conflicts with `02` through the joining edge `27`. Thus `02=uw` has **14**, rather than 13, conflicts in `N(01)`.

[AuditExamples.lean](Se20Insertion/AuditExamples.lean) contains this graph and kernel-checked proofs of the overlapping conflicts. The independent, reproducible [audit-example.ps1](audit-example.ps1) checks the complete degree list, saturation, colouring, `Z`, and the count 14; its output is [TRIANGLE_COUNTEREXAMPLE.json](TRIANGLE_COUNTEREXAMPLE.json). The full numerical check is a PowerShell calculation, not a Lean theorem. The Lean overlap certificates and the repaired general triangle theorem do not rely on that calculation.

The repaired proof permits `Z ∩ N(e) ≠ ∅`. It uses the exact cover of the conflicts of `uv` by incidences at `(N(u) − {v}) ∪ (N(v) − {u})`. In the blocked triangle case this cover has 20 edges, so its five incidence sets are disjoint and the colours are injective on `N(e)`. At least eight of those edges avoid `u,v,w`; the crude bound of twelve on the union of their incidence sets suffices here. Their distinct colours cannot all occur on the at most six edges of `Z`. A colour absent from `Z` must be free at `uw` or `vw`, allowing the single recolouring. No false disjointness assumption about `Z` is used.

There is also a boundary gap in the informal argument for Corollary 11.8: choosing a second colour `d` outside `Y`, distinct from a missing colour `c`, requires at least two colours outside `Y`. That argument does not cover `|Y|=19`. This is not an established counterexample to the corollary. The general chain-obstruction assertion was not formalized; the numerical count was proved with saturation stated explicitly.

No counterexample to any of the four conjectures was found. The new star reduction is verified after repairing Lemma 11.17. In particular, no colouring of `G − e` is used as a partial colouring of `G`.

**All requested main implications are proved.** Their exact source signatures are:

```lean
theorem strongColourable_of_conj119Star (h : Conj119Star) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20

theorem conj119Star_of_conj119 : Conj119 → Conj119Star

theorem strongColourable_of_conj1115 (h : Conj1115) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20

theorem strongColourable_of_conj1126 (h : Conj1126Weak) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20

theorem strongColourable_of_starInsertion (h : StarInsertion) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20

theorem strongColourable_of_conj119 (h : Conj119) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20
```

All declarations are in namespace `Se20Insertion`; the source opens `Classical` locally for instances. The last theorem is an additional direct reduction from Conjecture 11.9.

| Result | File / declaration |
|---|---|
| `Conj119Star` implies the bound; abstract restricted star insertion implies the bound | [StarReduction.lean](Se20Insertion/StarReduction.lean), `strongColourable_of_conj119Star`, `strongColourable_of_starInsertion` |
| `Conj119 → Conj119Star`; the three alternatives yield an insertion | [Insertion.lean](Se20Insertion/Insertion.lean), `conj119Star_of_conj119`, `starInsertion_of_conj119Star` |
| `Conj1115`, `Conj1126Weak`, and `Conj119` imply the bound for arbitrary finite vertex types | [Fragmentation.lean](Se20Insertion/Fragmentation.lean) |
| Conflict monotonicity, induced-subgraph equality, vertex-deletion equality, transport from `Fin n` | [GraphBasics.lean](Se20Insertion/GraphBasics.lean), `L2Map`, `L2_embedding_adj_iff`, `L2_deleteVertex_adj_iff`, `strongColourable_of_fin` |
| One-component and multiple-component swaps preserve properness; separability frees a colour | [Kempe.lean](Se20Insertion/Kempe.lean), `component_closed`, `swap`, `jointSeparable_frees`, `separable_frees` |
| Theorem 11.7 for `k=1`; the `k=0` separable insertion | [Insertion.lean](Se20Insertion/Insertion.lean), `singleInsertion`; [Kempe.lean](Se20Insertion/Kempe.lean), `insert_of_separable` |
| Theorem 11.14 | [Insertion.lean](Se20Insertion/Insertion.lean), `colourClassInsertion` |
| Theorem 11.18 | [GroupedInsertion.lean](Se20Insertion/GroupedInsertion.lean), `groupedColourClassInsertion` |
| Ambient conflict bounds 24 and 20 for a triangle edge | [ConflictBounds.lean](Se20Insertion/ConflictBounds.lean) |
| Lemma 11.17, with the count of changed previously coloured edges at most one | [Triangle.lean](Se20Insertion/Triangle.lean), [TriangleInsertion.lean](Se20Insertion/TriangleInsertion.lean), `triangle_local_repair`, `triangle_insertion` |
| Lemma 11.36 | [TriangleInsertion.lean](Se20Insertion/TriangleInsertion.lean), `triangle_edges_last` |
| Lemma 11.37(1) and (2) | [Exceptional.lean](Se20Insertion/Exceptional.lean), `exceptional_triangleFree_incident_card`, `strongColourable_of_all_exceptional` |
| Triangle-free matching conflicts at most six; seven-colouring | [Greedy.lean](Se20Insertion/Greedy.lean), `matching_conflicts_le_six`, `matching_seven_colourable` |
| The regular completion in Proposition 11.38 | [RegularCompletion.lean](Se20Insertion/RegularCompletion.lean), `double_degree`, `regularCompletion` |
| Suppression is simple and preserves all remaining vertex degrees | [Suppression.lean](Se20Insertion/Suppression.lean), `suppress_degree`, `suppress_regular` |
| The vertex-deletion colouring is a star state; repeatedly filling that star | [VertexDeletion.lean](Se20Insertion/VertexDeletion.lean), `starColouring_of_deleteColourable`, `fill_star_fin` |
| Proposition 11.27, existence of a fragmentation local maximum and the colouring induction | [Fragmentation.lean](Se20Insertion/Fragmentation.lean), `exists_locallyMaximal`, `strongColourable_fin_of_conj1126` |
| Lemma 11.6(1), including the weaker trivial-separability assumption | [HoleMoves.lean](Se20Insertion/HoleMoves.lean), `single_saturated_of_no_trivial` |
| Lemma 11.6(2), and the length-one count 15 | [SupportCounts.lean](Se20Insertion/SupportCounts.lean), `single_neighbour_at_least_fifteen` |
| Lemma 11.11: legal, reversible hole move, class sizes preserved, new hole blocked | [HoleMoves.lean](Se20Insertion/HoleMoves.lean), `holeMove`, `holeMove_single_reverse`, `holeMove_reverse_domain`, `holeMove_reverse`, `holeMove_class_card`, `holeMove_blocked` |
| Lemma 11.12 | [HoleMoves.lean](Se20Insertion/HoleMoves.lean), `holeMove_inseparable_moved_colour` |
| Lemma 11.13 | [HoleMoves.lean](Se20Insertion/HoleMoves.lean), `inherited_inseparable` |
| At least `16 + k` single colours when blocked, with `k` other uncoloured conflicts | [Counting.lean](Se20Insertion/Counting.lean), `at_least_sixteen_add_uncoloured_single` |
| Corollary 11.8's numerical bound for colours outside `Y`, under explicit saturation | [SupportCounts.lean](Se20Insertion/SupportCounts.lean), `outside_colours_single_count` |

The partial-colouring representation uses a total colour function with unused values outside its specified domain. [Greedy.lean](Se20Insertion/Greedy.lean), `partialColouring_iff_colourable`, proves that existence of this representation is equivalent to colourability of the induced graph. Hole-move reversibility is accordingly equality on the coloured domain, not equality of irrelevant values outside it. The grouped insertion theorem allows any cover of the colour class by groups, so in particular applies to the stipulated partitions.

For Proposition 11.27, a global maximum of `componentCount` among the finite set of proper colourings gives a local maximum. This replaces the hill-climbing argument without changing the conjecture or the final conclusion. Reachability of that global maximum from a prescribed initial colouring by Kempe swaps is neither asserted nor needed. The induction is on coloured subsets of the fixed `L2 G`.

**Hypotheses and unfinished supporting work.** `Conj119Star`, `Conj119`, `Conj1115`, and `Conj1126Weak` remain unproved propositions and occur only as explicit hypotheses of implications. `StarInsertion` is the explicit hypothesis of the abstract reduction; it is proved from `Conj119Star`. No triangle insertion, regular completion, exceptional-vertex result, or suppression result is assumed in any main theorem.

The following were not formalized:

- The general `k ≥ 2` chain version of Theorem 11.7. The requested main reductions use the proved `k=1` version.
- The full chain-obstruction/extension assertion of Corollary 11.8. Its counting inequality, including the sharpened count 15, is proved as described above.
- Lemma 11.16 (`componentCount ≥ 7m`). The upper bound `componentCount ≤ 19m` and a particular hill-climbing execution are also not formalized; finiteness suffices for the proved fragmentation reduction.
- The optional Proposition 11.35 was not separately stated; Proposition 11.38 is proved directly.
- The stretch results 11.24–11.25, 11.19, and 11.20–11.22 were not attempted.

There are no unfinished Lean declarations or partial Lean files in the default target. Unimplemented results have no placeholder declarations.

**Validation.** The full sequential build finished successfully with exit code 0 on 2026-11-05 (`Get-Date`: 00:46). The project uses the specified Lean `4.35.0-rc4` toolchain and existing local Mathlib dependency. [build.ps1](build.ps1) compiles every project module sequentially and then the default root `Se20Insertion.lean`. It uses `lake env lean` only to obtain the existing dependency paths; it does not build or fetch dependencies. All generated files are in this workspace. No installation, commit, or push was performed. See [BUILD.log](BUILD.log) for the final build result and [AXIOMS.txt](AXIOMS.txt) for the axiom audit. A source scan found no `sorry`, `admit`, new `axiom`, `native_decide`, or `Lean.ofReduceBool`.

The exact axiom output for the main theorems is:

```text
'Se20Insertion.strongColourable_of_conj119Star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.conj119Star_of_conj119' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1115' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj1126' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_starInsertion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.strongColourable_of_conj119' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact definitions and conjecture statements follow, copied from [Definitions.lean](Se20Insertion/Definitions.lean), including the context needed to interpret them. In particular, the conflict relation always uses the original `G`, pair components use its fixed conflict graph, all conjectures quantify over `SimpleGraph (Fin n)`, and the local-maximum predicate concerns a single entire nonempty component at a time.

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

/-! All conflicts in this development are in the fixed ambient graph. -/
noncomputable section
open scoped Classical

namespace Se20Insertion

abbrev Colour := Fin 20

/-- The conflict graph on actual unordered edges of the ambient graph. -/
def L2 {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ G.Adj a b
  symm := ⟨by
    rintro e f ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha,
      hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def StrongColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (L2 G).Colorable k

/-- Values outside `F` are unused. Properness refers to the ambient graph `H`. -/
structure PartialColouring {W : Type*} (H : SimpleGraph W) (F : Finset W) where
  colour : W → Colour
  proper : ∀ ⦃x y⦄, x ∈ F → y ∈ F → H.Adj x y → colour x ≠ colour y

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def Neighbour (φ : PartialColouring H F) (f : W) (a : Colour) (g : W) : Prop :=
  g ∈ F ∧ H.Adj f g ∧ φ.colour g = a

def Free (φ : PartialColouring H F) (f : W) (a : Colour) : Prop :=
  ¬ ∃ g, φ.Neighbour f a g

def Single (φ : PartialColouring H F) (f : W) (p : Colour) (g : W) : Prop :=
  φ.Neighbour f p g ∧ ∀ g', φ.Neighbour f p g' → g' = g

def Bicoloured (φ : PartialColouring H F) (a b : Colour) : Set W :=
  {g | g ∈ F ∧ (φ.colour g = a ∨ φ.colour g = b)}

def KempeGraph (φ : PartialColouring H F) (a b : Colour) :
    SimpleGraph (φ.Bicoloured a b) := H.induce (φ.Bicoloured a b)

/-- Two edges are in the same component of the induced two-colour graph. -/
def SameComponent (φ : PartialColouring H F) (a b : Colour) (x y : W) : Prop :=
  ∃ hx : x ∈ φ.Bicoloured a b, ∃ hy : y ∈ φ.Bicoloured a b,
    (φ.KempeGraph a b).Reachable ⟨x, hx⟩ ⟨y, hy⟩

def Separable (φ : PartialColouring H F) (f : W) (a b : Colour) : Prop :=
  ∀ x y, φ.Neighbour f a x → φ.Neighbour f b y → ¬ φ.SameComponent a b x y

def JointSeparable (φ : PartialColouring H F) (B : Set W) (a b : Colour) : Prop :=
  ∀ f ∈ B, ∀ g ∈ B, ∀ x y,
    φ.Neighbour f a x → φ.Neighbour g b y → ¬ φ.SameComponent a b x y

def Stuck (φ : PartialColouring H F) (e : W) : Prop :=
  (∀ a, ∃ g, φ.Neighbour e a g) ∧
    ∀ a b, a ≠ b → ¬ φ.Separable e a b

/-- A union of whole components of the induced two-colour graph. -/
def KempeClosed (φ : PartialColouring H F) (a b : Colour) (S : Set W) : Prop :=
  S ⊆ φ.Bicoloured a b ∧
    ∀ ⦃x y⦄, x ∈ S → y ∈ φ.Bicoloured a b → H.Adj x y → y ∈ S

def swapColour (φ : PartialColouring H F) (a b : Colour) (S : Set W) (x : W) : Colour :=
  if x ∈ S then Equiv.swap a b (φ.colour x) else φ.colour x

/-- The actual connected components are counted, including isolated coloured edges. -/
def componentCount (φ : PartialColouring H F) : ℕ :=
  ∑ a : Colour, ∑ b : Colour,
    if a < b then Nat.card (φ.KempeGraph a b).ConnectedComponent else 0

/-- `ψ` is obtained by one swap on one entire nonempty component. -/
def OneKempeSwap (φ ψ : PartialColouring H F) : Prop :=
  ∃ a b : Colour, a ≠ b ∧ ∃ x, x ∈ φ.Bicoloured a b ∧
    ∀ y, ψ.colour y = φ.swapColour a b {y | φ.SameComponent a b x y} y

def LocallyMaximal (φ : PartialColouring H F) : Prop :=
  ∀ ψ, φ.OneKempeSwap ψ → ψ.componentCount ≤ φ.componentCount

def Repairable (φ : PartialColouring H F) (e : W) : Prop :=
  (∃ a, φ.Free e a) ∨ (∃ a b, a ≠ b ∧ φ.Separable e a b) ∨
    ∃ p f, φ.Single e p f ∧ ∃ a b,
      a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b

end PartialColouring

def OnTriangle {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : Prop :=
  ∃ u v w, e.val = s(u, v) ∧ G.Adj u w ∧ G.Adj v w

def Nonexceptional {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ M : ((G.induce (G.neighborSet v))ᶜ).Subgraph, M.IsPerfectMatching

def MaxDegreeFour {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v ≤ 4

def FourRegular {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v = 4

def StarSet {V : Type*} (G : SimpleGraph V) (v : V) (U : Finset G.edgeSet) : Prop :=
  U.Nonempty ∧ ∀ e ∈ U, v ∈ e.val

/-- Conjectures quantify only over graphs on `Fin n`. -/
def Conj119Star : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ φ : PartialColouring (L2 G) (Finset.univ \ U),
        ∃ e ∈ U, φ.Repairable e

def Conj119 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ (F : Finset G.edgeSet) (φ : PartialColouring (L2 G) F) (e : G.edgeSet),
      e ∉ F → φ.Stuck e →
        ∃ p f, φ.Single e p f ∧ ∃ a b,
          a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b

def Conj1115 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ (F : Finset G.edgeSet) (φ : PartialColouring (L2 G) F) (e : G.edgeSet),
      e ∉ F → φ.Stuck e →
        ∃ c a b, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          φ.JointSeparable {g | φ.Neighbour e c g} a b

def Conj1126Weak : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), MaxDegreeFour G →
    ∀ (F : Finset G.edgeSet) (h : G.edgeSet), h ∈ F →
      ∀ φ : PartialColouring (L2 G) (F.erase h), φ.LocallyMaximal →
        (∃ a, φ.Free h a) ∨ (∃ a b, a ≠ b ∧ φ.Separable h a b)

def StarInsertion : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), FourRegular G →
    ∀ v, Nonexceptional G v → ∀ U : Finset G.edgeSet,
      StarSet G v U → (∀ e ∈ U, ¬ OnTriangle G e) →
      ∀ _φ : PartialColouring (L2 G) (Finset.univ \ U),
        ∃ e ∈ U, Nonempty (PartialColouring (L2 G) (insert e (Finset.univ \ U)))

end Se20Insertion

```
