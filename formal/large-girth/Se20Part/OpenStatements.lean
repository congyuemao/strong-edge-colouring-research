import Se20Part.Selection
import Se20Part.ColouringTheorems

/-! First-pass target specifications, recorded as propositions, never as axioms.
The second- and third-pass modules now prove all of these specifications.
`CompletedTheorems.lean` discharges the B+ counting and numerical assumptions.
The proposition definitions below are unchanged. -/
noncomputable section
open scoped Classical
namespace Se20Part

def Separated {V : Type*} (G : SimpleGraph V) (d : ℕ) (D : Set G.edgeSet) : Prop :=
  ∀ e ∈ D, ∀ f ∈ D, e ≠ f → ¬ EdgeWithin G (d-1) e f

def NearDefects {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) : Set G.edgeSet :=
  {h | h ∈ M ∧ ∃ r ∈ D, (L2 G).Adj h r}

def ProblemAt {V : Type*} (G : SimpleGraph V) (M : Set G.edgeSet)
    (r h : G.edgeSet) : Prop :=
  h ∈ M ∧ (L2 G).Adj h r ∧ Nat.card (External G h) = 6 ∧ External G h ⊆ Covered M

def Problem {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) (h : G.edgeSet) : Prop :=
  ∃ r ∈ D, ProblemAt G M r h

def Dead {V : Type*} (G : SimpleGraph V) (D M : Set G.edgeSet) (h : G.edgeSet) : Prop :=
  Problem G D M h ∧
    ∀ f ∈ M, (L2 G).Adj h f → f ∈ NearDefects G D M

def VertexEdgeDistance {V : Type*} (G : SimpleGraph V) (v : V) (e : G.edgeSet) (d : ℕ) : Prop :=
  (∀ x ∈ e.val, (d : ℕ∞) ≤ G.edist v x) ∧ ∃ x ∈ e.val, G.edist v x = d

def TwoDegreeDecompositionStatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G →
    ∃ c : G.edgeSet → Fin 2, ∀ i v,
      Nat.card {e : G.edgeSet // c e = i ∧ v ∈ e.val} ≤ 2

def LocalDominatorsStatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G → GirthAtLeast G 11 →
    ∀ (M : Set G.edgeSet), IsMatching M → ∀ r : G.edgeSet, r ∉ M →
      ∃ d : {h // ProblemAt G M r h} → M,
        (∀ h, (L2 G).Adj h.val (d h).val ∧
          ∃ p t, (d h).val.val = s(p,t) ∧
            VertexEdgeDistance G p r 2 ∧ VertexEdgeDistance G t r 3) ∧
        ∀ h h', h ≠ h' → ¬ EdgeWithin G 3 (d h).val (d h').val

def DeadEdgeAStatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G → GirthAtLeast G 8 →
    ∀ (D M : Set G.edgeSet), IsInducedMatching D → IsMatching M → Disjoint D M →
      ∀ h, Dead G D M h → ∀ r ∈ D,
        (∃ u, u ∈ h.val ∧ u ∈ r.val) →
        3 ≤ Nat.card {r' : G.edgeSet // r' ∈ D ∧ r' ≠ r ∧ EdgeWithin G 4 r r' ∧
          ∃ f ∈ M, (L2 G).Adj h f ∧ (L2 G).Adj f r'}

def DeadEdgeBStatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G → GirthAtLeast G 9 →
    ∀ (D M : Set G.edgeSet), IsInducedMatching D → IsMatching M → Disjoint D M →
      ∀ h, Dead G D M h → (∀ u ∈ h.val, u ∉ Covered D) →
        6 ≤ Nat.card {r : G.edgeSet // r ∈ D ∧
          ∃ f ∈ M, (L2 G).Adj h f ∧ (L2 G).Adj f r}

def NoDeadEdgesStatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), MaxDegreeFour G → GirthAtLeast G 6 →
    ∀ (D M : Set G.edgeSet), Separated G 5 D → IsMatching M → Disjoint D M →
      ∀ h, ¬ Dead G D M h

/-- Infinite trees are genuine simple graphs on an arbitrary infinite vertex type.
The finite-neighbor condition is explicit, so Nat.card cannot hide infinite degrees. -/
structure InfiniteFourTree where
  Vertex : Type
  infinite : Infinite Vertex
  graph : SimpleGraph Vertex
  isTree : graph.IsTree
  finite_neighbors : ∀ v, (graph.neighborSet v).Finite
  degree_four : ∀ v, Nat.card (graph.neighborSet v) = 4

def TwoFactor {V : Type*} {G : SimpleGraph V} (F : Set G.edgeSet) : Prop :=
  ∀ v, Nat.card {e : G.edgeSet // e ∈ F ∧ v ∈ e.val} = 2

def TreeLemmaStatement : Prop :=
  ∀ (T : InfiniteFourTree) (F₁ F₂ D M : Set T.graph.edgeSet),
    Disjoint F₁ F₂ → F₁ ∪ F₂ = Set.univ → TwoFactor F₁ → TwoFactor F₂ →
    Separated T.graph 5 D → IsMatching M → M ⊆ F₂ \ D →
    (∀ v, v ∉ Covered D → v ∈ Covered M) →
    ∃ J : Set T.graph.edgeSet, J ⊆ M ∧ IsInducedMatching J ∧
      (∀ e ∈ J, ∀ r ∈ D, ¬ (L2 T.graph).Adj e r) ∧
      ∀ h, Problem T.graph D M h → ∃ d ∈ J, (L2 T.graph).Adj h d

def TheoremBStatement : Prop :=
  Kostochka → Haxell → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    MaxDegreeFour G → GirthAtLeast G 39360 → StrongColourable G 20

def TheoremBPlusStatement : Prop :=
  Kostochka → LovaszLocalLemma → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    MaxDegreeFour G → GirthAtLeast G 5710 → StrongColourable G 20

end Se20Part
