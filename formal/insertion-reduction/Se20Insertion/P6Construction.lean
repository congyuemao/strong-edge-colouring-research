import Se20Insertion.P2Geometry
import Se20Insertion.RimCounting

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.P6

/-- L and U each have two labelled leaves for each centre. -/
abbrev Leaf (I : Type*) := I × Fin 2
abbrev Vertex (I : Type*) := I ⊕ (Leaf I ⊕ Leaf I)

def centre {I : Type*} (i : I) : Vertex I := Sum.inl i
def lower {I : Type*} (i : Leaf I) : Vertex I := Sum.inr (Sum.inl i)
def upper {I : Type*} (i : Leaf I) : Vertex I := Sum.inr (Sum.inr i)

/-- An arbitrary simple bipartite relation supplies the L--U edges. -/
def graph {I : Type*} (B : Leaf I → Leaf I → Prop) : SimpleGraph (Vertex I) where
  Adj x y := match x, y with
    | .inl i, .inr (.inl l) => i = l.1
    | .inl i, .inr (.inr u) => i = u.1
    | .inr (.inl l), .inl i => i = l.1
    | .inr (.inr u), .inl i => i = u.1
    | .inr (.inl l), .inr (.inr u) => B l u
    | .inr (.inr u), .inr (.inl l) => B l u
    | _, _ => False
  symm := ⟨by rintro (i | (l | u)) (j | (m | v)) <;> simp_all⟩
  loopless := ⟨by rintro (i | (l | u)) <;> simp⟩

def kind {I : Type*} : Vertex I → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def counts : Fin 3 → Fin 3 → ℕ := ![![0,2,2], ![1,0,3], ![1,3,0]]

/-- The incidence specification of C/L/U, for use independently of labels. -/
structure Pattern {V : Type*} [Fintype V] (G : SimpleGraph V) where
  kind : V → Fin 3
  neighbours : ∀ x i, ((G.neighborFinset x).filter (fun y => kind y = i)).card = counts (kind x) i

variable {I : Type*} [Fintype I] (B : Leaf I → Leaf I → Prop)

def ThreeRegular : Prop :=
  (∀ l, (Finset.univ.filter (B l)).card = 3) ∧
  (∀ u, (Finset.univ.filter (fun l => B l u)).card = 3)

theorem vertex_card : Fintype.card (Vertex I) = 5 * Fintype.card I := by
  simp [Vertex, Leaf]
  omega

theorem part_card (i : Fin 3) :
    (Finset.univ.filter (fun x : Vertex I => kind x = i)).card =
      if i = 0 then Fintype.card I else 2 * Fintype.card I := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  fin_cases i <;> simp [Vertex, Leaf, kind, Fintype.sum_sum_type] <;> omega

theorem graph_neighbours (hB : ThreeRegular B) (x : Vertex I) (i : Fin 3) :
    (((graph B).neighborFinset x).filter (fun y => kind y = i)).card = counts (kind x) i := by
  have he : ((graph B).neighborFinset x).filter (fun y => kind y = i) =
      Finset.univ.filter (fun y => (graph B).Adj x y ∧ kind y = i) := by
    ext y
    simp
  rw [he]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rcases x with x | (x | x) <;> fin_cases i <;>
    simp [graph, kind, counts, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Leaf, ← Finset.card_filter, hB.1, hB.2]
  all_goals
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp [apply_ite]

def pattern (hB : ThreeRegular B) : Pattern (graph B) :=
  ⟨kind, graph_neighbours B hB⟩

namespace Pattern
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

include P in
theorem degree : FourRegular G := by
  intro x
  have hp := Finset.sum_card_fiberwise_eq_card_filter
    (s := G.neighborFinset x) (t := (Finset.univ : Finset (Fin 3))) (g := P.kind)
  simp only [Finset.mem_univ, Finset.filter_true] at hp
  simp_rw [P.neighbours] at hp
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hp
  have hs : (∑ i : Fin 3, counts (P.kind x) i) = 4 := by
    generalize P.kind x = k
    fin_cases k <;> decide
  omega

theorem adjacent_different {x y : V} (hxy : G.Adj x y) : P.kind x ≠ P.kind y := by
  intro he
  have hc := P.neighbours x (P.kind x)
  have hz : counts (P.kind x) (P.kind x) = 0 := by
    generalize P.kind x = k
    fin_cases k <;> rfl
  rw [hz, Finset.card_eq_zero] at hc
  have hm : y ∈ (G.neighborFinset x).filter (fun y => P.kind y = P.kind x) := by
    simp [hxy,he]
  rw [hc] at hm
  exact Finset.notMem_empty _ hm

end Pattern
end Se20Insertion.P6
