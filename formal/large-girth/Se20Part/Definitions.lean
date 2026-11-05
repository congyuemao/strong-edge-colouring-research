import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

noncomputable section
open scoped Classical

namespace Se20Part

/-- Conflicts are always measured in the fixed ambient graph. -/
def L2 {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ G.Adj a b
  symm := ⟨by
    rintro e f ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha,
      hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def StrongColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (L2 G).Colorable k

def MaxDegreeFour {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v ≤ 4

/-- Instance-independent degree bound; on finite graphs this equals the usual degree bound. -/
def DegreeLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v, Nat.card (G.neighborSet v) ≤ d

theorem degreeLE_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) :
    DegreeLE G d ↔ ∀ v, G.degree v ≤ d := by
  simp only [DegreeLE, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

/-- Acyclic graphs satisfy every girth lower bound, as in the manuscript. -/
def GirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → g ≤ p.length

theorem girthAtLeast_iff_egirth {V : Type*} (G : SimpleGraph V) (g : ℕ) :
    GirthAtLeast G g ↔ (g : ℕ∞) ≤ G.egirth := by
  simp [GirthAtLeast, SimpleGraph.le_egirth]

theorem GirthAtLeast.mono {V : Type*} {G : SimpleGraph V} {a b : ℕ}
    (h : GirthAtLeast G b) (hab : a ≤ b) : GirthAtLeast G a :=
  fun v p hp => hab.trans (h v p hp)

abbrev ConflictGraph {V : Type*} (G : SimpleGraph V) (M : Set G.edgeSet) :=
  (L2 G).induce M

def IsMatching {V : Type*} {G : SimpleGraph V} (M : Set G.edgeSet) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → ∀ ⦃v⦄, v ∈ e.val → v ∈ f.val → e = f

def IsInducedMatching {V : Type*} {G : SimpleGraph V} (M : Set G.edgeSet) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → ¬ (L2 G).Adj e f

def External {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : Set V :=
  {v | v ∉ e.val ∧ ∃ u ∈ e.val, G.Adj u v}

def Covered {V : Type*} {G : SimpleGraph V} (M : Set G.edgeSet) : Set V :=
  {v | ∃ e ∈ M, v ∈ e.val}

def EdgeColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : G.edgeSet → Fin k, ∀ i, IsMatching {e | c e = i}

end Se20Part
