import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-! Faithful definitions. A finite family may list a stable set more than once;
merging equal sets gives exactly the usual nonnegative weighting of stable sets. -/
namespace Se20Fractional
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def Stable (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

def Clique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b

noncomputable def neighbors (G : SimpleGraph V) (U : Finset V) (v : V) : Finset V :=
  by classical exact U.filter (G.Adj v)

noncomputable def degreeOn (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ :=
  (neighbors G U v).card

structure Colouring (G : SimpleGraph V) (U : Finset V) where
  n : ℕ
  sets : Fin n → Finset V
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  stable : ∀ i, Stable G (sets i)
  subset : ∀ i, sets i ⊆ U
  cover : ∀ v ∈ U, 1 ≤ ∑ i, if v ∈ sets i then weight i else 0

noncomputable def Colouring.total {G : SimpleGraph V} {U : Finset V}
    (c : Colouring G U) : ℝ := ∑ i, c.weight i

def FractionalColourableOn (G : SimpleGraph V) (U : Finset V) (k : ℝ) : Prop :=
  ∃ c : Colouring G U, c.total ≤ k

def FractionalColourable (G : SimpleGraph V) (k : ℝ) : Prop :=
  FractionalColourableOn G univ k

/-- The graph on actual unordered edges, with precisely the conflicts in the brief. -/
def L2 (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ G.Adj a b
  symm := ⟨by
    rintro e f ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha, hab.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

@[simp] theorem mem_neighbors (G : SimpleGraph V) (U : Finset V) (v w : V) :
    w ∈ neighbors G U v ↔ w ∈ U ∧ G.Adj v w := by
  classical
  simp [neighbors]

theorem stable_subset {G : SimpleGraph V} {S T : Finset V}
    (h : Stable G S) (hTS : T ⊆ S) : Stable G T :=
  fun a ha b hb => h a (hTS ha) b (hTS hb)

theorem Colouring.total_nonneg {G : SimpleGraph V} {U : Finset V}
    (c : Colouring G U) : 0 ≤ c.total :=
  Finset.sum_nonneg fun i _ => c.nonneg i

theorem degreeOn_mono (G : SimpleGraph V) {U T : Finset V} (h : U ⊆ T) (v : V) :
    degreeOn G U v ≤ degreeOn G T v := by
  classical
  apply Finset.card_le_card
  intro w hw
  simp only [mem_neighbors] at hw ⊢
  exact ⟨h hw.1, hw.2⟩

end Se20Fractional
