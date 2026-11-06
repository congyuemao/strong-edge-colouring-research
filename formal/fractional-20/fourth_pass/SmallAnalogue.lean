import fourth_pass.SelectionSearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card

namespace Se20Fractional.FourthPass

def cycleCompatible (a b : Fin 5) : Bool :=
  a == b || (a.val + 1) % 5 == b.val || (b.val + 1) % 5 == a.val
def cyclePossible (chosen : List (Fin 5)) (a : Fin 5) : Bool :=
  chosen.all (cycleCompatible a)

theorem cycle_search :
    selectionSearch cyclePossible (fun st a => a :: st) 6 3 [] (List.finRange 5) = true :=
  by decide

/-- A small graph analogue, using the same generic search and its semantic
soundness theorem. The cycle on five vertices has no three-vertex clique. -/
theorem cycle_clique_card_le_two (Q : Finset (Fin 5))
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, cycleCompatible a b = true) : Q.card ≤ 2 := by
  let realizes (st : List (Fin 5)) (m : Finset (Fin 5)) :=
    (∀ a ∈ m, ∀ b ∈ m, cycleCompatible a b = true) ∧ ∀ a ∈ st, a ∈ m
  have hp : ∀ st m a, realizes st m → decide (a ∈ m) = true → cyclePossible st a = true := by
    intro st m a hm ha
    apply List.all_eq_true.mpr
    intro b hb
    exact hm.1 a (of_decide_eq_true ha) b (hm.2 b hb)
  have hs : ∀ st m a, realizes st m → decide (a ∈ m) = true → realizes (a :: st) m := by
    intro st m a hm ha
    refine ⟨hm.1, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact of_decide_eq_true ha
    · exact hm.2 b hb
  have hi := selectionSearch_sound cyclePossible (fun st a => a :: st) realizes
    (fun m a => decide (a ∈ m)) hp hs 6 3 [] (List.finRange 5) cycle_search Q
    ⟨hQ, by simp⟩
  have he : ((List.finRange 5).filter (fun a => decide (a ∈ Q))).toFinset = Q := by
    ext a
    simp
  have hc := List.toFinset_card_of_nodup
    ((List.nodup_finRange 5).filter (fun a => decide (a ∈ Q)))
  rw [he] at hc
  omega

#print axioms selectionSearch_sound
#print axioms cycle_search
#print axioms cycle_clique_card_le_two
end Se20Fractional.FourthPass
