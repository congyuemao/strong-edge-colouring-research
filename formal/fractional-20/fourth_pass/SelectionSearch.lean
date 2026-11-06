import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace Se20Fractional.FourthPass

/-- Exhaustive selection with monotone, model-preserving pruning. Fuel only
limits proof search: exhaustion returns `false`, never a claimed refutation. -/
def selectionSearch {α σ : Type} (possible : σ → α → Bool) (step : σ → α → σ) :
    Nat → Nat → σ → List α → Bool
  | 0, _, _, _ => false
  | fuel + 1, need, state, candidates =>
    if need = 0 then false else
    let viable := candidates.filter (possible state)
    if viable.length < need then true else
    match viable with
    | [] => true
    | a :: rest =>
      selectionSearch possible step fuel need state rest &&
      selectionSearch possible step fuel (need - 1) (step state a) rest

/-- The semantic interface is independent of the model's representation.
Every still-needed element of a genuine model survives pruning, and adding
such an element preserves compatibility with that model. -/
theorem selectionSearch_sound {α σ μ : Type}
    (possible : σ → α → Bool) (step : σ → α → σ)
    (realizes : σ → μ → Prop) (good : μ → α → Bool)
    (hp : ∀ state model a, realizes state model → good model a = true →
      possible state a = true)
    (hs : ∀ state model a, realizes state model → good model a = true →
      realizes (step state a) model)
    (fuel need : Nat) (state : σ) (candidates : List α)
    (hcheck : selectionSearch possible step fuel need state candidates = true) :
    ∀ model, realizes state model → (candidates.filter (good model)).length < need := by
  induction fuel generalizing need state candidates with
  | zero => simp [selectionSearch] at hcheck
  | succ fuel ih =>
    intro model hm
    simp only [selectionSearch] at hcheck
    split at hcheck
    · contradiction
    · rename_i hn
      have hfilter : ((candidates.filter (possible state)).filter (good model)) =
          candidates.filter (good model) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro a ha
        by_cases hg : good model a = true
        · simp [hg, hp state model a hm hg]
        · have hf : good model a = false := Bool.eq_false_iff.mpr hg
          simp [hf]
      split at hcheck
      · rename_i hc
        rw [← hfilter]
        exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) hc
      · split at hcheck
        · rename_i he
          rw [← hfilter, he]
          simpa using Nat.pos_of_ne_zero hn
        · rename_i a rest he
          simp only [Bool.and_eq_true] at hcheck
          obtain ⟨hskip, htake⟩ := hcheck
          rw [← hfilter, he]
          by_cases hg : good model a = true
          · have hi := ih (need - 1) (step state a) rest htake model
              (hs state model a hm hg)
            simp only [List.filter_cons, hg, ↓reduceIte, List.length_cons]
            omega
          · have hf : good model a = false := Bool.eq_false_iff.mpr hg
            simpa [hf] using ih need state rest hskip model hm

theorem selectionSearch_prune {α σ : Type} (possible : σ → α → Bool) (step : σ → α → σ)
    (fuel need : Nat) (st : σ) (cs : List α) (hn : need ≠ 0)
    (hc : (cs.filter (possible st)).length < need) :
    selectionSearch possible step (fuel+1) need st cs = true := by
  simp [selectionSearch,hn,hc]

theorem selectionSearch_split {α σ : Type} (possible : σ → α → Bool) (step : σ → α → σ)
    (fuel need : Nat) (st : σ) (cs : List α) (a : α) (rest : List α) (next : σ)
    (hn : need ≠ 0) (hv : cs.filter (possible st) = a :: rest) (he : step st a = next)
    (hskip : selectionSearch possible step fuel need st rest = true)
    (htake : selectionSearch possible step fuel (need-1) next rest = true) :
    selectionSearch possible step (fuel+1) need st cs = true := by
  simp only [selectionSearch,hn,↓reduceIte,hv]
  split
  · rfl
  · simp only [he,hskip,htake,Bool.true_and]

end Se20Fractional.FourthPass
