import fourth_pass.PackedSearch
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Card

namespace Se20Fractional.FourthPass.Packed

theorem clear_bit_count (x : Nat) (hx : x ≠ 0) :
    (x &&& (x-1)).bitIndices.length + 1 = x.bitIndices.length := by
  induction x using Nat.binaryRec with
  | zero => contradiction
  | bit b x ih =>
    cases b with
    | false =>
      have hx' : x ≠ 0 := by simpa [Nat.bit_false] using hx
      have he : Nat.bit false x - 1 = Nat.bit true (x-1) := by
        simp only [Nat.bit_false, Nat.bit_true]
        omega
      rw [he, Nat.land_bit]
      simpa [Nat.bitIndices_bit_false] using ih hx'
    | true =>
      have he : Nat.bit true x - 1 = Nat.bit false x := by
        simp [Nat.bit_false, Nat.bit_true]
      rw [he, Nat.land_bit]
      simp [Nat.bitIndices_bit_false, Nat.bitIndices_bit_true]

theorem pop_eq_min (fuel x : Nat) : pop fuel x = min fuel x.bitIndices.length := by
  induction fuel generalizing x with
  | zero => simp [pop]
  | succ fuel ih =>
    by_cases hx : x = 0
    · simp [hx,pop]
    · have hc := clear_bit_count x hx
      simp only [pop, beq_iff_eq, hx, ↓reduceIte, ih]
      omega

def BitSubset (a b : Nat) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

theorem pop_mono {a b : Nat} (hab : BitSubset a b) (fuel : Nat) :
    pop fuel a ≤ pop fuel b := by
  have hs : a.bitIndices.toFinset ⊆ b.bitIndices.toFinset := by
    intro i hi
    simp only [List.mem_toFinset,Nat.mem_bitIndices] at hi ⊢
    exact hab i hi
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup,
    List.toFinset_card_of_nodup Nat.bitIndices_nodup] at hc
  rw [pop_eq_min,pop_eq_min]
  omega

#print axioms pop_eq_min
#print axioms pop_mono
end Se20Fractional.FourthPass.Packed
