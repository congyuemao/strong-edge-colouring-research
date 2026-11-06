import Se20Part.Definitions

namespace Se20Part.TwoRepresentativeSizeChecks

/-- The scalar parameters from S20, section 7; no graph is enumerated. -/
def admissible (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : Prop :=
  s₁.val + t.val ≤ 5 + e₁.val ∧ s₂.val + t.val ≤ 5 + e₂.val ∧
  (s₁.val = 3 → t.val ≤ 2) ∧ (s₂.val = 3 → t.val ≤ 2)

instance (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : Decidable (admissible e₁ e₂ s₁ s₂ t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def highCount (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : ℕ :=
  e₁.val + e₂.val + s₁.val + s₂.val + t.val

def highEdges (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : ℕ :=
  Nat.choose s₁.val 2 + Nat.choose s₂.val 2 +
    e₁.val * (s₁.val + t.val) + e₂.val * (s₂.val + t.val)

def isolatedLow (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : ℕ :=
  (if e₁.val = 0 ∧ s₁.val + t.val = 5 then 1 else 0) +
  (if e₂.val = 0 ∧ s₂.val + t.val = 5 then 1 else 0)

def numerator (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : ℕ :=
  29 * highCount e₁ e₂ s₁ s₂ t - 8 * highEdges e₁ e₂ s₁ s₂ t -
    12 - 15 * isolatedLow e₁ e₂ s₁ s₂ t

def parityBound (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7) : ℕ :=
  let q := numerator e₁ e₂ s₁ s₂ t / 5
  q - ((q + highCount e₁ e₂ s₁ s₂ t) % 2)

def rowBound (e₁ e₂ : Fin 2) (t : Fin 7) : ℕ :=
  (Finset.univ : Finset (Fin 4 × Fin 4)).sup fun s =>
    if admissible e₁ e₂ s.1 s.2 t then parityBound e₁ e₂ s.1 s.2 t else 0

/-- The complete 3×7 displayed table. Zero records the impossible low-representative t=6 case. -/
theorem table :
    (∀ t, rowBound 0 0 t = ![22,27,28,29,26,19,0] t) ∧
    (∀ t, rowBound 0 1 t = ![23,28,29,28,28,25,0] t) ∧
    (∀ t, rowBound 1 1 t = ![24,27,30,29,32,29,24] t) := by
  decide +kernel

/-- All 448 parameter tuples are checked, including the reversed mixed row. -/
theorem checked_bounds : ∀ (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7),
    admissible e₁ e₂ s₁ s₂ t →
    parityBound e₁ e₂ s₁ s₂ t ≤ (if e₁ = 1 ∧ e₂ = 1 then 32 else 29) ∧
    highCount e₁ e₂ s₁ s₂ t + isolatedLow e₁ e₂ s₁ s₂ t ≤ 13 := by
  decide +kernel

/-- The numerical consequence of the port inequality and parity. The
graph-theoretic derivation of these premises is not assumed to be proved. -/
theorem size_bound (e₁ e₂ : Fin 2) (s₁ s₂ : Fin 4) (t : Fin 7)
    (ha : admissible e₁ e₂ s₁ s₂ t) (n : ℕ)
    (hport : n ≤ highCount e₁ e₂ s₁ s₂ t + isolatedLow e₁ e₂ s₁ s₂ t ∨
      5 * n ≤ numerator e₁ e₂ s₁ s₂ t)
    (hparity : n % 2 = highCount e₁ e₂ s₁ s₂ t % 2) :
    n ≤ (if e₁ = 1 ∧ e₂ = 1 then 32 else 29) := by
  obtain ⟨hbound,hsmall⟩ := checked_bounds e₁ e₂ s₁ s₂ t ha
  rcases hport with hport | hport
  · split_ifs <;> omega
  · have hn : n ≤ parityBound e₁ e₂ s₁ s₂ t := by
      dsimp only [parityBound]
      omega
    exact hn.trans hbound

end Se20Part.TwoRepresentativeSizeChecks
