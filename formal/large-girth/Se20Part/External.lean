import Se20Part.Definitions

noncomputable section
open scoped Classical
namespace Se20Part

/-- The cited general theorem, not an axiom. Arithmetic is in ℝ, including subtraction. -/
def Kostochka : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (σ g χ : ℕ),
    5 ≤ σ → 7 ≤ g → DegreeLE G σ → GirthAtLeast G g →
    σ / 2 + 2 ≤ χ →
    (Real.exp 1 / 2) * ((g + 1) / 2 : ℕ) * σ * ((σ : ℝ) + χ - 2) ≤
      (((χ : ℝ) - 1) / ((σ : ℝ) - χ + 1)) ^ ((g + 1) / 2 - 1) →
    G.Colorable χ

def K6 : Prop := ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  DegreeLE G 6 → GirthAtLeast G 21 → G.Colorable 5

def K5 : Prop := ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  DegreeLE G 5 → GirthAtLeast G 35 → G.Colorable 4

theorem kostochka_K6_numeric :
    (Real.exp 1 / 2) * (11 : ℝ) * 6 * (6 + 5 - 2) ≤
      (((5 : ℝ) - 1) / (6 - 5 + 1)) ^ (11 - 1 : ℕ) := by
  have he := Real.exp_one_lt_three
  norm_num at *
  linarith

theorem kostochka_K5_numeric :
    (Real.exp 1 / 2) * (18 : ℝ) * 5 * (5 + 4 - 2) ≤
      (((4 : ℝ) - 1) / (5 - 4 + 1)) ^ (18 - 1 : ℕ) := by
  have he := Real.exp_one_lt_three
  norm_num at *
  linarith

theorem Kostochka.to_K6 (h : Kostochka) : K6 := by
  intro V _ G hd hg
  exact h V G 6 21 5 (by norm_num) (by norm_num) hd hg (by norm_num)
    (by convert kostochka_K6_numeric using 1)

theorem Kostochka.to_K5 (h : Kostochka) : K5 := by
  intro V _ G hd hg
  exact h V G 5 35 4 (by norm_num) (by norm_num) hd hg (by norm_num)
    (by convert kostochka_K5_numeric using 1)

/-- Parts of a partition are nonempty, including in the Δ = 0 case. -/
def Haxell : Prop :=
  ∀ (V I : Type) [Fintype V] [Fintype I] (G : SimpleGraph V)
    (part : V → I) (Δ : ℕ), Function.Surjective part → DegreeLE G Δ →
    (∀ i, 2 * Δ ≤ Fintype.card {v // part v = i}) →
    ∃ f : I → V, (∀ i, part (f i) = i) ∧
      ∀ i j, i ≠ j → ¬ G.Adj (f i) (f j)

/-- Finite probability spaces suffice for the manuscript's random selections. -/
def eventProb {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (E : Set Ω) : ℝ :=
  ∑ ω, if ω ∈ E then p ω else 0

def Avoid {Ω I : Type} (E : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ E i}

/-- General asymmetric finite local lemma, with joint non-neighbor independence. -/
def LovaszLocalLemma : Prop :=
  ∀ (Ω I : Type) [Fintype Ω] [Fintype I] (p : Ω → ℝ) (E : I → Set Ω)
    (D : SimpleGraph I) (x : I → ℝ),
    (∀ ω, 0 ≤ p ω) → (∑ ω, p ω) = 1 →
    (∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ D.Adj i j) →
      eventProb p (E i ∩ Avoid E S) = eventProb p (E i) * eventProb p (Avoid E S)) →
    (∀ i, 0 ≤ x i ∧ x i < 1) →
    (∀ i, eventProb p (E i) ≤ x i * ∏ j ∈ D.neighborFinset i, (1 - x j)) →
    0 < eventProb p (Avoid E Finset.univ)

end Se20Part
