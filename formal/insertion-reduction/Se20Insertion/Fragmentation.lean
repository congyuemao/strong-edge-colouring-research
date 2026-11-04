import Se20Insertion.Insertion
import Se20Insertion.GraphBasics

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

theorem colour_injective : Function.Injective (colour : PartialColouring H F → W → Colour) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  cases h
  rfl

instance [Finite W] : Finite (PartialColouring H F) :=
  Finite.of_injective colour colour_injective

/-- A global maximum exists in the finite space of proper colourings, hence
is a local maximum for single-component Kempe swaps (Proposition 11.27). -/
theorem exists_locallyMaximal [Finite W] (φ : PartialColouring H F) :
    ∃ ψ : PartialColouring H F, ψ.LocallyMaximal := by
  letI := Fintype.ofFinite (PartialColouring H F)
  obtain ⟨ψ, _, hψ⟩ := Finset.exists_max_image Finset.univ componentCount
    (Finset.univ_nonempty_iff.mpr ⟨φ⟩)
  exact ⟨ψ, fun θ _ => hψ θ (Finset.mem_univ _)⟩

end PartialColouring

theorem strongColourable_fin_of_conj1126 (h : Conj1126Weak) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hΔ : MaxDegreeFour G) : StrongColourable G 20 := by
  apply PartialColouring.colourable_of_insertion
  intro F φ e he
  obtain ⟨ψ, hψ⟩ := φ.exists_locallyMaximal
  have herase : (insert e F).erase e = F := Finset.erase_insert he
  have hc : (∃ a, ψ.Free e a) ∨ (∃ a b, a ≠ b ∧ ψ.Separable e a b) := by
    have hh := h n G hΔ (insert e F) e (Finset.mem_insert_self e F)
    rw [herase] at hh
    exact hh ψ hψ
  rcases hc with ⟨a, ha⟩ | ⟨a, b, hab, hs⟩
  · exact ⟨ψ.insertFree e a ha⟩
  · exact ψ.insert_of_separable hab hs

theorem strongColourable_of_conj119 (h : Conj119) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20 :=
  strongColourable_of_fin (fun _ G hΔ => strongColourable_fin_of_conj119 h G hΔ) G hΔ

theorem strongColourable_of_conj1115 (h : Conj1115) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20 :=
  strongColourable_of_fin (fun _ G hΔ => strongColourable_fin_of_conj1115 h G hΔ) G hΔ

theorem strongColourable_of_conj1126 (h : Conj1126Weak) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ 4) : StrongColourable G 20 :=
  strongColourable_of_fin (fun _ G hΔ => strongColourable_fin_of_conj1126 h G hΔ) G hΔ

end Se20Insertion
