import Se20Part.CompactTriangles

noncomputable section
open scoped Classical
namespace Se20Part.Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H R : SimpleGraph W)

/-- All monochromatic complete obstructions, as vertex sets. When capacities
avoid two these are precisely the exceptional components in the manuscript. -/
def badCliques (d : C → ℕ) (π : W → C) : Finset (Finset W) :=
  Finset.univ.filter (fun T => ∃ c, T.card = d c + 1 ∧
    (∀ x ∈ T, π x = c) ∧ H.IsClique (T : Set W))

theorem mem_badCliques (d : C → ℕ) (π : W → C) (T : Finset W) :
    T ∈ badCliques H d π ↔ ∃ c, T.card = d c + 1 ∧
      (∀ x ∈ T, π x = c) ∧ H.IsClique (T : Set W) := by
  simp only [badCliques,Finset.mem_filter,Finset.mem_univ,true_and]

def CliqueMinimumTwo (d : C → ℕ) (π : W → C) : Prop :=
  WeightedMinimum H d π ∧ ∀ σ, WeightedMinimum H d σ →
    (badCliques H d π).card ≤ (badCliques H d σ).card

/-- `energy R` counts twice the monochromatic pairs in R. In the edge
application R is the line graph, so this is exactly twice the tie-breaker T. -/
def CliqueMinimumThree (d : C → ℕ) (π : W → C) : Prop :=
  CliqueMinimumTwo H d π ∧ ∀ σ, CliqueMinimumTwo H d σ → energy R π ≤ energy R σ

theorem exists_cliqueMinimumThree [Nonempty C] (d : C → ℕ) :
    ∃ π : W → C, CliqueMinimumThree H R d π := by
  obtain ⟨π,hπ⟩ := exists_weighted_minimum H d
  let A : Finset (W → C) := Finset.univ.filter (WeightedMinimum H d)
  obtain ⟨σ,hσ,hsmin⟩ := A.exists_min_image (fun s => (badCliques H d s).card)
    ⟨π,by simp [A,hπ]⟩
  have hs : CliqueMinimumTwo H d σ :=
    ⟨(Finset.mem_filter.mp hσ).2,fun τ hτ => hsmin τ (by simp [A,hτ])⟩
  let B : Finset (W → C) := Finset.univ.filter (CliqueMinimumTwo H d)
  obtain ⟨τ,hτ,htmin⟩ := B.exists_min_image (energy R) ⟨σ,by simp [B,hs]⟩
  exact ⟨τ,(Finset.mem_filter.mp hτ).2,fun ρ hρ => htmin ρ (by simp [B,hρ])⟩

theorem badClique_neighbours {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T) :
    T.erase x = Finset.univ.filter (fun y => H.Adj x y ∧ π y = π x) := by
  obtain ⟨c,ht,hc,hcl⟩ := (mem_badCliques H d π T).mp hT
  have hsub : T.erase x ⊆ Finset.univ.filter (fun y => H.Adj x y ∧ π y = π x) := by
    intro y hy
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcl hx hy hne.symm,(hc y hy).trans (hc x hx).symm⟩
  apply Finset.eq_of_subset_of_card_le hsub
  have hb := hΔ x
  rw [degreeIn_eq_card,hc x hx] at hb
  have hh := Finset.card_erase_add_one hx
  rw [hc x hx]
  omega

theorem badClique_unique_at {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    {T S : Finset W} (hT : T ∈ badCliques H d π) (hS : S ∈ badCliques H d π)
    {x : W} (hx : x ∈ T) (hxS : x ∈ S) : T = S := by
  have hh := (badClique_neighbours H hΔ hT hx).trans (badClique_neighbours H hΔ hS hxS).symm
  have := congrArg (fun s : Finset W => insert x s) hh
  simpa only [Finset.insert_erase hx,Finset.insert_erase hxS] using this

theorem badClique_own_degree {d : C → ℕ} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ d (π v))
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T) :
    degreeIn H π x (π x) = d (π x) := by
  obtain ⟨c,ht,hc,hcl⟩ := (mem_badCliques H d π T).mp hT
  have he := congrArg Finset.card (badClique_neighbours H hΔ hT hx)
  rw [hc x hx] at he
  have hh := Finset.card_erase_add_one hx
  rw [degreeIn_eq_card,hc x hx]
  omega

theorem badCliques_update_off (d : C → ℕ) (π : W → C) (x : W) (j : C)
    (T : Finset W) (hx : x ∉ T) :
    T ∈ badCliques H d π ↔ T ∈ badCliques H d (Function.update π x j) := by
  simp only [mem_badCliques]
  have hh (a : W) (ha : a ∈ T) : Function.update π x j a = π a :=
    Function.update_of_ne (show a ≠ x from fun he => hx (he ▸ ha)) _ _
  constructor <;> rintro ⟨c,hc,hcol,hcl⟩ <;> refine ⟨c,hc,?_,hcl⟩
  · intro a ha; rw [hh a ha]; exact hcol a ha
  · intro a ha; rw [← hh a ha]; exact hcol a ha

/-- The precise counting fact behind Lemma A; every new bad clique contains
the moved vertex, and at most one can contain it. -/
theorem badCliques_update_le {d : C → ℕ} {π : W → C} (x : W) (j : C)
    (hnew : ∀ v, degreeIn H (Function.update π x j) v ((Function.update π x j) v) ≤
      d ((Function.update π x j) v))
    {T : Finset W} (hT : T ∈ badCliques H d π) (hx : x ∈ T) :
    (badCliques H d (Function.update π x j)).card ≤ (badCliques H d π).card := by
  let A := badCliques H d (Function.update π x j)
  let B := badCliques H d π
  let f : A → B := fun S => if hs : x ∈ S.val then ⟨T,hT⟩
    else ⟨S.val,(badCliques_update_off H d π x j S.val hs).mpr S.prop⟩
  have hinj : Function.Injective f := by
    intro S U hsu
    have he := congrArg Subtype.val hsu
    apply Subtype.ext
    by_cases hs : x ∈ S.val <;> by_cases hu : x ∈ U.val
    · exact badClique_unique_at H hnew S.prop U.prop hs hu
    · simp only [f,dif_pos hs,dif_neg hu] at he
      exact False.elim (hu (he ▸ hx))
    · simp only [f,dif_neg hs,dif_pos hu] at he
      exact False.elim (hs (he.symm ▸ hx))
    · simpa only [f,dif_neg hs,dif_neg hu] using he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Lemma 4.10 for the clique-obstruction potential, in particular the
capacity vector (3,3,3,3,1,1,1,1,1,1,1,1) of Theorem 4.11. The capacity-two
odd-cycle potential is deliberately not conflated with this definition. -/
theorem weighted_clique_hub_monotone {d : C → ℕ} {π : W → C}
    (hπ : CliqueMinimumThree H R d π)
    (hbudget : ∀ x, (H.degree x : ℤ) < ∑ c, ((d c : ℤ)+1))
    {T : Finset W} (hT : T ∈ badCliques H d π) {x : W} (hx : x ∈ T)
    (j : C) (hj : degreeIn H π x j = d j) :
    degreeIn R π x (π x) ≤ degreeIn R π x j := by
  have hold := lovasz_degree_bound H hπ.1.1 hbudget
  have hown := badClique_own_degree H hold hT hx
  let σ := Function.update π x j
  have henergy : weightedEnergy H d σ = weightedEnergy H d π := by
    rw [weightedEnergy_update,hj,hown]
    omega
  have hσ : WeightedMinimum H d σ := by
    intro ρ
    rw [henergy]
    exact hπ.1.1 ρ
  have hc := badCliques_update_le H x j (lovasz_degree_bound H hσ hbudget) hT hx
  have hσtwo : CliqueMinimumTwo H d σ := ⟨hσ,fun ρ hρ => hc.trans (hπ.1.2 ρ hρ)⟩
  have hh := hπ.2 σ hσtwo
  rw [energy_update] at hh
  omega

end Se20Part.Partition
