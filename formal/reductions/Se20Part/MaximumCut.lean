import Se20Part.Partitions

noncomputable section
open scoped Classical BigOperators
namespace Se20Part.Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)

theorem energy_lt_of_removes_conflict (π σ : W → C)
    (h : ∀ u v, H.Adj u v → σ u = σ v → π u = π v)
    {y z : W} (hyz : H.Adj y z) (hπ : π y = π z) (hσ : σ y ≠ σ z) :
    energy H σ < energy H π := by
  have hp (u v : W) :
      (if H.Adj u v ∧ σ u = σ v then (1 : ℤ) else 0) ≤
      (if H.Adj u v ∧ π u = π v then (1 : ℤ) else 0) := by
    by_cases ha : H.Adj u v <;> by_cases hs : σ u = σ v
    · simp [ha, hs, h u v ha hs]
    · simp only [ha, hs, and_false, and_self, ite_false, true_and]
      split_ifs <;> omega
    · simp [ha]
    · simp [ha]
  apply Finset.sum_lt_sum (fun u _ => Finset.sum_le_sum (fun v _ => hp u v))
  refine ⟨y, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun v _ => hp y v)
  exact ⟨z, Finset.mem_univ _, by simp [hyz, hπ, hσ]⟩

def twoClassWithout (π : W → C) (p j : C) (y : W) : Set W :=
  {v | v ≠ y ∧ (π v = p ∨ π v = j)}

/-- Lemma 4.12, in the stronger general graph form. Equal palette sizes are
enough; no maximum-degree, strong-edge geometry, or Brooks hypothesis is used. -/
theorem monochromatic_edge_reaches_other_class {d : C → ℕ} {π : W → C}
    (hmin : WeightedMinimum H d π) {p j : C} (hpj : p ≠ j) (hd : d p = d j)
    {y z : W} (hy : π y = p) (hz : π z = p) (hyz : H.Adj y z) :
    ∃ w, ∃ hw : w ∈ twoClassWithout π p j y,
      π w = j ∧ H.Adj y w ∧
        (H.induce (twoClassWithout π p j y)).Reachable
          ⟨z, hyz.ne.symm, Or.inl hz⟩ ⟨w, hw⟩ := by
  let A := twoClassWithout π p j y
  let zA : A := ⟨z, hyz.ne.symm, Or.inl hz⟩
  let S : Set W := {v | ∃ hv : v ∈ A, (H.induce A).Reachable zA ⟨v,hv⟩}
  by_contra hn
  have hsA {v : W} (hv : v ∈ S) : v ∈ A := hv.choose
  have hzS : z ∈ S := ⟨zA.prop, SimpleGraph.Reachable.refl _⟩
  have hyS : y ∉ S := fun h => (hsA h).1 rfl
  have closed {u v : W} (hu : u ∈ S) (hv : v ∈ A) (huv : H.Adj u v) : v ∈ S := by
    obtain ⟨huA,huR⟩ := hu
    exact ⟨hv, huR.trans (show (H.induce A).Adj ⟨u,huA⟩ ⟨v,hv⟩ from huv).reachable⟩
  have at_y {v : W} (hv : v ∈ S) (hyv : H.Adj y v) : π v = p := by
    rcases (hsA hv).2 with hvp | hvj
    · exact hvp
    · obtain ⟨hvA,hvR⟩ := hv
      exact False.elim (hn ⟨v,hvA,hvj,hyv,hvR⟩)
  let σ : W → C := fun v => if v ∈ S then Equiv.swap p j (π v) else π v
  have boundary {u v : W} (hu : u ∈ S) (hv : v ∉ S) (huv : H.Adj u v) : σ u ≠ σ v := by
    intro heq
    have hup : π u = p ∨ π u = j := (hsA hu).2
    have hvp : π v = p ∨ π v = j := by
      rcases hup with hup | hup
      · right
        simpa [σ, hu, hv, hup] using heq.symm
      · left
        simpa [σ, hu, hv, hup] using heq.symm
    by_cases hvy : v = y
    · subst v
      have hup := at_y hu huv.symm
      have : j = p := by simpa [σ, hu, hyS, hup, hy] using heq
      exact hpj this.symm
    · exact hv (closed hu ⟨hvy,hvp⟩ huv)
  have hproper : ∀ u v, H.Adj u v → σ u = σ v → π u = π v := by
    intro u v huv heq
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact (Equiv.swap p j).injective (by simpa [σ,hu,hv] using heq)
    · exact False.elim (boundary hu hv huv heq)
    · exact False.elim (boundary hv hu huv.symm heq.symm)
    · simpa [σ,hu,hv] using heq
  have hσ : σ y ≠ σ z := by simpa [σ,hyS,hzS,hy,hz] using hpj
  have hless := energy_lt_of_removes_conflict H π σ hproper hyz (hy.trans hz.symm) hσ
  have hweights : ∀ v, d (σ v) = d (π v) := by
    intro v
    by_cases hv : v ∈ S
    · rcases (hsA hv).2 with hvp | hvj
      · simpa [σ,hv,hvp] using hd.symm
      · simpa [σ,hv,hvj] using hd
    · simp [σ,hv]
  have hsum : (∑ v, (d (σ v) : ℤ)) = ∑ v, (d (π v) : ℤ) := by
    simp_rw [hweights]
  have hm := hmin σ
  unfold weightedEnergy at hm
  rw [hsum] at hm
  omega

end Se20Part.Partition
