import Se20Insertion.ParametricCounting

noncomputable section
open scoped Classical
namespace Se20Insertion.Parametric.PartialColouring
variable {K : ℕ} {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- Proposition 11.49(3) for K colours. -/
theorem allGroupsFail_single_saturated (φ : PartialColouring K H F) {h f : W} {k : ℕ}
    {a : Fin K} (hk : 2 ≤ k) (hk' : k ≤ K) (hf : φ.AllGroupsFail h k)
    (hs : φ.Single h a f) : ∀ b, b ≠ a → ∃ x, φ.Neighbour f b x := by
  intro b hba
  obtain ⟨x,y,hx,hy,hc⟩ := φ.allGroupsFail_tangled hk hk' hf a b hba.symm
  have hxf := hs.2 x hx
  subst x
  obtain ⟨hfB,hyB,hr⟩ := hc
  have hne : (⟨f,hfB⟩ : φ.Bicoloured a b) ≠ ⟨y,hyB⟩ := by
    intro h
    have hfy := congrArg Subtype.val h
    exact hba (hy.2.2.symm.trans ((congrArg φ.colour hfy).symm.trans hs.1.2.2))
  obtain ⟨z,hz⟩ := hr.nonempty_neighborSet_left hne
  rcases z.2.2 with hza | hzb
  · exact False.elim (φ.proper hs.1.1 z.2.1 hz (hs.1.2.2.trans hza.symm))
  · exact ⟨z.val,z.2.1,hz,hzb⟩

/-- Division-free ratio formula. It is valid for all degrees, including d=0,
and uses no truncated subtraction of 2K-d. -/
theorem allGroupsFail_sum (φ : PartialColouring K H F) (h : W) {k : ℕ}
    (hk : 2 ≤ k) (hk' : k < K) (hf : φ.AllGroupsFail h k) :
    2 * K * Nat.choose (K-1) k ≤
      (domainNeighbours H (insert h F) h).card * Nat.choose (K-1) k +
        ∑ f ∈ domainNeighbours H (insert h F) h, φ.tangleCliqueCount k f := by
  let N := domainNeighbours H (insert h F) h
  have hNF : N ⊆ F := by
    change domainNeighbours H (insert h F) h ⊆ F
    rw [φ.hole_domainNeighbours]
    exact Finset.filter_subset _ _
  have hlocal : ∀ Y ∈ colourGroups (K := K) k,
      2 * (K - k) ≤ (N.filter (fun f => φ.colour f ∉ Y)).card +
        (N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card := by
    intro Y hY
    have hcard := mem_colourGroups.mp hY
    have hcore := (φ.colourSetCore_isCore h Y).2 h (hf Y hY)
    have ho : φ.outsideYNeighbours h Y h = N.filter (fun f => φ.colour f ∉ Y) := by
      ext f
      simp only [outsideYNeighbours, Finset.mem_sdiff, Finset.mem_filter, yNeighbours]
      constructor
      · rintro ⟨hfN, hn⟩
        exact ⟨hfN, fun hc => hn ⟨hNF hfN, (Finset.mem_filter.mp hfN).2, hc⟩⟩
      · rintro ⟨hfN, hc⟩
        exact ⟨hfN, fun hm => hc hm.2.2⟩
    have hsub : domainNeighbours H (φ.colourSetCore h Y) h ⊆
        N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f) := by
      intro f hf'
      obtain ⟨hfC, hhf⟩ := Finset.mem_filter.mp hf'
      obtain ⟨hfD, hfY, ht⟩ := Finset.mem_filter.mp ((φ.colourSetCore_isCore h Y).1 hfC)
      have hfN : f ∈ N := Finset.mem_filter.mpr ⟨hfD, hhf⟩
      exact Finset.mem_filter.mpr ⟨hfN, hfY (hNF hfN), ht⟩
    have hle := Finset.card_le_card hsub
    rw [φ.threshold_eq_outside, ho, hcard] at hcore
    omega
  have hsum := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, φ.sum_groups_avoiding] at hsum
  have hswap := sum_filter_card_swap (colourGroups (K := K) k) N
    (fun Y f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)
  change (∑ Y ∈ colourGroups (K := K) k, (N.filter (fun f => φ.colour f ∉ Y ∧ φ.AllTangled Y f)).card) =
    ∑ f ∈ N, φ.tangleCliqueCount k f at hswap
  rw [hswap] at hsum
  have hK : K - 1 + 1 = K := by omega
  have hchoose : Nat.choose K k * (K - k) = Nat.choose (K-1) k * K := by
    have hh := (Nat.choose_mul_succ_eq (K-1) k).symm
    simpa only [hK] using hh
  simp only [Finset.sum_const, smul_eq_mul, card_colourGroups] at hsum
  change 2 * K * Nat.choose (K-1) k ≤ N.card * Nat.choose (K-1) k + _
  nlinarith

/-- Section 11.27: the average proportion is at least (2K-d)/d. -/
theorem allGroupsFail_ratio (φ : PartialColouring K H F) (h : W) {k d : ℕ}
    (hk : 2 ≤ k) (hk' : k < K) (hf : φ.AllGroupsFail h k)
    (hd : (domainNeighbours H (insert h F) h).card = d) (hdpos : 0 < d) :
    (2 * (K : ℚ) - d) / d ≤
      (∑ f ∈ domainNeighbours H (insert h F) h, (φ.tangleCliqueCount k f : ℚ)) /
        (d * (Nat.choose (K-1) k : ℚ)) := by
  have hsum := φ.allGroupsFail_sum h hk hk' hf
  rw [hd] at hsum
  have hq : 2 * (K : ℚ) * Nat.choose (K-1) k ≤
      d * (Nat.choose (K-1) k : ℚ) +
        ∑ f ∈ domainNeighbours H (insert h F) h, (φ.tangleCliqueCount k f : ℚ) := by
    exact_mod_cast hsum
  have hb : 0 < (Nat.choose (K-1) k : ℚ) := by
    exact_mod_cast (Nat.choose_pos (show k ≤ K-1 by omega))
  have hdq : 0 < (d : ℚ) := by exact_mod_cast hdpos
  apply (div_le_div_iff₀ hdq (mul_pos hdq hb)).mpr
  have := mul_le_mul_of_nonneg_left hq hdq.le
  nlinarith

end Se20Insertion.Parametric.PartialColouring

namespace Se20Insertion.Parametric
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def ofTwenty (φ : Se20Insertion.PartialColouring H F) : PartialColouring 20 H F :=
  ⟨φ.colour,φ.proper⟩

def toTwenty (φ : PartialColouring 20 H F) : Se20Insertion.PartialColouring H F :=
  ⟨φ.colour,φ.proper⟩

theorem ofTwenty_core (φ : Se20Insertion.PartialColouring H F) (h : W) (Y : Finset Colour) :
    (ofTwenty φ).colourSetCore h Y = φ.colourSetCore h Y := rfl

/-- K=20 recovers the existing core insertion theorem through the new proof. -/
theorem core_insertion_twenty (φ : Se20Insertion.PartialColouring H F) (h : W) (hh : h ∉ F)
    (Y : Finset Colour) (hY : 2 ≤ Y.card) (hc : h ∉ φ.colourSetCore h Y) :
    Nonempty (Se20Insertion.PartialColouring H (insert h F)) := by
  obtain ⟨ψ⟩ := (ofTwenty φ).colourSetInsertion h hh Y hY (by rwa [ofTwenty_core])
  exact ⟨toTwenty ψ⟩

/-- K=20,d=24 recovers the earlier 2/3 counting statement. -/
theorem clique_sum_twenty (φ : Se20Insertion.PartialColouring H F) (h : W) {k : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 19) (hf : φ.AllGroupsFail h k)
    (hd : (Se20Insertion.PartialColouring.domainNeighbours H (insert h F) h).card = 24) :
    3 * (∑ f ∈ Se20Insertion.PartialColouring.domainNeighbours H (insert h F) h,
      φ.tangleCliqueCount k f) ≥ 2 * 24 * Nat.choose 19 k := by
  have hsum := (ofTwenty φ).allGroupsFail_sum h hk (by omega) hf
  change 2 * 20 * Nat.choose 19 k ≤
    (Se20Insertion.PartialColouring.domainNeighbours H (insert h F) h).card * Nat.choose 19 k +
      (∑ f ∈ Se20Insertion.PartialColouring.domainNeighbours H (insert h F) h, φ.tangleCliqueCount k f) at hsum
  rw [hd] at hsum
  omega

end Se20Insertion.Parametric
