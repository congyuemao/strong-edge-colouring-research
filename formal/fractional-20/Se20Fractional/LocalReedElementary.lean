import Se20Fractional.Peeling

/-! An elementary proof of local fractional Reed by maximum stable sets and
finite induction on the support of a nonnegative demand. No LP duality. -/
namespace Se20Fractional
namespace Elementary
open Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def MaximumStable (G : SimpleGraph V) (U S : Finset V) : Prop :=
  S ⊆ U ∧ Stable G S ∧ ∀ T : Finset V, T ⊆ U → Stable G T → T.card ≤ S.card

noncomputable def maximumStableSets (G : SimpleGraph V) (U : Finset V) : Finset (Finset V) :=
  U.powerset.filter (MaximumStable G U)

@[simp] theorem mem_maximumStableSets (U S : Finset V) :
    S ∈ maximumStableSets G U ↔ MaximumStable G U S := by
  simp only [maximumStableSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

theorem maximumStableSets_nonempty (U : Finset V) : (maximumStableSets G U).Nonempty := by
  let A := U.powerset.filter (Stable G)
  have hA : A.Nonempty := ⟨∅, by simp [A, Stable]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hSm : S ⊆ U ∧ Stable G S := by simpa [A] using hS
  refine ⟨S, (mem_maximumStableSets U S).mpr ⟨hSm.1, hSm.2, ?_⟩⟩
  intro T hTU hT
  exact hmax T (by simp [A, hTU, hT])

theorem maximum_nonempty {U S : Finset V} (hU : U.Nonempty) (hS : MaximumStable G U S) :
    S.Nonempty := by
  obtain ⟨v, hv⟩ := hU
  have hs : Stable G {v} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; exact G.irrefl
  have h := hS.2.2 {v} (Finset.singleton_subset_iff.mpr hv) hs
  simp only [Finset.card_singleton] at h
  exact Finset.card_pos.mp h

theorem maximum_has_neighbor {U S : Finset V} (hS : MaximumStable G U S)
    {v : V} (hvU : v ∈ U) (hvS : v ∉ S) : (neighbors G S v).Nonempty := by
  by_contra h
  have hstable : Stable G (insert v S) := by
    apply stable_insert hS.2.1
    intro w hw hvw
    exact h ⟨w, (mem_neighbors _ _ _ _).mpr ⟨hw, hvw⟩⟩
  have hc := hS.2.2 (insert v S) (Finset.insert_subset hvU hS.1) hstable
  rw [Finset.card_insert_of_notMem hvS] at hc
  omega

theorem unique_erase_noadj {S : Finset V} {v u : V}
    (hu : neighbors G S v = {u}) : ∀ a ∈ S.erase u, ¬ G.Adj v a := by
  intro a ha hva
  have hn : a ∈ neighbors G S v := (mem_neighbors _ _ _ _).mpr
    ⟨Finset.mem_of_mem_erase ha, hva⟩
  rw [hu, Finset.mem_singleton] at hn
  exact (Finset.mem_erase.mp ha).1 hn

theorem maximum_swap {U S : Finset V} (hS : MaximumStable G U S)
    {v u : V} (hvU : v ∈ U) (hvS : v ∉ S) (hu : neighbors G S v = {u}) :
    MaximumStable G U (insert v (S.erase u)) ∧ insert u ((insert v (S.erase u)).erase v) = S := by
  have huS : u ∈ S := by
    have hn : u ∈ neighbors G S v := by rw [hu]; simp
    exact ((mem_neighbors _ _ _ _).mp hn).1
  have hvE : v ∉ S.erase u := fun h => hvS (Finset.mem_of_mem_erase h)
  have hc : (insert v (S.erase u)).card = S.card := by
    rw [Finset.card_insert_of_notMem hvE]
    exact Finset.card_erase_add_one huS
  refine ⟨⟨Finset.insert_subset hvU ((Finset.erase_subset _ _).trans hS.1),
    stable_insert (stable_subset hS.2.1 (Finset.erase_subset _ _)) (unique_erase_noadj hu), ?_⟩, ?_⟩
  · intro T hTU hT
    rw [hc]
    exact hS.2.2 T hTU hT
  · rw [Finset.erase_insert hvE, Finset.insert_erase huS]

noncomputable def replacements (G : SimpleGraph V) (U T : Finset V) (v : V) : Finset V :=
  U.filter (fun u => G.Adj v u ∧ u ∉ T ∧ Stable G (insert u (T.erase v)))

theorem replacements_clique {U T : Finset V} (hT : MaximumStable G U T)
    {v : V} (hv : v ∈ T) : Clique G (insert v (replacements G U T v)) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with hae | haR
  · subst a
    have hbR := (Finset.mem_insert.mp hb).resolve_left hab.symm
    exact (Finset.mem_filter.mp hbR).2.1
  · rcases Finset.mem_insert.mp hb with hbe | hbR
    · subst b
      exact (Finset.mem_filter.mp haR).2.1.symm
    · obtain ⟨haU, _, haT, haSt⟩ := Finset.mem_filter.mp haR
      obtain ⟨hbU, _, hbT, hbSt⟩ := Finset.mem_filter.mp hbR
      by_contra hnot
      have hstable : Stable G (insert a (insert b (T.erase v))) := by
        apply stable_insert hbSt
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hnot
        · exact haSt a (Finset.mem_insert_self _ _) x (Finset.mem_insert_of_mem hx)
      have hsub : insert a (insert b (T.erase v)) ⊆ U := Finset.insert_subset haU
        (Finset.insert_subset hbU ((Finset.erase_subset _ _).trans hT.1))
      have hcard := hT.2.2 _ hsub hstable
      have haE : a ∉ insert b (T.erase v) := by simp [hab, haT]
      have hbE : b ∉ T.erase v := fun h => hbT (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem haE, Finset.card_insert_of_notMem hbE] at hcard
      have he := Finset.card_erase_add_one hv
      omega

theorem replacements_card {U T : Finset V} (hT : MaximumStable G U T)
    {v : V} (hv : v ∈ T) (ω : ℕ)
    (hω : ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω) :
    (replacements G U T v).card + 1 ≤ ω := by
  have hsub : insert v (replacements G U T v) ⊆ U :=
    Finset.insert_subset (hT.1 hv) (Finset.filter_subset _ _)
  have hnot : v ∉ replacements G U T v := by simp [replacements, hv]
  have h := hω _ hsub (Finset.mem_insert_self _ _) (replacements_clique hT hv)
  simpa only [Finset.card_insert_of_notMem hnot] using h

noncomputable def occurrence (F : Finset (Finset V)) (v : V) : ℕ :=
  (F.filter (fun S => v ∈ S)).card

/-- The fibre bound for the swap map, with one added to both sides per target. -/
theorem unique_count_bound (U : Finset V) (v : V) (hvU : v ∈ U) (ω : ℕ)
    (hω : ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω) :
    ((maximumStableSets G U).filter (fun S => v ∉ S ∧ degreeOn G S v = 1)).card +
      occurrence (maximumStableSets G U) v ≤ ω * occurrence (maximumStableSets G U) v := by
  let F := maximumStableSets G U
  let A := F.filter (fun S => v ∉ S ∧ degreeOn G S v = 1)
  let B := F.filter (fun S => v ∈ S)
  have hex (S : Finset V) : ∃ u : V, S ∈ A → neighbors G S v = {u} := by
    by_cases hS : S ∈ A
    · have hone := (Finset.mem_filter.mp hS).2.2
      exact (Finset.card_eq_one.mp hone).imp (fun u hu => fun _ => hu)
    · exact ⟨v, fun h => False.elim (hS h)⟩
  choose u hu using hex
  let f (S : Finset V) := insert v (S.erase (u S))
  have hswap (S : Finset V) (hSA : S ∈ A) :
      MaximumStable G U (f S) ∧ insert (u S) ((f S).erase v) = S := by
    obtain ⟨hSF, hvS, _⟩ := Finset.mem_filter.mp hSA
    exact maximum_swap ((mem_maximumStableSets U S).mp hSF) hvU hvS (hu S hSA)
  have hfB (S : Finset V) (hSA : S ∈ A) : f S ∈ B := by
    exact Finset.mem_filter.mpr ⟨(mem_maximumStableSets U (f S)).mpr (hswap S hSA).1,
      Finset.mem_insert_self _ _⟩
  have huR (S : Finset V) (hSA : S ∈ A) : u S ∈ replacements G U (f S) v := by
    obtain ⟨hSF, hvS, _⟩ := Finset.mem_filter.mp hSA
    have hS := (mem_maximumStableSets U S).mp hSF
    have hun : u S ∈ neighbors G S v := by rw [hu S hSA]; simp
    obtain ⟨huS, hvu⟩ := (mem_neighbors _ _ _ _).mp hun
    refine Finset.mem_filter.mpr ⟨hS.1 huS, hvu, ?_, ?_⟩
    · simp [f, hvu.ne.symm]
    · rw [(hswap S hSA).2]
      exact hS.2.1
  have hfiber (T : Finset V) (hTB : T ∈ B) :
      (A.filter (fun S => f S = T)).card + 1 ≤ ω := by
    have hle : (A.filter (fun S => f S = T)).card ≤ (replacements G U T v).card := by
      apply Finset.card_le_card_of_injOn u
      · intro S hS
        obtain ⟨hSA, hST⟩ := Finset.mem_filter.mp hS
        change u S ∈ replacements G U T v
        simpa only [hST] using huR S hSA
      · intro S hS R hR heq
        obtain ⟨hSA, hST⟩ := Finset.mem_filter.mp hS
        obtain ⟨hRA, hRT⟩ := Finset.mem_filter.mp hR
        have hs := (hswap S hSA).2
        have hr := (hswap R hRA).2
        rw [hST, heq] at hs
        rw [hRT] at hr
        exact hs.symm.trans hr
    obtain ⟨hTF, hvT⟩ := Finset.mem_filter.mp hTB
    have hb := replacements_card ((mem_maximumStableSets U T).mp hTF) hvT ω hω
    omega
  have hsum := Finset.sum_le_sum (fun T hT => hfiber T hT)
  have hid : (∑ T ∈ B, (A.filter (fun S => f S = T)).card) = A.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hfB
  simp only [Finset.sum_add_distrib, hid, Finset.sum_const, Nat.nsmul_eq_mul] at hsum
  change A.card + B.card ≤ ω * B.card
  simpa only [mul_one, Nat.mul_comm] using hsum

/-- The maximum-stable-set inequality in the question, before division by |F|. -/
theorem maximum_stable_key (U : Finset V) (v : V) (hvU : v ∈ U) (ω : ℕ)
    (hω : ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω) :
    2 * (maximumStableSets G U).card ≤
      (∑ S ∈ maximumStableSets G U, degreeOn G S v) +
        (ω + 1) * occurrence (maximumStableSets G U) v := by
  let F := maximumStableSets G U
  let A := F.filter (fun S => v ∉ S ∧ degreeOn G S v = 1)
  have hpoint (S : Finset V) (hSF : S ∈ F) :
      2 ≤ degreeOn G S v + 2 * (if v ∈ S then 1 else 0) + (if S ∈ A then 1 else 0) := by
    by_cases hvS : v ∈ S
    · simp only [hvS, ite_true, mul_one]
      omega
    · have hn := maximum_has_neighbor ((mem_maximumStableSets U S).mp hSF) hvU hvS
      have hc : 0 < degreeOn G S v := Finset.card_pos.mpr hn
      by_cases hone : degreeOn G S v = 1
      · have hSA : S ∈ A := Finset.mem_filter.mpr ⟨hSF, hvS, hone⟩
        simp [hvS, hone, hSA]
      · simp only [hvS, ite_false, mul_zero, add_zero]
        omega
  have hs := Finset.sum_le_sum (fun S hS => hpoint S hS)
  have hfilt : F.filter (fun S => S ∈ A) = A :=
    Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Nat.nsmul_eq_mul, hfilt] at hs
  have hb := unique_count_bound U v hvU ω hω
  change A.card + occurrence F v ≤ ω * occurrence F v at hb
  change F.card * 2 ≤ (∑ S ∈ F, degreeOn G S v) +
    2 * occurrence F v + A.card at hs
  change 2 * F.card ≤ (∑ S ∈ F, degreeOn G S v) + (ω+1)*occurrence F v
  nlinarith

/-- Double-count appearances of neighbours among maximum stable sets. -/
theorem occurrence_neighbors (U : Finset V) (v : V) :
    (∑ u ∈ neighbors G U v, occurrence (maximumStableSets G U) u) =
      ∑ S ∈ maximumStableSets G U, degreeOn G S v := by
  simp only [occurrence, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hSF
  have hS := (mem_maximumStableSets U S).mp hSF
  rw [Finset.sum_boole]
  change ((neighbors G U v).filter (fun u => u ∈ S)).card = (neighbors G S v).card
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter, mem_neighbors]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hS.1 h.1, h.2⟩, h.1⟩⟩

theorem maximum_stable_key_real (U : Finset V) (v : V) (hvU : v ∈ U) (ω : ℕ)
    (hω : ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω) :
    2 * ((maximumStableSets G U).card : ℝ) ≤
      (∑ u ∈ neighbors G U v, (occurrence (maximumStableSets G U) u : ℝ)) +
        (ω + 1 : ℝ) * occurrence (maximumStableSets G U) v := by
  have h := maximum_stable_key U v hvU ω hω
  rw [← occurrence_neighbors] at h
  exact_mod_cast h

structure DemandColouring (G : SimpleGraph V) (U : Finset V) (r : V → ℝ) where
  weight : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ weight S
  support : ∀ S, weight S ≠ 0 → S ⊆ U ∧ Stable G S
  cover : ∀ v ∈ U, r v ≤ ∑ S, if v ∈ S then weight S else 0

noncomputable def DemandColouring.total {U : Finset V} {r : V → ℝ}
    (c : DemandColouring G U r) : ℝ := ∑ S, c.weight S

noncomputable def DemandColouring.mass {U : Finset V} {r : V → ℝ}
    (c : DemandColouring G U r) (v : V) : ℝ := ∑ S, if v ∈ S then c.weight S else 0

theorem DemandColouring.mass_nonneg {U : Finset V} {r : V → ℝ}
    (c : DemandColouring G U r) (v : V) : 0 ≤ c.mass v := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> simp [c.nonneg]

theorem zero_demand_colouring (U : Finset V) (r : V → ℝ)
    (hr : ∀ v ∈ U, r v ≤ 0) (k : ℝ) (hk : 0 ≤ k) :
    ∃ c : DemandColouring G U r, c.total ≤ k := by
  refine ⟨⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩, ?_⟩
  · intro S h; exact False.elim (h rfl)
  · intro v hv; simpa using hr v hv
  · simpa [DemandColouring.total] using hk

theorem lift_zero_demand {U T : Finset V} {r : V → ℝ} (c : DemandColouring G T r)
    (hTU : T ⊆ U) (hz : ∀ v ∈ U, v ∉ T → r v ≤ 0) :
    ∃ d : DemandColouring G U r, d.total = c.total := by
  refine ⟨⟨c.weight, c.nonneg, ?_, ?_⟩, rfl⟩
  · intro S hS
    exact ⟨(c.support S hS).1.trans hTU, (c.support S hS).2⟩
  · intro v hv
    by_cases hvT : v ∈ T
    · exact c.cover v hvT
    · exact (hz v hv hvT).trans (c.mass_nonneg v)

theorem neighbor_sum_mono {U T : Finset V} (hTU : T ⊆ U) (r : V → ℝ)
    (hr : ∀ v ∈ U, 0 ≤ r v) (v : V) :
    ∑ u ∈ neighbors G T v, r u ≤ ∑ u ∈ neighbors G U v, r u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨huT, hvu⟩ := (mem_neighbors _ _ _ _).mp hu
    exact (mem_neighbors _ _ _ _).mpr ⟨hTU huT, hvu⟩
  · intro u hu _
    exact hr u ((mem_neighbors _ _ _ _).mp hu).1

theorem uniform_total (F : Finset (Finset V)) (a : ℝ) :
    (∑ S : Finset V, if S ∈ F then a else 0) = a * F.card := by
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem uniform_mass (F : Finset (Finset V)) (a : ℝ) (v : V) :
    (∑ S : Finset V, if v ∈ S then (if S ∈ F then a else 0) else 0) =
      a * occurrence F v := by
  have h (S : Finset V) :
      (if v ∈ S then (if S ∈ F then a else 0) else 0) =
        if S ∈ F.filter (fun T => v ∈ T) then a else 0 := by
    by_cases hv : v ∈ S <;> by_cases hS : S ∈ F <;> simp [hv, hS]
  simp_rw [h]
  exact uniform_total _ _

theorem add_uniform {U T : Finset V} (hTU : T ⊆ U) (r r' : V → ℝ)
    (F : Finset (Finset V)) (hF : ∀ S ∈ F, S ⊆ U ∧ Stable G S)
    (a : ℝ) (ha : 0 ≤ a) (c : DemandColouring G T r')
    (hres : ∀ v ∈ U, r v ≤ a * occurrence F v + c.mass v) :
    ∃ d : DemandColouring G U r, d.total = a * F.card + c.total := by
  let x (S : Finset V) := (if S ∈ F then a else 0) + c.weight S
  have hm (v : V) : (∑ S, if v ∈ S then x S else 0) = a * occurrence F v + c.mass v := by
    have hi (S : Finset V) : (if v ∈ S then x S else 0) =
        (if v ∈ S then (if S ∈ F then a else 0) else 0) +
        (if v ∈ S then c.weight S else 0) := by
      by_cases h : v ∈ S <;> simp [h, x]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, uniform_mass]
    rfl
  refine ⟨⟨x, ?_, ?_, ?_⟩, ?_⟩
  · intro S
    apply add_nonneg _ (c.nonneg S)
    split_ifs <;> positivity
  · intro S hS
    by_cases hSF : S ∈ F
    · exact hF S hSF
    · have hc : c.weight S ≠ 0 := by simpa [x, hSF] using hS
      exact ⟨(c.support S hc).1.trans hTU, (c.support S hc).2⟩
  · intro v hv
    rw [hm]
    exact hres v hv
  · change (∑ S, ((if S ∈ F then a else 0) + c.weight S)) = _
    rw [Finset.sum_add_distrib, uniform_total]
    rfl

theorem DemandColouring.toColouring {U : Finset V} (c : DemandColouring G U (fun _ => 1)) :
    ∃ d : Colouring G U, d.total = c.total := by
  let e := (Fintype.equivFin (Finset V)).symm
  let ss (i : Fin (Fintype.card (Finset V))) := if c.weight (e i) = 0 then ∅ else e i
  have hm (v : V) : (∑ i, if v ∈ ss i then c.weight (e i) else 0) = c.mass v := by
    have hi (i : Fin (Fintype.card (Finset V))) :
        (if v ∈ ss i then c.weight (e i) else 0) = if v ∈ e i then c.weight (e i) else 0 := by
      by_cases h : c.weight (e i) = 0 <;> simp [ss, h]
    simp_rw [hi]
    exact e.sum_comp (fun S => if v ∈ S then c.weight S else 0)
  refine ⟨{
    n := Fintype.card (Finset V)
    sets := ss
    weight := fun i => c.weight (e i)
    nonneg := fun i => c.nonneg (e i)
    stable := ?_
    subset := ?_
    cover := ?_ }, ?_⟩
  · intro i
    dsimp [ss]
    split_ifs with h
    · simp [Stable]
    · exact (c.support (e i) h).2
  · intro i
    dsimp [ss]
    split_ifs with h
    · exact Finset.empty_subset _
    · exact (c.support (e i) h).1
  · intro v hv
    rw [hm]
    exact c.cover v hv
  · exact e.sum_comp c.weight

theorem occurrence_positive_exists {U : Finset V} (hU : U.Nonempty) :
    (U.filter (fun v => 0 < occurrence (maximumStableSets G U) v)).Nonempty := by
  obtain ⟨S, hSF⟩ := maximumStableSets_nonempty (G := G) U
  have hS := (mem_maximumStableSets U S).mp hSF
  obtain ⟨v, hvS⟩ := maximum_nonempty hU hS
  exact ⟨v, Finset.mem_filter.mpr ⟨hS.1 hvS, Finset.card_pos.mpr
    ⟨S, Finset.mem_filter.mpr ⟨hSF, hvS⟩⟩⟩⟩

/-- Reed's weighted process. Each recursive step either removes a zero-demand
vertex or gives equal weight to all maximum stable sets and exhausts a demand. -/
theorem weighted_local_reed (U : Finset V) :
    ∀ (r : V → ℝ) (k : ℝ) (ω : V → ℕ),
    (∀ v ∈ U, 0 ≤ r v) → 0 ≤ k →
    (∀ v ∈ U, ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω v) →
    (∀ v ∈ U, (∑ u ∈ neighbors G U v, r u) + ((ω v : ℝ) + 1) * r v ≤ 2*k) →
    ∃ c : DemandColouring G U r, c.total ≤ k := by
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro r k ω hr hk hω hlocal
    by_cases hU : U.Nonempty
    swap
    · apply zero_demand_colouring U r _ k hk
      intro v hv
      exact False.elim (hU ⟨v, hv⟩)
    by_cases hz : ∃ v ∈ U, r v = 0
    · obtain ⟨v, hvU, hrv⟩ := hz
      have hsub : U.erase v ⊆ U := Finset.erase_subset _ _
      have hloc : ∀ w ∈ U.erase v, (∑ u ∈ neighbors G (U.erase v) w, r u) +
          ((ω w : ℝ)+1)*r w ≤ 2*k := by
        intro w hw
        have hn := neighbor_sum_mono (G := G) hsub r hr w
        have hl := hlocal w (hsub hw)
        linarith
      obtain ⟨c, hc⟩ := ih (U.erase v) (Finset.erase_ssubset hvU) r k ω
        (fun w hw => hr w (hsub hw)) hk
        (fun w hw Q hQ hwQ hcl => hω w (hsub hw) Q (hQ.trans hsub) hwQ hcl) hloc
      obtain ⟨d, hd⟩ := lift_zero_demand c hsub (by
        intro w hw hwerase
        have heq : w = v := by
          by_contra hne
          exact hwerase (Finset.mem_erase.mpr ⟨hne, hw⟩)
        simp [heq, hrv])
      exact ⟨d, hd ▸ hc⟩
    have hrpos (v : V) (hv : v ∈ U) : 0 < r v := by
      have hn : r v ≠ 0 := fun h => hz ⟨v, hv, h⟩
      exact lt_of_le_of_ne (hr v hv) hn.symm
    let F := maximumStableSets G U
    let c (v : V) : ℕ := occurrence F v
    let P := U.filter (fun v => 0 < c v)
    have hP : P.Nonempty := occurrence_positive_exists hU
    obtain ⟨v₀, hv₀P, hmin⟩ := Finset.exists_min_image P (fun v => r v / (c v : ℝ)) hP
    obtain ⟨hv₀U, hv₀c⟩ := Finset.mem_filter.mp hv₀P
    have hv₀cr : (0 : ℝ) < c v₀ := by exact_mod_cast hv₀c
    let a : ℝ := r v₀ / (c v₀ : ℝ)
    have ha : 0 ≤ a := (div_pos (hrpos v₀ hv₀U) hv₀cr).le
    have haeq : a * (c v₀ : ℝ) = r v₀ := div_mul_cancel₀ _ (ne_of_gt hv₀cr)
    have hcover (v : V) (hv : v ∈ U) : a * (c v : ℝ) ≤ r v := by
      by_cases hc : c v = 0
      · simpa [hc] using hr v hv
      · have hcp : 0 < c v := Nat.pos_of_ne_zero hc
        have hcp' : (0 : ℝ) < c v := by exact_mod_cast hcp
        exact (le_div_iff₀ hcp').mp (hmin v (Finset.mem_filter.mpr ⟨hv, hcp⟩))
    let r' (v : V) : ℝ := r v - a * (c v : ℝ)
    have hr' (v : V) (hv : v ∈ U) : 0 ≤ r' v := sub_nonneg.mpr (hcover v hv)
    have hz₀ : r' v₀ = 0 := by dsimp [r']; rw [haeq]; ring
    let U' := U.filter (fun v => 0 < r' v)
    have hsub : U' ⊆ U := Finset.filter_subset _ _
    have hproper : U' ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
      intro heq
      have hv : v₀ ∈ U' := by rw [heq]; exact hv₀U
      have := (Finset.mem_filter.mp hv).2
      simpa [hz₀] using this
    have hkey (v : V) (hv : v ∈ U) :
        2 * (F.card : ℝ) ≤ (∑ u ∈ neighbors G U v, (c u : ℝ)) +
          ((ω v : ℝ)+1)*(c v : ℝ) := maximum_stable_key_real U v hv (ω v) (hω v hv)
    have hbudget : a * (F.card : ℝ) ≤ k := by
      have hdrop := mul_le_mul_of_nonneg_left (hkey v₀ hv₀U) ha
      have hsum : (∑ u ∈ neighbors G U v₀, a*(c u : ℝ)) ≤
          ∑ u ∈ neighbors G U v₀, r u :=
        Finset.sum_le_sum (fun u hu => hcover u ((mem_neighbors _ _ _ _).mp hu).1)
      have hv := mul_le_mul_of_nonneg_left (hcover v₀ hv₀U)
        (show (0 : ℝ) ≤ (ω v₀ : ℝ)+1 by positivity)
      rw [← Finset.mul_sum] at hsum
      have hl := hlocal v₀ hv₀U
      nlinarith
    have hk' : 0 ≤ k - a*(F.card : ℝ) := sub_nonneg.mpr hbudget
    have hloc' : ∀ v ∈ U', (∑ u ∈ neighbors G U' v, r' u) +
        ((ω v : ℝ)+1)*r' v ≤ 2*(k - a*(F.card : ℝ)) := by
      intro v hv
      have hN := neighbor_sum_mono (G := G) hsub r' hr' v
      have he : (∑ u ∈ neighbors G U v, r' u) + ((ω v : ℝ)+1)*r' v =
          (∑ u ∈ neighbors G U v, r u) + ((ω v : ℝ)+1)*r v -
            a*((∑ u ∈ neighbors G U v, (c u : ℝ)) + ((ω v : ℝ)+1)*(c v : ℝ)) := by
        simp only [r', Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      have hdrop := mul_le_mul_of_nonneg_left (hkey v (hsub hv)) ha
      have hl := hlocal v (hsub hv)
      linarith
    obtain ⟨d, hd⟩ := ih U' hproper r' (k-a*(F.card : ℝ)) ω
      (fun v hv => hr' v (hsub hv)) hk'
      (fun v hv Q hQ hvQ hcl => hω v (hsub hv) Q (hQ.trans hsub) hvQ hcl) hloc'
    have hres (v : V) (hv : v ∈ U) : r v ≤ a * occurrence F v + d.mass v := by
      have hrem : r' v ≤ d.mass v := by
        by_cases hv' : v ∈ U'
        · exact d.cover v hv'
        · have hz' : r' v ≤ 0 := le_of_not_gt (fun hp => hv'
            (Finset.mem_filter.mpr ⟨hv, hp⟩))
          exact hz'.trans (d.mass_nonneg v)
      change r v - a * (occurrence F v : ℝ) ≤ d.mass v at hrem
      linarith
    obtain ⟨e, he⟩ := add_uniform hsub r r' F (fun S hS =>
      let h := (mem_maximumStableSets U S).mp hS
      ⟨h.1, h.2.1⟩) a ha d hres
    refine ⟨e, ?_⟩
    rw [he]
    linarith

#print axioms maximum_stable_key
#print axioms weighted_local_reed

end Elementary

/-- Lemma A, elementary and without any LP hypothesis. -/
theorem local_fractional_reed_elementary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (k : ℝ) (hk : 0 ≤ k) (ω : V → ℕ)
    (hω : ∀ v ∈ U, ∀ Q : Finset V, Q ⊆ U → v ∈ Q → Clique G Q → Q.card ≤ ω v)
    (hlocal : ∀ v ∈ U, (degreeOn G U v : ℝ) + 1 + (ω v : ℝ) ≤ 2*k) :
    FractionalColourableOn G U k := by
  obtain ⟨c, hc⟩ := Elementary.weighted_local_reed (G := G) U (fun _ => 1) k ω
    (by intros; norm_num) hk hω (by
      intro v hv
      simpa [degreeOn, add_comm, add_left_comm, add_assoc] using hlocal v hv)
  obtain ⟨d, hd⟩ := c.toColouring
  exact ⟨d, hd ▸ hc⟩

#print axioms local_fractional_reed_elementary
end Se20Fractional
