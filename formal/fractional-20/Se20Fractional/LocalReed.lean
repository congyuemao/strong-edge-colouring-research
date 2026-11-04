import Se20Fractional.Peeling

namespace Se20Fractional
set_option backward.isDefEq.respectTransparency false
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {U : Finset V}

/-- A feasible dual to the finite stable-set covering LP. -/
structure DualWeight (G : SimpleGraph V) (U : Finset V) where
  w : V → ℝ
  nonneg : ∀ v ∈ U, 0 ≤ w v
  feasible : ∀ S : Finset V, S ⊆ U → Stable G S → ∑ v ∈ S, w v ≤ 1

/-- Exactly primal and dual feasibility with equality of the two objectives.
No local-Reed or graph-degree bound is included in this hypothesis. -/
structure FractionalLPWitness (G : SimpleGraph V) (U : Finset V) where
  primal : Colouring G U
  dual : DualWeight G U
  objective_eq : primal.total = ∑ v ∈ U, dual.w v

/-- The finite LP strong-duality/attainment statement left as an explicit hypothesis. -/
structure FractionalDuality (G : SimpleGraph V) : Prop where
  exists_optimal : ∀ U : Finset V, Nonempty (FractionalLPWitness G U)

theorem sum_subset_indicator {S T : Finset V} (h : S ⊆ T) (f : V → ℝ) :
    ∑ v ∈ S, f v = ∑ v ∈ T, if v ∈ S then f v else 0 := by
  have hs := Finset.sum_subset (f := fun v => if v ∈ S then f v else 0) h
    (fun v _ hv => by simp [hv])
  simpa using hs

theorem Colouring.double_count (c : Colouring G U) (f : V → ℝ) :
    ∑ i, c.weight i * (∑ v ∈ c.sets i, f v) = ∑ v ∈ U, f v * c.mass v := by
  simp_rw [sum_subset_indicator (c.subset _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Colouring.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_comm]

theorem weak_duality (c : Colouring G U) (w : DualWeight G U) :
    ∑ v ∈ U, w.w v ≤ c.total := by
  calc
    _ ≤ ∑ v ∈ U, w.w v * c.mass v := Finset.sum_le_sum fun v hv =>
      le_mul_of_one_le_right (w.nonneg v hv) (c.cover v hv)
    _ = ∑ i, c.weight i * (∑ v ∈ c.sets i, w.w v) := (c.double_count w.w).symm
    _ ≤ c.total := Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_right (c.nonneg i) (w.feasible _ (c.subset i) (c.stable i))

theorem dual_weight_le_one (w : DualWeight G U) {v : V} (hv : v ∈ U) : w.w v ≤ 1 := by
  have hs : Stable G {v} := by
    intro a ha b hb
    have ha' : a = v := Finset.mem_singleton.mp ha
    have hb' : b = v := Finset.mem_singleton.mp hb
    subst a; subst b
    exact G.irrefl
  simpa using w.feasible {v} (Finset.singleton_subset_iff.mpr hv) hs

/-- The objective equality really characterizes the fractional chromatic optimum. -/
theorem FractionalLPWitness.is_optimal (opt : FractionalLPWitness G U) :
    IsFractionalChromaticOn G U opt.primal.total := by
  refine ⟨⟨opt.primal, le_rfl⟩, ?_⟩
  rintro r ⟨c, hc⟩
  rw [opt.objective_eq]
  exact (weak_duality c opt.dual).trans hc

theorem optimal_tight (c : Colouring G U) (w : DualWeight G U)
    (hexact : ∀ v ∈ U, c.mass v = 1) (heq : c.total = ∑ v ∈ U, w.w v) :
    ∀ i, 0 < c.weight i → ∑ v ∈ c.sets i, w.w v = 1 := by
  have hs : (∑ i, c.weight i * (1 - ∑ v ∈ c.sets i, w.w v)) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, c.double_count]
    have hx : (∑ v ∈ U, w.w v * c.mass v) = ∑ v ∈ U, w.w v :=
      Finset.sum_congr rfl (fun v hv => by rw [hexact v hv, mul_one])
    rw [hx, ← heq]
    exact sub_self _
  have hn (i : Fin c.n) : 0 ≤ c.weight i * (1 - ∑ v ∈ c.sets i, w.w v) :=
    mul_nonneg (c.nonneg i) (sub_nonneg.mpr (w.feasible _ (c.subset i) (c.stable i)))
  intro i hi
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs i (Finset.mem_univ i)
  have hz' := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hi)
  linarith

/-- Every positive maximum-dual vertex outside a tight stable set has a neighbour in it. -/
theorem tight_has_neighbor (w : DualWeight G U) {S : Finset V} (hSU : S ⊆ U)
    (hS : Stable G S) (ht : ∑ u ∈ S, w.w u = 1) {z : V}
    (hzU : z ∈ U) (hzS : z ∉ S) (hzpos : 0 < w.w z) :
    (neighbors G S z).Nonempty := by
  by_contra h
  have hzero : ∀ u ∈ S, ¬ G.Adj z u := by
    intro u hu hzu
    exact h ⟨u, (mem_neighbors _ _ _ _).mpr ⟨hu, hzu⟩⟩
  have hd := w.feasible (insert z S) (Finset.insert_subset hzU hSU) (stable_insert hS hzero)
  rw [Finset.sum_insert hzS, ht] at hd
  linarith

/-- Replacing a unique neighbour by z forces that neighbour to have at least z's weight. -/
theorem tight_unique_neighbor_weight (w : DualWeight G U) {S : Finset V}
    (hSU : S ⊆ U) (hS : Stable G S) (ht : ∑ u ∈ S, w.w u = 1)
    {z u : V} (hzU : z ∈ U) (hzS : z ∉ S)
    (hu : neighbors G S z = {u}) : w.w z ≤ w.w u := by
  have huS : u ∈ S := by
    have hmem : u ∈ neighbors G S z := by rw [hu]; simp
    exact ((mem_neighbors _ _ _ _).mp hmem).1
  have hstable : Stable G (insert z (S.erase u)) := by
    apply stable_insert (stable_subset hS (Finset.erase_subset _ _))
    intro a ha hza
    have hamem : a ∈ neighbors G S z := (mem_neighbors _ _ _ _).mpr
      ⟨Finset.mem_of_mem_erase ha, hza⟩
    rw [hu, Finset.mem_singleton] at hamem
    exact (Finset.mem_erase.mp ha).1 hamem
  have hsub : insert z (S.erase u) ⊆ U :=
    Finset.insert_subset hzU ((Finset.erase_subset _ _).trans hSU)
  have hd := w.feasible _ hsub hstable
  have hn : z ∉ S.erase u := fun h => hzS (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hn] at hd
  have he := Finset.sum_erase_add S w.w huS
  linarith

theorem unique_neighbor_erase {S : Finset V} {z u : V}
    (hu : neighbors G S z = {u}) : ∀ a ∈ S.erase u, ¬ G.Adj z a := by
  intro a ha hza
  have hamem : a ∈ neighbors G S z := (mem_neighbors _ _ _ _).mpr
    ⟨Finset.mem_of_mem_erase ha, hza⟩
  rw [hu, Finset.mem_singleton] at hamem
  exact (Finset.mem_erase.mp ha).1 hamem

theorem tight_unique_neighbors_adj (w : DualWeight G U) {S : Finset V}
    (hSU : S ⊆ U) (hS : Stable G S) (ht : ∑ u ∈ S, w.w u = 1)
    {a b u : V} (haU : a ∈ U) (hbU : b ∈ U) (haS : a ∉ S) (hbS : b ∉ S)
    (haN : neighbors G S a = {u}) (hbN : neighbors G S b = {u})
    (hwa : w.w a = w.w u) (hwb : w.w b = w.w u) (hpos : 0 < w.w u)
    (hab : a ≠ b) : G.Adj a b := by
  by_contra hnot
  have huS : u ∈ S := by
    have hu : u ∈ neighbors G S a := by rw [haN]; simp
    exact ((mem_neighbors _ _ _ _).mp hu).1
  have hstable : Stable G (insert a (insert b (S.erase u))) := by
    apply stable_insert (stable_insert (stable_subset hS (Finset.erase_subset _ _))
      (unique_neighbor_erase hbN))
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hnot
    · exact unique_neighbor_erase haN x hx
  have hsub : insert a (insert b (S.erase u)) ⊆ U := Finset.insert_subset haU
    (Finset.insert_subset hbU ((Finset.erase_subset _ _).trans hSU))
  have hbnot : b ∉ S.erase u := fun h => hbS (Finset.mem_of_mem_erase h)
  have hanot : a ∉ insert b (S.erase u) := by simp [hab, haS]
  have hd := w.feasible _ hsub hstable
  rw [Finset.sum_insert hanot, Finset.sum_insert hbnot, hwa, hwb] at hd
  have he := Finset.sum_erase_add S w.w huS
  linarith

noncomputable def uniqueClass (M S : Finset V) (u : V) : Finset V :=
  M.filter (fun z => z ∉ S ∧ neighbors G S z = {u})

theorem stable_set_local_count (w : DualWeight G U) (S : Finset V)
    (hSU : S ⊆ U) (hS : Stable G S) (ht : ∑ u ∈ S, w.w u = 1)
    (W : ℝ) (hW : 0 < W) (hmax : ∀ u ∈ U, w.w u ≤ W)
    (M : Finset V) (hM : ∀ z, z ∈ M ↔ z ∈ U ∧ w.w z = W)
    (ω : V → ℕ)
    (hω : ∀ u ∈ U, ∀ Q : Finset V, Q ⊆ U → u ∈ Q → Clique G Q → Q.card ≤ ω u) :
    (∑ z ∈ M, if z ∈ S then (0 : ℝ) else 2 - (degreeOn G S z : ℝ)) ≤
      ∑ u ∈ S ∩ M, ((ω u : ℝ) - 1) := by
  let A := uniqueClass (G := G) M S
  have hAS (u : V) (z : V) : z ∈ A u ↔ z ∈ M ∧ z ∉ S ∧ neighbors G S z = {u} := by
    simp [A, uniqueClass]
  have hcount (u : V) (hu : u ∈ S ∩ M) : ((A u).card : ℝ) ≤ (ω u : ℝ) - 1 := by
    obtain ⟨huS, huM⟩ := Finset.mem_inter.mp hu
    obtain ⟨huU, hwu⟩ := (hM u).mp huM
    have huA : u ∉ A u := by simp [hAS, huS]
    have hQsub : insert u (A u) ⊆ U := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact huU
      · exact ((hM z).mp ((hAS u z).mp hz).1).1
    have hQ : Clique G (insert u (A u)) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hae | haA
      · subst a
        have hbA : b ∈ A u := (Finset.mem_insert.mp hb).resolve_left hab.symm
        obtain ⟨_, _, hbN⟩ := (hAS u b).mp hbA
        have huN : u ∈ neighbors G S b := by rw [hbN]; simp
        exact ((mem_neighbors _ _ _ _).mp huN).2.symm
      · rcases Finset.mem_insert.mp hb with hbe | hbA
        · subst b
          obtain ⟨_, _, haN⟩ := (hAS u a).mp haA
          have huN : u ∈ neighbors G S a := by rw [haN]; simp
          exact ((mem_neighbors _ _ _ _).mp huN).2
        · obtain ⟨haM, haS, haN⟩ := (hAS u a).mp haA
          obtain ⟨hbM, hbS, hbN⟩ := (hAS u b).mp hbA
          obtain ⟨haU, hwa⟩ := (hM a).mp haM
          obtain ⟨hbU, hwb⟩ := (hM b).mp hbM
          exact tight_unique_neighbors_adj w hSU hS ht haU hbU haS hbS haN hbN
            (hwa.trans hwu.symm) (hwb.trans hwu.symm) (hwu ▸ hW) hab
    have hcard := hω u huU (insert u (A u)) hQsub (Finset.mem_insert_self _ _) hQ
    rw [Finset.card_insert_of_notMem huA] at hcard
    have hcard' : ((A u).card : ℝ) + 1 ≤ (ω u : ℝ) := by exact_mod_cast hcard
    linarith
  have hpoint (z : V) (hz : z ∈ M) :
      (if z ∈ S then (0 : ℝ) else 2 - (degreeOn G S z : ℝ)) ≤
        ∑ u ∈ S ∩ M, if z ∈ A u then (1 : ℝ) else 0 := by
    have hnonneg : 0 ≤ ∑ u ∈ S ∩ M, if z ∈ A u then (1 : ℝ) else 0 :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    by_cases hzS : z ∈ S
    · simpa [hzS] using hnonneg
    · simp only [hzS, ite_false]
      obtain ⟨hzU, hwz⟩ := (hM z).mp hz
      have hne := tight_has_neighbor w hSU hS ht hzU hzS (hwz ▸ hW)
      by_cases hone : (neighbors G S z).card = 1
      · obtain ⟨u, huN⟩ := Finset.card_eq_one.mp hone
        have huS : u ∈ S := by
          have hu : u ∈ neighbors G S z := by rw [huN]; simp
          exact ((mem_neighbors _ _ _ _).mp hu).1
        have hwu := tight_unique_neighbor_weight w hSU hS ht hzU hzS huN
        have huM : u ∈ M := (hM u).mpr ⟨hSU huS, by
          have hmu := hmax u (hSU huS)
          linarith⟩
        have huA : z ∈ A u := (hAS u z).mpr ⟨hz, hzS, huN⟩
        have hs := Finset.single_le_sum (f := fun u => if z ∈ A u then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_inter.mpr ⟨huS, huM⟩)
        calc
          _ = (1 : ℝ) := by norm_num [degreeOn, hone]
          _ ≤ _ := by simpa only [huA, ite_true] using hs
      · have hc : 2 ≤ (neighbors G S z).card := by
          have := Finset.card_pos.mpr hne
          omega
        have hc' : (2 : ℝ) ≤ (degreeOn G S z : ℝ) := by exact_mod_cast hc
        linarith
  calc
    _ ≤ ∑ z ∈ M, ∑ u ∈ S ∩ M, if z ∈ A u then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun z hz => hpoint z hz
    _ = ∑ u ∈ S ∩ M, ((A u).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      have hsub : A u ⊆ M := fun z hz => ((hAS u z).mp hz).1
      simpa using (sum_subset_indicator hsub (fun _ => (1 : ℝ))).symm
    _ ≤ _ := Finset.sum_le_sum fun u hu => hcount u hu

theorem degreeOn_as_sum (S : Finset V) (z : V) :
    (degreeOn G S z : ℝ) = ∑ u ∈ S, if G.Adj z u then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter _ _

theorem Colouring.expected_degree (c : Colouring G U)
    (hexact : ∀ v ∈ U, c.mass v = 1) (z : V) :
    ∑ i, c.weight i * (degreeOn G (c.sets i) z : ℝ) = (degreeOn G U z : ℝ) := by
  simp_rw [degreeOn_as_sum]
  rw [c.double_count]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hexact u hu, mul_one]

theorem stable_degree_zero {S : Finset V} (hS : Stable G S) {z : V} (hz : z ∈ S) :
    degreeOn G S z = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨huS, hzu⟩ := (mem_neighbors _ _ _ _).mp hu
  exact hS z hz u huS hzu

theorem Colouring.expected_local_term (c : Colouring G U)
    (hexact : ∀ v ∈ U, c.mass v = 1) (z : V) (hz : z ∈ U) :
    (∑ i, c.weight i * (if z ∈ c.sets i then 0 else 2 - (degreeOn G (c.sets i) z : ℝ))) =
      2 * (c.total - 1) - (degreeOn G U z : ℝ) := by
  have hi (i : Fin c.n) :
      c.weight i * (if z ∈ c.sets i then 0 else 2 - (degreeOn G (c.sets i) z : ℝ)) =
        2 * (c.weight i - (if z ∈ c.sets i then c.weight i else 0)) -
          c.weight i * (degreeOn G (c.sets i) z : ℝ) := by
    by_cases hzi : z ∈ c.sets i
    · simp [hzi, stable_degree_zero (c.stable i) hzi]
    · simp only [hzi, ite_false]; ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, c.expected_degree hexact]
  change 2 * (c.total - c.mass z) - _ = _
  rw [hexact z hz]

theorem Colouring.expected_restricted_sum (c : Colouring G U) (M : Finset V)
    (hMU : M ⊆ U) (hexact : ∀ v ∈ U, c.mass v = 1) (f : V → ℝ) :
    ∑ i, c.weight i * (∑ u ∈ c.sets i ∩ M, f u) = ∑ u ∈ M, f u := by
  have hi (i : Fin c.n) : (∑ u ∈ c.sets i ∩ M, f u) =
      ∑ u ∈ M, if u ∈ c.sets i then f u else 0 := by
    have h := sum_subset_indicator (Finset.inter_subset_right : c.sets i ∩ M ⊆ M) f
    convert h using 1
    apply Finset.sum_congr rfl
    intro u hu
    simp [hu]
  simp_rw [hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    _ = f u * c.mass u := by
      simp only [Colouring.mass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp [mul_comm]
    _ = f u := by rw [hexact u (hMU hu), mul_one]

/-- Lemma A as a colourability statement, conditional only on finite LP duality.
`ω u` may be any upper bound on the size of cliques containing u. -/
theorem local_fractional_reed (hLP : Nonempty (FractionalLPWitness G U))
    (k : ℝ) (hk : 0 ≤ k) (ω : V → ℕ)
    (hω : ∀ u ∈ U, ∀ Q : Finset V, Q ⊆ U → u ∈ Q → Clique G Q → Q.card ≤ ω u)
    (hlocal : ∀ u ∈ U, (degreeOn G U u : ℝ) + 1 + (ω u : ℝ) ≤ 2 * k) :
    FractionalColourableOn G U k := by
  obtain ⟨opt⟩ := hLP
  obtain ⟨c, hct, hexact⟩ := normalize_colouring opt.primal
  let w := opt.dual
  have heq : c.total = ∑ u ∈ U, w.w u := hct.trans opt.objective_eq
  by_contra hnot
  have hbig : k < c.total := lt_of_not_ge (fun h => hnot ⟨c, h⟩)
  have hpositive : 0 < ∑ u ∈ U, w.w u := by linarith
  have hU : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hpositive
  obtain ⟨z, hzU, hzmax⟩ := Finset.exists_max_image U w.w hU
  let W := w.w z
  have hW : 0 < W := by
    by_contra h
    have hh : ∑ u ∈ U, w.w u ≤ 0 := Finset.sum_nonpos (fun u hu => (hzmax u hu).trans (le_of_not_gt h))
    linarith
  let M := U.filter (fun u => w.w u = W)
  have hM (u : V) : u ∈ M ↔ u ∈ U ∧ w.w u = W := by simp [M]
  have hMU : M ⊆ U := Finset.filter_subset _ _
  have hMne : M.Nonempty := ⟨z, (hM z).mpr ⟨hzU, rfl⟩⟩
  have htight := optimal_tight c w hexact heq
  have hsum :
      (∑ i, c.weight i * (∑ z ∈ M, if z ∈ c.sets i then (0 : ℝ) else
        2 - (degreeOn G (c.sets i) z : ℝ))) ≤
      ∑ i, c.weight i * (∑ u ∈ c.sets i ∩ M, ((ω u : ℝ) - 1)) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hzero : c.weight i = 0
    · simp [hzero]
    · have hi : 0 < c.weight i := lt_of_le_of_ne (c.nonneg i) (Ne.symm hzero)
      exact mul_le_mul_of_nonneg_left
        (stable_set_local_count w (c.sets i) (c.subset i) (c.stable i) (htight i hi)
          W hW hzmax M hM ω hω) (c.nonneg i)
  have hleft :
      (∑ i, c.weight i * (∑ z ∈ M, if z ∈ c.sets i then (0 : ℝ) else
        2 - (degreeOn G (c.sets i) z : ℝ))) =
      ∑ z ∈ M, (2 * (c.total - 1) - (degreeOn G U z : ℝ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun z hz => c.expected_local_term hexact z (hMU hz))
  rw [hleft, c.expected_restricted_sum M hMU hexact] at hsum
  have hstrict : (∑ z ∈ M, ((ω z : ℝ) - 1)) <
      ∑ z ∈ M, (2 * (c.total - 1) - (degreeOn G U z : ℝ)) := by
    apply Finset.sum_lt_sum_of_nonempty hMne
    intro z hz
    have hl := hlocal z (hMU hz)
    linarith
  exact (not_lt_of_ge hsum) hstrict

#print axioms weak_duality
#print axioms stable_set_local_count
#print axioms local_fractional_reed

end Se20Fractional
