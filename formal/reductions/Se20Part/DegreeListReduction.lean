import Se20Part.DegreeListTools

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part.DegreeList
variable {W C : Type*} [Fintype W] [DecidableEq W] [Nonempty C]
  (H : SimpleGraph W)

theorem degree_delete (v : W) (x : {x // x ≠ v}) :
    (H.induce {x | x ≠ v}).degree x + (if H.Adj x.val v then 1 else 0) = H.degree x.val := by
  have hc : (H.induce {x | x ≠ v}).degree x = ((H.neighborFinset x.val).erase v).card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Fintype.card_coe ((H.neighborFinset x.val).erase v)]
    apply Fintype.card_congr
      { toFun := fun y => ⟨y.val.val,Finset.mem_erase.mpr
          ⟨y.val.prop,(H.mem_neighborFinset _ _).mpr y.prop⟩⟩
        invFun := fun y => ⟨⟨y.val,(Finset.mem_erase.mp y.prop).1⟩,
          (H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp y.prop).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hc]
  by_cases hxv : H.Adj x.val v
  · have hh := Finset.card_erase_add_one ((H.mem_neighborFinset _ _).mpr hxv)
    simpa [hxv] using hh
  · simp [hxv]

/-- Precolour one endpoint with a colour missing from its neighbour's list.
If deleting that endpoint leaves a connected graph, the remaining lists have slack. -/
theorem colourable_of_list_difference (L : W → Finset C) {v w : W}
    (hvw : H.Adj v w) (hconn : (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) {a : C} (hav : a ∈ L v) (haw : a ∉ L w) :
    ColourableOn H L Finset.univ := by
  let J := H.induce {x | x ≠ v}
  let L' : {x // x ≠ v} → Finset C := fun x => if H.Adj x.val v then (L x.val).erase a else L x.val
  have hdeg (x : {x // x ≠ v}) : J.degree x ≤ (L' x).card := by
    have hx := degree_delete H v x
    have hl := hd x.val
    by_cases ha : H.Adj x.val v
    · simp only [L',ha,ite_true] at *
      have hle : (L x.val).card ≤ ((L x.val).erase a).card + 1 := by
        by_cases hm : a ∈ L x.val
        · exact (Finset.card_erase_add_one hm).ge
        · simp [Finset.erase_eq_of_notMem hm]
      change (H.induce {x | x ≠ v}).degree x ≤ _
      omega
    · simpa [L',ha,J] using hx.le.trans hl
  let w' : {x // x ≠ v} := ⟨w,hvw.ne.symm⟩
  have hslack : J.degree w' < (L' w').card := by
    have hwd : J.degree w' + 1 = H.degree w := by
      have hh := degree_delete H v w'
      change J.degree w' + (if H.Adj w v then 1 else 0) = H.degree w at hh
      rwa [if_pos hvw.symm] at hh
    have hl := hd w
    have heq : L' w' = L w := by simp [L',w',hvw.symm,haw]
    rw [heq]
    omega
  obtain ⟨c,hc,hproper⟩ := colourable_of_one_slack J L' hconn hdeg w' hslack
  have hcL (x : {x // x ≠ v}) : c x ∈ L x.val := by
    have hh := hc x (Finset.mem_univ _)
    dsimp [L'] at hh
    split_ifs at hh
    · exact Finset.mem_of_mem_erase hh
    · exact hh
  have hca (x : {x // x ≠ v}) (hx : H.Adj x.val v) : c x ≠ a := by
    have hh := hc x (Finset.mem_univ _)
    simpa [L',hx] using (Finset.mem_erase.mp (show c x ∈ (L x.val).erase a from by simpa [L',hx] using hh)).1
  refine ⟨fun x => if hx : x = v then a else c ⟨x,hx⟩,?_,?_⟩
  · intro x _
    dsimp only
    split_ifs with hx
    · simpa [hx] using hav
    · exact hcL ⟨x,hx⟩
  · intro x _ y _ hxy heq
    by_cases hx : x = v <;> by_cases hy : y = v
    · subst x; subst y; exact hxy.ne rfl
    · subst x; exact hca ⟨y,hy⟩ hxy.symm (by simpa [hy] using heq.symm)
    · subst y; exact hca ⟨x,hx⟩ hxy (by simpa [hx] using heq)
    · exact hproper ⟨x,hx⟩ (Finset.mem_univ _) ⟨y,hy⟩ (Finset.mem_univ _) hxy
        (by simpa [hx,hy] using heq)

/-- In a bad degree-list assignment, a non-cut vertex's list is contained in
each neighbour's list. This is the list-specific step of the Gallai argument. -/
theorem bad_lists_subset_at_noncut (L : W → Finset C) {v w : W}
    (hvw : H.Adj v w) (hconn : (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ) :
    L v ⊆ L w := by
  intro a ha
  by_contra hn
  exact hbad (colourable_of_list_difference H L hvw hconn hd ha hn)

/-- No cut vertices forces equality of the lists along every edge. -/
theorem bad_lists_equal_on_edges (L : W → Finset C)
    (hdelete : ∀ v, (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ)
    {v w : W} (hvw : H.Adj v w) : L v = L w :=
  Finset.Subset.antisymm (bad_lists_subset_at_noncut H L hvw (hdelete v) hd hbad)
    (bad_lists_subset_at_noncut H L hvw.symm (hdelete w) hd hbad)

/-- The two-connected bad-list problem reduces to a uniform regular graph.
This does not assert the missing Brooks/non-separating-pair classification. -/
theorem bad_noncut_uniform (L : W → Finset C) (hconn : H.Connected)
    (hdelete : ∀ v, (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ)
    (r : W) : ∀ x, L x = L r ∧ H.degree x = (L r).card := by
  have go : ∀ {a b : W}, H.Walk a b → L a = L b := by
    intro a b p
    induction p with
    | nil => rfl
    | @cons a b c hab p ih =>
      exact (bad_lists_equal_on_edges H L hdelete hd hbad hab).trans ih
  intro x
  obtain ⟨p⟩ := hconn x r
  have hx := go p
  exact ⟨hx,(bad_degree_lists_tight H L hconn hd hbad x).symm.trans (congrArg Finset.card hx)⟩

end Se20Part.DegreeList
