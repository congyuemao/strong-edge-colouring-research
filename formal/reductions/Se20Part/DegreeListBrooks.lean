import Se20Part.DegreeListInduced

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part.DegreeList
variable {W C : Type*} [Fintype W] [DecidableEq W] [Nonempty C] (H : SimpleGraph W)

/-- Connectivity and non-completeness suffice for an induced three-vertex path.
No assertion about deleting its ends is included here. -/
theorem exists_induced_three_path (hconn : H.Connected)
    (hn : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) :
    ∃ u v r, u ≠ v ∧ ¬ H.Adj u v ∧ H.Adj r u ∧ H.Adj r v := by
  by_contra hno
  have ht {x y z : W} (hxy : H.Adj x y) (hyz : H.Adj y z) (hxz : x ≠ z) : H.Adj x z := by
    by_contra hn'
    exact hno ⟨x,z,y,hxz,hn',hxy.symm,hyz⟩
  have go : ∀ {x y : W}, H.Walk x y → x = y ∨ H.Adj x y := by
    intro x y p
    induction p with
    | nil => exact Or.inl rfl
    | @cons x y z hxy p ih =>
      rcases ih with rfl | hyz
      · exact Or.inr hxy
      · by_cases hxz : x = z
        · exact Or.inl hxz
        · exact Or.inr (ht hxy hyz hxz)
  obtain ⟨x,y,hxy,hnxy⟩ := hn
  obtain ⟨p⟩ := hconn x y
  exact (go p).elim hxy hnxy

/-- In the no-cut case, a bad assignment also obstructs ordinary colouring
with the common list size. This includes the even-cycle case whenever an
ordinary two-colouring of that cycle is supplied. -/
theorem bad_noncut_not_degree_colourable (L : W → Finset C) (hconn : H.Connected)
    (hdelete : ∀ v, (H.induce {x | x ≠ v}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) (hbad : ¬ ColourableOn H L Finset.univ)
    (r : W) : ¬ H.Colorable (H.degree r) := by
  have hu := bad_noncut_uniform H L hconn hdelete hd hbad r
  have hcard : (L r).card = H.degree r := bad_degree_lists_tight H L hconn hd hbad r
  let e : ↥(L r) ≃ Fin (H.degree r) := Finset.equivFinOfCardEq hcard
  rintro ⟨c⟩
  apply hbad
  refine ⟨fun x => (e.symm (c x)).val,?_,?_⟩
  · intro x _
    rw [(hu x).1]
    exact (e.symm (c x)).prop
  · intro x _ y _ hxy heq
    exact c.valid hxy (e.symm.injective (Subtype.ext heq))

/-- The three-connected branch of the non-separating-pair proof. Pair
deletion is an explicit connectivity premise here, not inferred from
two-connectivity. -/
theorem colourable_of_pair_deletions (L : W → Finset C) (hconn : H.Connected)
    (hdelete : ∀ v, (H.induce {x | x ≠ v}).Connected)
    (hpairs : ∀ u v, u ≠ v → (H.induce {x | x ∉ ({u,v} : Finset W)}).Connected)
    (hn : ∃ x y, x ≠ y ∧ ¬ H.Adj x y)
    (hd : ∀ x, H.degree x ≤ (L x).card) : ColourableOn H L Finset.univ := by
  by_contra hbad
  obtain ⟨u,v,r,huv,hnuv,hru,hrv⟩ := exists_induced_three_path H hconn hn
  have heq := (bad_noncut_uniform H L hconn hdelete hd hbad u v).1
  have hpos : 0 < (L u).card :=
    (H.degree_pos_iff_nonempty.mpr ⟨r,hru.symm⟩).trans_le (hd u)
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
  exact hbad (colourable_of_nonseparating_pair H L huv hnuv hru hrv (hpairs u v huv) hd ha
    (heq.symm ▸ ha))

end Se20Part.DegreeList
