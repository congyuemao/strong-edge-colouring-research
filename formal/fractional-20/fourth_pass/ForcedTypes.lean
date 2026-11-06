import fourth_pass.ProfileEnumeration

namespace Se20Fractional.FourthPass.Packed

def forcedType (d lower : Nat) : Nat :=
  (((List.range (2^d)).filter (fun t => lower ≤ t)).foldr Nat.land (mask d))

theorem bandFold_subset (ts : List Nat) (z t : Nat) (ht : t ∈ ts) :
    BitSubset (ts.foldr Nat.land z) t := by
  induction ts with
  | nil => simp at ht
  | cons a ts ih =>
    intro i hi
    change (a &&& ts.foldr Nat.land z).testBit i = true at hi
    simp only [Nat.testBit_and,Bool.and_eq_true] at hi
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hi.1
    · exact ih ht i hi.2

theorem forcedType_subset (d lower t : Nat) (hl : lower ≤ t) (ht : t < 2^d) :
    BitSubset (forcedType d lower) t := by
  apply bandFold_subset
  simp only [List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨ht,hl⟩

theorem typeEdges_mono (d : Nat) (as bs : List Nat)
    (hlen : as.length = bs.length)
    (hsub : ∀ i, i < as.length → BitSubset (as[i]?.getD 0) (bs[i]?.getD 0)) :
    ∀ e ∈ typeEdges d as, e ∈ typeEdges d bs := by
  rintro ⟨a,b⟩ he
  obtain ⟨i,hi,hb,ha,hd,ht⟩ := (mem_typeEdges d as a b).mp he
  exact (mem_typeEdges d bs a b).mpr ⟨i,by omega,hb,ha,hd,hsub i hi (a-1) ht⟩

theorem forced_edges (d m : Nat) (pre ts : List Nat) (lower remaining : Nat)
    (hlen : ts.length = remaining) (hb : ∀ t ∈ ts, lower ≤ t ∧ t < 2^d) :
    ∀ e ∈ profileEdges d m (pre ++ List.replicate remaining (forcedType d lower)),
      e ∈ profileEdges d m (pre ++ ts) := by
  intro e he
  simp only [profileEdges,List.mem_append] at he ⊢
  rcases he with he | he
  · exact Or.inl he
  · right
    apply typeEdges_mono d _ _ (by simp [hlen]) ?_ e he
    intro i hi
    by_cases hip : i < pre.length
    · simp only [List.getElem?_append_left hip]
      exact .refl _
    · have hij : i-pre.length < ts.length := by
        simp only [List.length_append,List.length_replicate] at hi
        omega
      have ht := hb ts[i-pre.length] (List.getElem_mem hij)
      have ht' := forcedType_subset d lower _ ht.1 ht.2
      simpa only [List.getElem?_append_right (by omega : pre.length ≤ i),
        List.getElem?_replicate,show i-pre.length < remaining from by omega,
        decide_true,↓reduceIte,List.getElem?_eq_getElem hij,Option.getD_some] using ht'

theorem completion_forced_invalid (d s m : Nat) (pre : List Nat) (lower remaining : Nat)
    (hv : valid 14 ⟨profileGraph d m (pre ++ List.replicate remaining (forcedType d lower)),
      rootChosen s⟩ = false) : CompletionFree d s m pre lower remaining := by
  intro ts hl _ hb full P
  have hsub : BitSubset
      (profileGraph d m (pre ++ List.replicate remaining (forcedType d lower))) full.graph := by
    apply edgesGraph_subset
    intro e he
    have ha := P.edge_actual e (forced_edges d m pre ts lower remaining hl hb e he)
    exact ⟨ha,P.model.symm e.1 e.2 ▸ ha⟩
  have ht := valid_mono 14 hsub P.root_selected P.model.valid
  simp [hv] at ht

#print axioms completion_forced_invalid
end Se20Fractional.FourthPass.Packed
