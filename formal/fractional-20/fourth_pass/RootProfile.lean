import fourth_pass.ProfileGraph
import fourth_pass.CutSearch

namespace Se20Fractional.FourthPass.Packed
open Finset

structure RootProfile (d s m : Nat) (ts : List Nat) (full : State) : Prop where
  model : Model 14 full
  d_le : d ≤ 4
  s_le : s ≤ d
  s_ge : 3 ≤ s
  length : d+1+ts.length = 14
  ordered : ∀ e ∈ full.chosen, e.1 < e.2
  nodup : full.chosen.Nodup
  size : full.chosen.length = 16
  root : ∀ v, v < 14 → (adjacent 14 full.graph 0 v = true ↔ 1 ≤ v ∧ v ≤ d)
  root_selected : ∀ e ∈ rootChosen s, e ∈ full.chosen
  root_bound : ∀ e ∈ full.chosen, e.1 = 0 → e.2 ≤ s
  inner : ∀ a b, 1 ≤ a → a < b → b ≤ d →
    ((a,b) ∈ innerEdges d m ↔ adjacent 14 full.graph a b = true)
  types : ∀ x, x < ts.length → ∀ a, a < d →
    adjacent 14 full.graph (a+1) (d+1+x) = (ts[x]?.getD 0).testBit a

theorem mem_innerEdges_bounds {d m : Nat} {e : Edge} (he : e ∈ innerEdges d m) :
    1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ d := by
  obtain ⟨⟨f,i⟩,hf,hef⟩ := List.mem_map.mp he
  dsimp only at hef
  subst f
  have hzip := (List.mem_filter.mp hf).1
  have hmem : e ∈ innerPairs d := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hzip)
  obtain ⟨hp,ha⟩ := List.mem_filter.mp hmem
  have hb := (mem_pairs (d+1) e.1 e.2).mp hp
  simp only [decide_eq_true_eq] at ha
  omega

theorem RootProfile.edge_bounds {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) :
    ∀ e ∈ profileEdges d m ts, e.1 < 14 ∧ e.2 < 14 := by
  intro e he
  rcases e with ⟨a,b⟩
  simp only [profileEdges,List.mem_append] at he
  rcases he with (he | he) | he
  · have h := (mem_starEdges d a b).mp he
    have := P.d_le
    omega
  · have h := mem_innerEdges_bounds he
    have := P.d_le
    omega
  · obtain ⟨x,hx,hb,ha,had,_⟩ := (mem_typeEdges d ts a b).mp he
    have := P.length
    have := P.d_le
    omega

theorem RootProfile.edge_actual {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) :
    ∀ e ∈ profileEdges d m ts, adjacent 14 full.graph e.1 e.2 = true := by
  intro e he
  have hb := P.edge_bounds e he
  rcases e with ⟨a,b⟩
  simp only [profileEdges,List.mem_append] at he
  rcases he with (he | he) | he
  · obtain ⟨rfl,hb1,hbd⟩ := (mem_starEdges d a b).mp he
    exact (P.root b hb.2).mpr ⟨hb1,hbd⟩
  · obtain ⟨ha,hab,hbd⟩ := mem_innerEdges_bounds he
    exact (P.inner a b ha hab hbd).mp he
  · obtain ⟨x,hx,rfl,ha,had,ht⟩ := (mem_typeEdges d ts a b).mp he
    have hae : a = (a-1)+1 := by omega
    rw [hae,P.types x hx (a-1) (by omega)]
    exact ht

theorem RootProfile.boundary {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) : Boundary 14 d (profileGraph d m ts) full.graph := by
  have hdir (a b : Nat) (had : a ≤ d) (hab : adjacent 14 full.graph a b = true) :
      adjacent 14 (profileGraph d m ts) a b = true := by
    have hb := ((adjacent_iff 14 full.graph a b).mp hab).2
    have ha := ((adjacent_iff 14 full.graph b a).mp (P.model.symm a b ▸ hab)).2
    apply (edgesGraph_adj (profileEdges d m ts) ha hb P.edge_bounds).mpr
    by_cases ha0 : a = 0
    · subst a
      have hroot := (P.root b hb).mp hab
      exact ⟨(0,b),by simp only [profileEdges,List.mem_append]; exact Or.inl (Or.inl
        ((mem_starEdges d 0 b).mpr ⟨rfl,hroot⟩)),Or.inl ⟨rfl,rfl⟩⟩
    by_cases hb0 : b = 0
    · subst b
      have hroot := (P.root a ha).mp (P.model.symm a 0 ▸ hab)
      exact ⟨(0,a),by simp only [profileEdges,List.mem_append]; exact Or.inl (Or.inl
        ((mem_starEdges d 0 a).mpr ⟨rfl,hroot⟩)),Or.inr ⟨rfl,rfl⟩⟩
    by_cases hbd : b ≤ d
    · have hne : a ≠ b := by intro h; subst b; simp [P.model.irrefl] at hab
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hi := (P.inner a b (by omega) hlt hbd).mpr hab
        exact ⟨(a,b),by simp only [profileEdges,List.mem_append]; exact Or.inl (Or.inr hi),
          Or.inl ⟨rfl,rfl⟩⟩
      · have hi := (P.inner b a (by omega) hgt had).mpr (P.model.symm a b ▸ hab)
        exact ⟨(b,a),by simp only [profileEdges,List.mem_append]; exact Or.inl (Or.inr hi),
          Or.inr ⟨rfl,rfl⟩⟩
    · have hx : b-(d+1) < ts.length := by have := P.length; omega
      have hax : a-1 < d := by omega
      have he : d+1+(b-(d+1)) = b := by omega
      have hae : (a-1)+1 = a := by omega
      have ht : (ts[b-(d+1)]?.getD 0).testBit (a-1) = true := by
        rw [← P.types _ hx _ hax,he,hae]
        exact hab
      have hi := (mem_typeEdges d ts a b).mpr ⟨b-(d+1),hx,he.symm,by omega,had,ht⟩
      exact ⟨(a,b),by simp only [profileEdges,List.mem_append]; exact Or.inr hi,Or.inl ⟨rfl,rfl⟩⟩
  intro a b hd hab
  rcases hd with ha | hb
  · exact hdir a b ha hab
  · have hba := hdir b a hb (P.model.symm a b ▸ hab)
    have hb' := ((adjacent_iff 14 full.graph a b).mp hab).2
    have ha' := ((adjacent_iff 14 full.graph b a).mp (P.model.symm a b ▸ hab)).2
    change adjacent 14 (edgesGraph 14 (profileEdges d m ts)) b a = true at hba
    rw [edgesGraph_symm 14 (profileEdges d m ts) P.edge_bounds b hb' a ha'] at hba
    exact hba

theorem RootProfile.extends {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) :
    Extends 14 d ⟨profileGraph d m ts,rootChosen s⟩ full := by
  refine ⟨?_,edgesGraph_symm 14 _ P.edge_bounds,P.boundary,P.root_selected⟩
  apply edgesGraph_subset
  intro e he
  have h := P.edge_actual e he
  exact ⟨h,P.model.symm e.1 e.2 ▸ h⟩

theorem RootProfile.outer_cover {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) {u v : Nat} (he : (u,v) ∈ full.chosen) (hu : d < u) :
    ((ts[u-d-1]?.getD 0 ||| ts[v-d-1]?.getD 0) &&& mask s) = mask s := by
  have huv := P.ordered (u,v) he
  have hb := P.model.bounds (u,v) he
  have hx : u-d-1 < ts.length := by have := P.length; omega
  have hy : v-d-1 < ts.length := by have := P.length; omega
  have hux : d+1+(u-d-1) = u := by omega
  have hvy : d+1+(v-d-1) = v := by omega
  have hbit (i : Nat) (hi : i < s) :
      (ts[u-d-1]?.getD 0 ||| ts[v-d-1]?.getD 0).testBit i = true := by
    have hid : i < d := by have := P.s_le; omega
    have hr : (0,i+1) ∈ full.chosen := P.root_selected _ (by simpa [rootChosen] using hi)
    have hc := P.model.conflicts (0,i+1) hr (u,v) he
    have h0u : ¬ adjacent 14 full.graph 0 u = true := by
      intro h; have := (P.root u hb.1).mp h; omega
    have h0v : ¬ adjacent 14 full.graph 0 v = true := by
      intro h; have := (P.root v hb.2).mp h; omega
    have hchoices : adjacent 14 full.graph (i+1) u = true ∨
        adjacent 14 full.graph (i+1) v = true := by
      have h0u' : (0 : Nat) ≠ u := by omega
      have h0v' : (0 : Nat) ≠ v := by omega
      have hiu : i+1 ≠ u := by omega
      have hiv : i+1 ≠ v := by omega
      simpa only [conflict_iff,h0u',h0v',hiu,hiv,h0u,h0v,Bool.false_eq_true,false_or] using hc
    rw [Nat.testBit_or]
    simp only [Bool.or_eq_true]
    have htx := P.types (u-d-1) hx i hid
    have hty := P.types (v-d-1) hy i hid
    rw [hux] at htx
    rw [hvy] at hty
    simpa only [htx,hty] using hchoices
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,mask,bit_eq_pow,Nat.testBit_two_pow_sub_one]
  by_cases hi : i < s
  · simp [hi,hbit i hi]
  · simp [hi]

theorem RootProfile.selected_cover {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) {e : Edge} (he : e ∈ full.chosen) :
    e ∈ rootChosen s ∨ e ∈ candidates 14 d s (profileGraph d m ts) ts := by
  rcases e with ⟨a,b⟩
  have hab := P.ordered (a,b) he
  have hb := P.model.bounds (a,b) he
  by_cases ha : a = 0
  · subst a
    have hbs := P.root_bound (0,b) he rfl
    left
    change (0,b) ∈ starEdges s
    exact (mem_starEdges s 0 b).mpr ⟨rfl,by omega,hbs⟩
  · right
    apply List.mem_filter.mpr
    refine ⟨(mem_pairs 14 a b).mpr ⟨hb.1,hb.2,hab⟩,?_⟩
    have ha' : 0 < a := by omega
    by_cases had : a ≤ d
    · have hedge := P.boundary a b (Or.inl had) (P.model.edges (a,b) he)
      simp only [had,↓reduceIte,hedge,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨ha',True.intro⟩
    · have hcov := P.outer_cover he (by omega)
      simp only [had,↓reduceIte,hcov,beq_self_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨ha',True.intro⟩

theorem RootProfile.enough_candidates {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full) :
    16-s ≤ ((candidates 14 d s (profileGraph d m ts) ts).filter
      (fun e => decide (e ∈ full.chosen))).length := by
  let cs := candidates 14 d s (profileGraph d m ts) ts
  let good := cs.filter (fun e => decide (e ∈ full.chosen))
  have hsub : full.chosen.toFinset ⊆ (rootChosen s).toFinset ∪ good.toFinset := by
    intro e he
    have he' : e ∈ full.chosen := List.mem_toFinset.mp he
    rcases P.selected_cover he' with hr | hc
    · exact mem_union_left _ (List.mem_toFinset.mpr hr)
    · exact mem_union_right _ (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hc,by simp [he']⟩))
  have hcount := (card_le_card hsub).trans (card_union_le _ _)
  have hroot : (rootChosen s).toFinset.card ≤ s := by
    calc
      _ ≤ (rootChosen s).length := List.toFinset_card_le (rootChosen s)
      _ = s := by simp [rootChosen]
  have hgood := List.toFinset_card_le (l := good)
  rw [List.toFinset_card_of_nodup P.nodup,P.size] at hcount
  change 16-s ≤ good.length
  omega

theorem RootProfile.false_of_safe {d s m : Nat} {ts : List Nat} {full : State}
    (P : RootProfile d s m ts full)
    (hs : Safe 14 d (16-s) (some ⟨profileGraph d m ts,rootChosen s⟩)
      (candidates 14 d s (profileGraph d m ts) ts)) : False := by
  have h := hs full ⟨P.model,_,rfl,P.extends⟩
  have hc := P.enough_candidates
  omega

#print axioms RootProfile.extends
#print axioms RootProfile.false_of_safe
end Se20Fractional.FourthPass.Packed
