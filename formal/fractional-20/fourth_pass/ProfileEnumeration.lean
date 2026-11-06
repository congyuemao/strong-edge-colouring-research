import fourth_pass.CanonicalProfile

namespace Se20Fractional.FourthPass.Packed

theorem typeEdges_prefix (d : Nat) (as bs : List Nat) :
    ∀ e ∈ typeEdges d as, e ∈ typeEdges d (as ++ bs) := by
  rintro ⟨a,b⟩ he
  obtain ⟨x,hx,hb,ha,hd,ht⟩ := (mem_typeEdges d as a b).mp he
  apply (mem_typeEdges d (as ++ bs) a b).mpr
  refine ⟨x,by simp only [List.length_append]; omega,hb,ha,hd,?_⟩
  simpa only [List.getElem?_append_left hx] using ht

theorem profileEdges_prefix (d m : Nat) (as bs : List Nat) :
    ∀ e ∈ profileEdges d m as, e ∈ profileEdges d m (as ++ bs) := by
  intro e he
  simp only [profileEdges,List.mem_append] at he ⊢
  rcases he with h | h
  · exact Or.inl h
  · exact Or.inr (typeEdges_prefix d as bs e h)

theorem RootProfile.prefix_valid {d s m : Nat} {as bs : List Nat} {full : State}
    (P : RootProfile d s m (as ++ bs) full) :
    valid 14 ⟨profileGraph d m as,rootChosen s⟩ = true := by
  refine valid_mono 14 ?_ P.root_selected P.model.valid
  · apply edgesGraph_subset
    intro e he
    have ha := P.edge_actual e (profileEdges_prefix d m as bs e he)
    exact ⟨ha,P.model.symm e.1 e.2 ▸ ha⟩


def CompletionFree (d s m : Nat) (pre : List Nat) (lower remaining : Nat) : Prop :=
  ∀ ts : List Nat, ts.length = remaining → ts.Pairwise (· ≤ ·) →
    (∀ t ∈ ts, lower ≤ t ∧ t < 2^d) →
    ∀ full, RootProfile d s m (pre ++ ts) full → False

theorem completion_invalid (d s m : Nat) (pre : List Nat) (lower remaining : Nat)
    (hv : valid 14 ⟨profileGraph d m pre,rootChosen s⟩ = false) :
    CompletionFree d s m pre lower remaining := by
  intro ts _ _ _ full P
  have := P.prefix_valid
  simp [hv] at this

theorem completion_leaf (d s m : Nat) (pre : List Nat) (lower : Nat)
    (hs : Safe 14 d (16-s) (some ⟨profileGraph d m pre,rootChosen s⟩)
      (candidates 14 d s (profileGraph d m pre) pre)) :
    CompletionFree d s m pre lower 0 := by
  intro ts hl _ _ full P
  have he : ts = [] := List.length_eq_zero_iff.mp hl
  subst ts
  simp only [List.append_nil] at P
  exact P.false_of_safe hs

def BranchesFree (d s m : Nat) (pre : List Nat) (lower remaining upper : Nat) : Prop :=
  ∀ t, lower ≤ t → t < upper → CompletionFree d s m (pre ++ [t]) t remaining

theorem branches_base (d s m : Nat) (pre : List Nat) (lower remaining : Nat) :
    BranchesFree d s m pre lower remaining lower := by
  intro t hl hu
  omega

theorem branches_step (d s m : Nat) (pre : List Nat) (lower remaining upper : Nat)
    (hp : BranchesFree d s m pre lower remaining upper)
    (ht : CompletionFree d s m (pre ++ [upper]) upper remaining) :
    BranchesFree d s m pre lower remaining (upper+1) := by
  intro t hl hu
  by_cases he : t = upper
  · subst t; exact ht
  · exact hp t hl (by omega)

theorem completion_split (d s m : Nat) (pre : List Nat) (lower remaining : Nat)
    (hs : BranchesFree d s m pre lower remaining (2^d)) :
    CompletionFree d s m pre lower (remaining+1) := by
  intro ts hl ho hb full P
  cases ts with
  | nil => simp at hl
  | cons t ts =>
    have ht := hb t (by simp)
    have hs' := hs t ht.1 ht.2
    have hpair := List.pairwise_cons.mp ho
    apply hs' ts (by simpa using hl) hpair.2 (fun a ha => ⟨hpair.1 a ha,(hb a (by simp [ha])).2⟩) full
    simpa only [List.append_assoc,List.singleton_append] using P

#print axioms completion_split
#print axioms completion_invalid
end Se20Fractional.FourthPass.Packed
