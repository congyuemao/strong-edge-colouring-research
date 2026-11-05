import Se20Insertion.CliqueReduction

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Se20Insertion.ComponentInsertion
variable {W : Type*} [DecidableEq W] (H : SimpleGraph W)

def count (S : Finset W) : ℕ := Nat.card (H.induce (S : Set W)).ConnectedComponent

def Touches (S : Finset W) (f : W) (c : (H.induce (S : Set W)).ConnectedComponent) : Prop :=
  ∃ x : S, H.Adj f x.val ∧ (H.induce (S : Set W)).connectedComponentMk x = c

def touchingCount (S : Finset W) (f : W) : ℕ :=
  Nat.card {c : (H.induce (S : Set W)).ConnectedComponent // Touches H S f c}

/-- Exact insertion/deletion identity, including zero neighbours and isolated vertices. -/
theorem count_insert (S : Finset W) (f : W) (hf : f ∉ S) :
    count H (insert f S) + touchingCount H S f = count H S + 1 := by
  let D := H.induce (S : Set W)
  let J := H.induce (↑(insert f S) : Set W)
  let C := D.ConnectedComponent
  let T : C → Prop := Touches H S f
  let Q := {c : C // ¬ T c}
  let emb : D →g J := ⟨fun x => ⟨x.val,Finset.mem_insert_of_mem x.property⟩,fun h => h⟩
  let root : (insert f S : Finset W) := ⟨f,Finset.mem_insert_self _ _⟩
  let old (x : (insert f S : Finset W)) (hx : x.val ≠ f) : S :=
    ⟨x.val,(Finset.mem_insert.mp x.property).resolve_left hx⟩
  let code : ↥(insert f S) → Option Q := fun x =>
    if hx : x.val = f then none else
      if ht : T (D.connectedComponentMk (old x hx)) then none
      else some ⟨D.connectedComponentMk (old x hx),ht⟩
  have old_ne (x : S) : x.val ≠ f := fun h => hf (h ▸ x.property)
  have code_root : code root = none := by simp [code,root]
  have code_old (x : S) : code (emb x) =
      if ht : T (D.connectedComponentMk x) then none else some ⟨D.connectedComponentMk x,ht⟩ := by
    simp [code,emb,old,old_ne x]
  have old_root (x : S) (hx : T (D.connectedComponentMk x)) : J.Reachable root (emb x) := by
    obtain ⟨y,hy,hyc⟩ := hx
    have hr : D.Reachable y x := SimpleGraph.ConnectedComponent.exact hyc
    exact (show J.Adj root (emb y) from hy).reachable.trans (hr.map emb)
  have adjacent {x y : (insert f S : Finset W)} (hxy : J.Adj x y) : code x = code y := by
    by_cases hx : x.val = f
    · have hxe : x = root := Subtype.ext hx
      subst x
      have hy : y.val ≠ f := fun h => hxy.ne (Subtype.ext h.symm)
      have hyold : emb (old y hy) = y := Subtype.ext rfl
      rw [← hyold,code_root,code_old]
      have ht : T (D.connectedComponentMk (old y hy)) := ⟨old y hy,hxy,rfl⟩
      simp [ht]
    by_cases hy : y.val = f
    · have hye : y = root := Subtype.ext hy
      subst y
      have hxold : emb (old x hx) = x := Subtype.ext rfl
      rw [← hxold,code_root,code_old]
      have ht : T (D.connectedComponentMk (old x hx)) := ⟨old x hx,hxy.symm,rfl⟩
      simp [ht]
    have hxold : emb (old x hx) = x := Subtype.ext rfl
    have hyold : emb (old y hy) = y := Subtype.ext rfl
    rw [← hxold,← hyold,code_old,code_old]
    have heq : D.connectedComponentMk (old x hx) = D.connectedComponentMk (old y hy) :=
      SimpleGraph.ConnectedComponent.sound (show D.Adj (old x hx) (old y hy) from hxy).reachable
    simp only [heq]
  have reachable_code {x y : (insert f S : Finset W)} (hxy : J.Reachable x y) : code x = code y := by
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => rfl
    | cons h p ih => exact (adjacent h).trans ih
  have code_reachable {x y : (insert f S : Finset W)} (hc : code x = code y) : J.Reachable x y := by
    have root_of_none (x : (insert f S : Finset W)) (hx : code x = none) : J.Reachable root x := by
      by_cases hxf : x.val = f
      · have heq : x = root := Subtype.ext hxf
        subst x; exact SimpleGraph.Reachable.refl _
      · have hxold : emb (old x hxf) = x := Subtype.ext rfl
        rw [← hxold,code_old] at hx
        have ht : T (D.connectedComponentMk (old x hxf)) := by
          by_contra ht; simp [ht] at hx
        exact hxold ▸ old_root (old x hxf) ht
    by_cases hx : code x = none
    · exact (root_of_none x hx).symm.trans (root_of_none y (hc.symm.trans hx))
    have hy : code y ≠ none := fun h => hx (hc.trans h)
    have hxf : x.val ≠ f := by intro h; apply hx; simp [code,h]
    have hyf : y.val ≠ f := by intro h; apply hy; simp [code,h]
    have hxold : emb (old x hxf) = x := Subtype.ext rfl
    have hyold : emb (old y hyf) = y := Subtype.ext rfl
    rw [← hxold,← hyold,code_old,code_old] at hc
    have htx : ¬ T (D.connectedComponentMk (old x hxf)) := by
      intro ht; apply hx; rw [← hxold,code_old]; simp [ht]
    have hty : ¬ T (D.connectedComponentMk (old y hyf)) := by
      intro ht; apply hy; rw [← hyold,code_old]; simp [ht]
    simp only [dif_neg htx,dif_neg hty,Option.some.injEq,Subtype.mk.injEq] at hc
    have hr := (SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hc)).map emb
    simpa only [hxold,hyold] using hr
  let map : J.ConnectedComponent → Option Q := Quot.lift code (fun _ _ h => reachable_code h)
  have hm (x : (insert f S : Finset W)) : map (J.connectedComponentMk x) = code x := rfl
  have hinj : Function.Injective map := by
    intro c d
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      induction d using SimpleGraph.ConnectedComponent.ind with
      | h y => exact fun h => SimpleGraph.ConnectedComponent.sound (code_reachable h)
  have hsur : Function.Surjective map := by
    intro q
    cases q with
    | none => exact ⟨J.connectedComponentMk root,code_root⟩
    | some c =>
      obtain ⟨x,hx⟩ := Quot.mk_surjective c.val
      refine ⟨J.connectedComponentMk (emb x),?_⟩
      rw [hm,code_old]
      have hx : D.connectedComponentMk x = c.val := hx
      simp only [hx,dif_neg c.property]
      rfl
  have hcard := Nat.card_congr (Equiv.ofBijective map ⟨hinj,hsur⟩)
  letI := Fintype.ofFinite C
  have hparts := Fintype.card_subtype_compl T
  have hle := Fintype.card_subtype_le T
  have hopt : Nat.card (Option Q) = Nat.card Q + 1 := by simp [Nat.card_eq_fintype_card]
  change Nat.card J.ConnectedComponent + Nat.card {c : C // T c} = Nat.card C + 1
  rw [hcard,hopt]
  simp only [Nat.card_eq_fintype_card]
  change Fintype.card {c : C // ¬ T c} + 1 + Fintype.card {c : C // T c} = Fintype.card C + 1
  omega

end Se20Insertion.ComponentInsertion
