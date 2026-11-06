import Se20Part.DecorationCounting
import Se20Part.TransferCounting

noncomputable section
open scoped Classical BigOperators
open SimpleGraph Finset
namespace Se20Part
set_option maxHeartbeats 0

abbrev PositiveDepth := {d : Fin 6 // 0 < d.val}

abbrev FamilyCode {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) (n : ℕ) :=
  Σ k : Fin (n+1), Σ d : PositiveDepth, Σ f : RootedPattern n k.val (Nat.le_of_lt_succ k.isLt) d.val,
    EmbeddedPattern G e n k.val d.val.val f.val

def codeEdges {V : Type*} [Fintype V] {G : SimpleGraph V} {e : G.edgeSet} {n : ℕ}
    (c : FamilyCode G e n) : Finset G.edgeSet :=
  insert e (univ.image (fun i => (c.2.2.2.2 i).val))

def codeWeight {V : Type*} [Fintype V] {G : SimpleGraph V} {e : G.edgeSet} {n : ℕ}
    (c : FamilyCode G e n) : ℚ := t5710^(Fintype.card (RootPositions c.2.2.1.val c.1.val))

theorem finitePattern_valid {n : ℕ} (f : ℕ → ℕ) (hf : ValidDepthPattern f n) :
    ValidSpanningPattern (fun i : Fin (n+1) => (⟨f i.val,by have := hf.bounded i.val (Nat.le_of_lt_succ i.isLt); omega⟩ : Fin 6)) := by
  refine ⟨by change f 0 ≠ 0; exact Nat.ne_of_gt hf.first,?_,?_⟩
  · intro i j hij hfi hfj
    exact hf.spacing i.val j.val hij (Nat.le_of_lt_succ j.isLt) (Nat.pos_of_ne_zero hfi) (Nat.pos_of_ne_zero hfj)
  · intro k hk
    obtain ⟨i,j,hi,hj,hjn,hfi,hfj,hspan⟩ := hf.spans k hk
    exact ⟨⟨i,by omega⟩,⟨j,by omega⟩,hi,hj,Nat.ne_of_gt hfi,Nat.ne_of_gt hfj,hspan⟩

theorem familyCode_exists {V : Type} [Fintype V] {G : SimpleGraph V}
    (E : Set G.edgeSet) (S : Finset E) (e : E) (he : e ∈ S)
    {u v : V} (Y : G.Walk u v) (hy : Y.IsPath) (hn : 0 < Y.length)
    (F : SpanningFamily (realFamily S) Y) (hF : F.edges = realFamily S)
    (hinj : Function.Injective (fun r => (F.projection r).pos))
    (hs : Separated G 5 (realFamily S)) :
    ∃ c : FamilyCode G e.val Y.length,
      codeEdges c = S.image Subtype.val ∧ codeWeight c = t5710^(S.card-1) := by
  let r : F.edges := ⟨e.val,by rw [hF]; exact ⟨e,he,rfl⟩⟩
  let k : Fin (Y.length+1) := ⟨(F.projection r).pos,by have := (F.projection r).pos_le; omega⟩
  let d : PositiveDepth := ⟨⟨(F.projection r).depth,by have := F.depth_le r; omega⟩,F.positive r⟩
  have hvalid := F.validDepthPattern hinj hs hn
  let f : SpanningPattern Y.length := fun i => ⟨F.depthPattern i.val,by have := F.depthPattern_bounded i.val; omega⟩
  have hf : ValidSpanningPattern f := finitePattern_valid F.depthPattern hvalid
  have hroot : f k = d.val := Fin.ext (F.depthPattern_at hinj r)
  have hpos (i : RootPositions f k.val) : 0 < F.depthPattern i.val.val := Nat.pos_of_ne_zero i.property.2
  choose pick hpick hdepth using fun i : RootPositions f k.val => F.depthPattern_positive (hpos i)
  let Y' : Segment G Y.length := ⟨u,v,⟨Y,hy⟩,rfl⟩
  let yr : RootSegment G e.val Y.length k.val d.val.val := ⟨Y',F.projection r,rfl,rfl⟩
  let dec : Decoration Y' f k.val := fun i => ⟨(pick i).val,F.projection (pick i),hpick i,hdepth i⟩
  let c : FamilyCode G e.val Y.length := ⟨k,d,⟨f,hf,hroot⟩,yr,dec⟩
  have hrec : codeEdges c = S.image Subtype.val := by
    ext a
    constructor
    · intro ha
      rcases mem_insert.mp ha with ha | ha
      · exact mem_image.mpr ⟨e,he,ha.symm⟩
      · obtain ⟨i,_,hi⟩ := mem_image.mp ha
        have hmem := (pick i).property
        have hmem' : (pick i).val ∈ realFamily S := hF.le hmem
        obtain ⟨s,hsS,hsa⟩ := hmem'
        exact mem_image.mpr ⟨s,hsS,hsa.trans hi⟩
    · intro ha
      obtain ⟨s,hsS,rfl⟩ := mem_image.mp ha
      by_cases hse : s = e
      · subst s; exact mem_insert_self _ _
      · let q : F.edges := ⟨s.val,by rw [hF]; exact ⟨s,hsS,rfl⟩⟩
        let j : Fin (Y.length+1) := ⟨(F.projection q).pos,by have := (F.projection q).pos_le; omega⟩
        have hjk : j.val ≠ k.val := by
          intro hh
          have hqr := hinj hh
          exact hse (Subtype.ext (congrArg (fun a : F.edges => a.val) hqr))
        have hjf : (f j).val ≠ 0 := by
          change F.depthPattern (F.projection q).pos ≠ 0
          rw [F.depthPattern_at hinj q]
          have := F.positive q
          omega
        let i : RootPositions f k.val := ⟨j,hjk,hjf⟩
        apply mem_insert_of_mem
        apply mem_image.mpr
        refine ⟨i,mem_univ _,?_⟩
        exact congrArg Subtype.val (hinj (hpick i))
  have hdecinj : Function.Injective (fun i : RootPositions f k.val => (pick i).val) := by
    intro i j hij
    have hh := congrArg (fun q : F.edges => (F.projection q).pos) (Subtype.ext hij)
    rw [hpick i,hpick j] at hh
    exact Subtype.ext (Fin.ext hh)
  have hnot : e.val ∉ univ.image (fun i : RootPositions f k.val => (pick i).val) := by
    intro hh
    obtain ⟨i,_,hi⟩ := mem_image.mp hh
    have hh := congrArg (fun q : F.edges => (F.projection q).pos) (show pick i = r from Subtype.ext hi)
    rw [hpick i] at hh
    exact i.property.1 hh
  have hcard : Fintype.card (RootPositions f k.val) = S.card-1 := by
    have hh := congrArg Finset.card hrec
    change (insert e.val (univ.image (fun i : RootPositions f k.val => (pick i).val))).card =
      (S.image Subtype.val).card at hh
    rw [card_insert_of_notMem hnot,card_image_of_injective _ hdecinj,card_univ,
      card_image_of_injective _ Subtype.val_injective] at hh
    omega
  exact ⟨c,hrec,by change t5710^(Fintype.card (RootPositions f k.val)) = _; rw [hcard]⟩

theorem familyCode_exists_length {V : Type} [Fintype V] {G : SimpleGraph V}
    (E : Set G.edgeSet) (S : Finset E) (e : E) (he : e ∈ S)
    {u v : V} (Y : G.Walk u v) (hy : Y.IsPath) {n : ℕ} (hlen : Y.length = n) (hn : 0 < n)
    (F : SpanningFamily (realFamily S) Y) (hF : F.edges = realFamily S)
    (hinj : Function.Injective (fun r => (F.projection r).pos))
    (hs : Separated G 5 (realFamily S)) :
    ∃ c : FamilyCode G e.val n,
      codeEdges c = S.image Subtype.val ∧ codeWeight c = t5710^(S.card-1) := by
  subst n
  exact familyCode_exists E S e he Y hy hn F hF hinj hs

end Se20Part
