import Se20Part.SmallColourPool
import Se20Part.Greedy
import Se20Part.Gallai

noncomputable section
open scoped Classical
namespace Se20Part

/-- A finite connected odd cycle, expressed by its intrinsic degrees and
order. A connected finite two-regular simple graph is a cycle. -/
def OddCycleGraph {W : Type} [Fintype W] (H : SimpleGraph W) : Prop :=
  H.Connected ∧ Odd (Fintype.card W) ∧ ∀ v, H.degree v = 2

/-- The no-cut-vertex form of degree choosability, proved below. -/
def GallaiDegreeChoosable : Prop :=
  ∀ (W C : Type) [Fintype W] [DecidableEq C] (H : SimpleGraph W),
    H.Connected → (∀ v : W, (H.induce {w | w ≠ v}).Preconnected) →
    ∀ L : W → Finset C, (∀ v, H.degree v ≤ (L v).card) →
    ¬ HasListColouring H L →
    (∀ u v, u ≠ v → H.Adj u v) ∨ OddCycleGraph H

/-- The former Gallai input is now a theorem, using the copied kernel-checked
degree-list proof. The intrinsic odd-cycle interface is unchanged. -/
theorem gallaiDegreeChoosable : GallaiDegreeChoosable := by
  intro W C _ _ H hc hdel L hd hb
  classical
  by_cases hs : Subsingleton W
  · exact Or.inl (fun u v huv => (huv (hs.elim u v)).elim)
  letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hs
  obtain ⟨x,y,hxy⟩ := exists_pair_ne W
  have hp : 0 < H.degree x := (hc x y).degree_pos_left hxy
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (hp.trans_le (hd x))
  letI : Nonempty C := ⟨a⟩
  have hdelete : ∀ v : W, (H.induce {w | w ≠ v}).Connected := by
    intro v
    obtain ⟨w,hw⟩ := exists_ne v
    exact { preconnected := hdel v, nonempty := ⟨⟨w,hw⟩⟩ }
  have hbad : ¬ DegreeList.ColourableOn H L Finset.univ := by
    rintro ⟨c,hc',hp'⟩
    exact hb ⟨c,fun v => hc' v (Finset.mem_univ _),
      fun u v huv => hp' u (Finset.mem_univ _) v (Finset.mem_univ _) huv⟩
  rcases DegreeList.bad_noncut_complete_or_odd_cycle H L hc hdelete hd hbad with hh | ho
  · exact Or.inl hh
  · obtain ⟨n,hn,⟨i⟩⟩ := ho
    refine Or.inr ⟨hc,?_,?_⟩
    · have he : Fintype.card W = n+3 :=
        (Fintype.card_congr i.toEquiv).trans (Fintype.card_fin _)
      simpa only [he] using hn
    · intro v
      rw [← i.degree_eq v]
      convert (SimpleGraph.cycleGraph_degree_three_le (v := i v)) using 1

/-- Minimality refers to every proper induced subgraph, with degrees in H. -/
def VertexMinimalNoncolourable {W : Type} [Fintype W] (H : SimpleGraph W) (k : ℕ) : Prop :=
  ¬ H.Colorable k ∧ ∀ A : Finset W, A.card < Fintype.card W →
    (H.induce (A : Set W)).Colorable k

/-- In a critical graph, every nonempty set of degree-k vertices admits
uncolourable residual lists at least as large as its current internal
degrees. The outside colouring is fixed throughout the argument. -/
theorem minimal_low_bad_lists {W : Type} [Fintype W] (H : SimpleGraph W) (k : ℕ)
    (hmin : VertexMinimalNoncolourable H k) (B : Finset W) (hB : B.Nonempty)
    (hlow : ∀ v ∈ B, H.degree v = k) :
    ∃ L : B → Finset (Fin k),
      (∀ v, (H.induce (B : Set W)).degree v ≤ (L v).card) ∧
      ¬ HasListColouring (H.induce (B : Set W)) L := by
  let O := Finset.univ \ B
  have hOc : O.card < Fintype.card W := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset W) B
    simp only [Finset.univ_inter,Finset.card_univ] at h
    have := Finset.card_pos.mpr hB
    dsimp only [O]
    omega
  obtain ⟨c⟩ := hmin.2 O hOc
  let N := fun v : B => H.neighborFinset v.val \ B
  let outside := fun (v : B) (w : N v) =>
    (⟨w.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp w.prop).2⟩⟩ : O)
  let D := fun v : B => (N v).attach.image (fun w => c (outside v w))
  let L := fun v : B => Finset.univ \ D v
  have hsize : ∀ v, (H.induce (B : Set W)).degree v ≤ (L v).card := by
    intro v
    have hD : (D v).card ≤ (N v).card := by
      exact Finset.card_image_le.trans_eq Finset.card_attach
    have hparts := Finset.card_sdiff_add_card_inter (H.neighborFinset v.val) B
    have hinner : (H.neighborFinset v.val ∩ B).card = (H.induce (B : Set W)).degree v := by
      rw [degree_induce_finset]
      congr 1
      ext w
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,Finset.mem_filter]
      exact and_comm
    rw [hinner,SimpleGraph.card_neighborFinset_eq_degree,hlow v.val v.prop] at hparts
    have he : (L v).card = k - (D v).card := by
      simp only [L,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
    change (N v).card + _ = k at hparts
    omega
  refine ⟨L,hsize,?_⟩
  rintro ⟨d,hd,hproper⟩
  have hfree : ∀ (v : B) (w : O), H.Adj v.val w.val → d v ≠ c w := by
    intro v w hvw he
    apply (Finset.mem_sdiff.mp (hd v)).2
    let z : N v := ⟨w.val,Finset.mem_sdiff.mpr
      ⟨(H.mem_neighborFinset _ _).mpr hvw,(Finset.mem_sdiff.mp w.prop).2⟩⟩
    exact Finset.mem_image.mpr ⟨z,Finset.mem_attach _ _,by
      change c (outside v z) = d v
      have hz : outside v z = w := Subtype.ext rfl
      rw [hz,he]⟩
  let f : W → Fin k := fun v => if hv : v ∈ B then d ⟨v,hv⟩
    else c ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩
  apply hmin.1
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro u v huv
  dsimp only [f]
  split_ifs with hu hv hv
  · exact hproper ⟨u,hu⟩ ⟨v,hv⟩ huv
  · exact hfree ⟨u,hu⟩ ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩ huv
  · exact (hfree ⟨v,hv⟩ ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩⟩ huv.symm).symm
  · exact c.valid huv

/-- The low-block classification used by A03/A04, now without a Gallai
hypothesis. No claim about leaf-block extension is assumed. -/
theorem minimal_low_block_classification
    {W : Type} [Fintype W] (H : SimpleGraph W) (k : ℕ)
    (hmin : VertexMinimalNoncolourable H k) (B : Finset W)
    (hconn : (H.induce (B : Set W)).Connected)
    (hnocut : ∀ v : B, ((H.induce (B : Set W)).induce {w | w ≠ v}).Preconnected)
    (hlow : ∀ v ∈ B, H.degree v = k) :
    (∀ u ∈ B, ∀ v ∈ B, u ≠ v → H.Adj u v) ∨ OddCycleGraph (H.induce (B : Set W)) := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨L,hdeg,hbad⟩ := minimal_low_bad_lists H k hmin B ⟨v.val,v.prop⟩ hlow
  rcases gallaiDegreeChoosable B (Fin k) (H.induce (B : Set W)) hconn hnocut L hdeg hbad with hc | ho
  · exact Or.inl (fun u hu v hv hne => hc ⟨u,hu⟩ ⟨v,hv⟩
      (fun h => hne (congrArg Subtype.val h)))
  · exact Or.inr ho

end Se20Part
