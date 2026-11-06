import Se20Part.Gallai

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part
variable {W : Type*} [Fintype W] (H : SimpleGraph W)

def vertexBoundary (S : Finset W) : Finset W :=
  Finset.univ.filter (fun y => y ∉ S ∧ ∃ x ∈ S, H.Adj x y)

theorem mem_vertexBoundary {S : Finset W} {y : W} :
    y ∈ vertexBoundary H S ↔ y ∉ S ∧ ∃ x ∈ S, H.Adj x y := by
  simp [vertexBoundary]

/-- A disconnected induced graph has an actual finite separation. -/
theorem finite_induced_separation (U : Finset W)
    (hn : ¬ (H.induce (U : Set W)).Preconnected) :
    ∃ D E : Finset W, D.Nonempty ∧ E.Nonempty ∧ Disjoint D E ∧ D ∪ E = U ∧
      ∀ x ∈ D, ∀ y ∈ E, ¬ H.Adj x y := by
  simp only [SimpleGraph.Preconnected,not_forall] at hn
  obtain ⟨x,y,hxy⟩ := hn
  let D := U.filter (fun w => ∃ hw : w ∈ U, (H.induce (U : Set W)).Reachable x ⟨w,hw⟩)
  let E := U \ D
  have hx : x.val ∈ D := Finset.mem_filter.mpr ⟨x.prop,⟨x.prop,SimpleGraph.Reachable.refl _⟩⟩
  have hy : y.val ∈ E := Finset.mem_sdiff.mpr ⟨y.prop,by
    rintro hh
    obtain ⟨hw,hh⟩ := (Finset.mem_filter.mp hh).2
    exact hxy hh⟩
  refine ⟨D,E,⟨x.val,hx⟩,⟨y.val,hy⟩,Finset.disjoint_left.mpr
    (fun _ hd he => (Finset.mem_sdiff.mp he).2 hd),?_,?_⟩
  · exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
  · intro a ha b hb hab
    obtain ⟨haU,ha⟩ := Finset.mem_filter.mp ha
    obtain ⟨_,ha⟩ := ha
    obtain ⟨hbU,hb⟩ := Finset.mem_sdiff.mp hb
    exact hb (Finset.mem_filter.mpr ⟨hbU,⟨hbU,ha.trans
      (SimpleGraph.Adj.reachable (G := H.induce (U : Set W))
        (u := ⟨a,haU⟩) (v := ⟨b,hbU⟩) hab)⟩⟩)

/-- Every nonempty finite graph has an end block. S is its nonempty
interior, and all neighbours of S are in B; B has at most one extra vertex.
The block may be an entire connected component. No block-tree theorem is
assumed. -/
theorem exists_end_block [Nonempty W] :
    ∃ S B : Finset W, S.Nonempty ∧ S ⊆ B ∧ (B \ S).card ≤ 1 ∧
      (∀ x ∈ S, ∀ y, H.Adj x y → y ∈ B) ∧ BlockEligible H B := by
  let regions := (Finset.univ : Finset W).powerset.filter
    (fun S => S.Nonempty ∧ (vertexBoundary H S).card ≤ 1)
  have hreg : regions.Nonempty := by
    refine ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),
      Finset.univ_nonempty,?_⟩⟩
    simp [vertexBoundary]
  obtain ⟨S,hS,hmin⟩ := regions.exists_min_image Finset.card hreg
  obtain ⟨hne,hbound⟩ := (Finset.mem_filter.mp hS).2
  have minimal (D : Finset W) (hD : D.Nonempty) (hb : (vertexBoundary H D).card ≤ 1) :
      S.card ≤ D.card := hmin D (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hD,hb⟩)
  let B := S ∪ vertexBoundary H S
  have hSB : S ⊆ B := Finset.subset_union_left
  have closed : ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ B := by
    intro x hx y hxy
    by_cases hy : y ∈ S
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ ((mem_vertexBoundary H).mpr ⟨hy,x,hx,hxy⟩)
  have hBS : (B \ S).card ≤ 1 := (Finset.card_le_card (by
    intro x hx
    exact (Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1).resolve_left (Finset.mem_sdiff.mp hx).2
    : B \ S ⊆ vertexBoundary H S)).trans hbound
  have smaller (D E : Finset W) (hD : D.Nonempty) (hE : E.Nonempty)
      (hdis : Disjoint D E) (hDS : D ⊆ S) (hDB : D ⊆ B) (hEB : E ⊆ B)
      (v : W) (hv : v ∈ B) (hvD : v ∉ D) (hvE : v ∉ E)
      (hcover : D ∪ E = B.erase v)
      (hsep : ∀ x ∈ D, ∀ y ∈ E, ¬ H.Adj x y) : False := by
    have hdproper : D.card < S.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hDS,?_⟩
      intro he
      have hvS : v ∉ S := he ▸ hvD
      obtain ⟨y,hy⟩ := hE
      have hyS : y ∉ S := fun hh => Finset.disjoint_left.mp hdis (he.symm ▸ hh) hy
      have hvB := Finset.mem_sdiff.mpr ⟨hv,hvS⟩
      have hyB := Finset.mem_sdiff.mpr ⟨hEB hy,hyS⟩
      have hyv : y = v := Finset.card_le_one.mp hBS y hyB v hvB
      exact hvE (hyv ▸ hy)
    have hb : vertexBoundary H D ⊆ {v} := by
      intro y hy
      obtain ⟨hyD,x,hx,hxy⟩ := (mem_vertexBoundary H).mp hy
      by_cases hyv : y = v
      · simpa [hyv]
      have hyB := closed x (hDS hx) y hxy
      have hyDE : y ∈ D ∪ E := hcover.symm ▸ Finset.mem_erase.mpr ⟨hyv,hyB⟩
      exact (hsep x hx y ((Finset.mem_union.mp hyDE).resolve_left hyD) hxy).elim
    have hm := minimal D hD ((Finset.card_le_card hb).trans (by simp))
    omega
  have noCut : ∀ v : B, (H.induce (B.erase v.val : Set W)).Preconnected := by
    intro v
    by_contra hn
    obtain ⟨D,E,hD,hE,hdis,hcover,hsep⟩ := finite_induced_separation H (B.erase v.val) hn
    have hDB : D ⊆ B := fun x hx => Finset.mem_of_mem_erase
      (hcover ▸ Finset.mem_union_left E hx)
    have hEB : E ⊆ B := fun x hx => Finset.mem_of_mem_erase
      (hcover ▸ Finset.mem_union_right D hx)
    have hvD : v.val ∉ D := fun h => (Finset.mem_erase.mp
      (hcover ▸ Finset.mem_union_left E h)).1 rfl
    have hvE : v.val ∉ E := fun h => (Finset.mem_erase.mp
      (hcover ▸ Finset.mem_union_right D h)).1 rfl
    have sides : D ⊆ S ∨ E ⊆ S := by
      by_contra! hn
      obtain ⟨d,hd,hdS⟩ := Finset.not_subset.mp hn.1
      obtain ⟨e,he,heS⟩ := Finset.not_subset.mp hn.2
      have hde := Finset.card_le_one.mp hBS d
        (Finset.mem_sdiff.mpr ⟨hDB hd,hdS⟩) e (Finset.mem_sdiff.mpr ⟨hEB he,heS⟩)
      exact Finset.disjoint_left.mp hdis hd (hde.symm ▸ he)
    rcases sides with hh | hh
    · exact smaller D E hD hE hdis hh hDB hEB v.val v.prop hvD hvE hcover hsep
    · exact smaller E D hE hD hdis.symm hh hEB hDB v.val v.prop hvE hvD
        (by rw [Finset.union_comm]; exact hcover) (fun x hx y hy hxy => hsep y hy x hx hxy.symm)
  have connected : (H.induce (B : Set W)).Connected := by
    have hneB : Nonempty B := let ⟨x,hx⟩ := hne; ⟨⟨x,hSB hx⟩⟩
    refine { nonempty := hneB, preconnected := ?_ }
    by_contra hn
    obtain ⟨D,E,hD,hE,hdis,hcover,hsep⟩ := finite_induced_separation H B hn
    have hDS : (D ∩ S).Nonempty := by
      obtain ⟨d,hd⟩ := hD
      by_cases hdS : d ∈ S
      · exact ⟨d,Finset.mem_inter.mpr ⟨hd,hdS⟩⟩
      have hdB : d ∈ B := hcover ▸ Finset.mem_union_left E hd
      obtain ⟨_,x,hx,hxd⟩ := (mem_vertexBoundary H).mp ((Finset.mem_union.mp hdB).resolve_left hdS)
      have hxDE : x ∈ D ∪ E := hcover.symm ▸ hSB hx
      have hxD := (Finset.mem_union.mp hxDE).resolve_right (fun he => hsep d hd x he hxd.symm)
      exact ⟨x,Finset.mem_inter.mpr ⟨hxD,hx⟩⟩
    have hES : (E ∩ S).Nonempty := by
      obtain ⟨e,he⟩ := hE
      by_cases heS : e ∈ S
      · exact ⟨e,Finset.mem_inter.mpr ⟨he,heS⟩⟩
      have heB : e ∈ B := hcover ▸ Finset.mem_union_right D he
      obtain ⟨_,x,hx,hxe⟩ := (mem_vertexBoundary H).mp ((Finset.mem_union.mp heB).resolve_left heS)
      have hxDE : x ∈ D ∪ E := hcover.symm ▸ hSB hx
      have hxE := (Finset.mem_union.mp hxDE).resolve_left (fun hd => hsep x hd e he hxe)
      exact ⟨x,Finset.mem_inter.mpr ⟨hxE,hx⟩⟩
    have hb : vertexBoundary H (D ∩ S) ⊆ vertexBoundary H S := by
      intro y hy
      obtain ⟨hyDS,x,hx,hxy⟩ := (mem_vertexBoundary H).mp hy
      obtain ⟨hxD,hxS⟩ := Finset.mem_inter.mp hx
      have hyS : y ∉ S := by
        intro hyS
        have hyDE : y ∈ D ∪ E := hcover.symm ▸ hSB hyS
        have hyE := (Finset.mem_union.mp hyDE).resolve_left
          (fun hyD => hyDS (Finset.mem_inter.mpr ⟨hyD,hyS⟩))
        exact hsep x hxD y hyE hxy
      exact (mem_vertexBoundary H).mpr ⟨hyS,x,hxS,hxy⟩
    have hlt : (D ∩ S).card < S.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,?_⟩
      intro heq
      obtain ⟨e,he⟩ := hES
      have heD := (Finset.mem_inter.mp (heq.symm ▸ (Finset.mem_inter.mp he).2)).1
      exact Finset.disjoint_left.mp hdis heD (Finset.mem_inter.mp he).1
    have hm := minimal (D ∩ S) hDS ((Finset.card_le_card hb).trans hbound)
    omega
  refine ⟨S,B,hne,hSB,hBS,closed,connected,?_⟩
  intro v
  let f : H.induce (B.erase v.val : Set W) →g
      (H.induce (B : Set W)).induce {w | w ≠ v} :=
    { toFun := fun x => ⟨⟨x.val,Finset.mem_of_mem_erase x.prop⟩,
        fun he => (Finset.mem_erase.mp x.prop).1 (congrArg Subtype.val he)⟩
      map_rel' := fun h => h }
  apply (noCut v).map f
  intro x
  exact ⟨⟨x.val.val,Finset.mem_erase.mpr
    ⟨fun he => x.prop (Subtype.ext he),x.val.prop⟩⟩,rfl⟩

end Se20Part
