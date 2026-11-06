import Se20Insertion.P6Geometry
import Se20Insertion.ColourSetSpecialCases
import Se20Insertion.Neighbourhood87

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.P6.Pattern
open PartialColouring
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : Pattern G)

/-- Every outside edge sees both C--L edges at a suitable centre. -/
theorem outside_centre {e : G.edgeSet} (he : e ∈ P.outside) :
    ∃ c, P.kind c = 0 ∧ ∀ f ∈ P.edgesOf 0 1 ∩ incident G c, (L2 G).Adj e f := by
  obtain ⟨u,v,hev⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  have hne (f : G.edgeSet) (hf : f ∈ P.edgesOf 0 1) : e ≠ f := by
    intro h
    exact (Finset.mem_sdiff.mp he).2 (h ▸ hf)
  have fromEndpoint (c : V) (hc : c ∈ e.val) (hk : P.kind c = 0) :
      ∃ c, P.kind c = 0 ∧ ∀ f ∈ P.edgesOf 0 1 ∩ incident G c, (L2 G).Adj e f := by
    refine ⟨c,hk,fun f hf => ⟨hne f (Finset.mem_inter.mp hf).1,c,hc,c,?_,Or.inl rfl⟩⟩
    exact (mem_incident G c f).mp (Finset.mem_inter.mp hf).2
  have fromLower (l : V) (hl : l ∈ e.val) (hk : P.kind l = 1) :
      ∃ c, P.kind c = 0 ∧ ∀ f ∈ P.edgesOf 0 1 ∩ incident G c, (L2 G).Adj e f := by
    have hn := P.neighbours l 0
    rw [hk] at hn
    have hn' : ((G.neighborFinset l).filter (fun c => P.kind c = 0)).Nonempty :=
      Finset.card_pos.mp (by simpa [counts] using hn.ge)
    obtain ⟨c,hc⟩ := hn'
    obtain ⟨hlc,hk⟩ := Finset.mem_filter.mp hc
    refine ⟨c,hk,fun f hf => ⟨hne f (Finset.mem_inter.mp hf).1,l,hl,c,?_,
      Or.inr ((G.mem_neighborFinset _ _).mp hlc)⟩⟩
    exact (mem_incident G c f).mp (Finset.mem_inter.mp hf).2
  rw [P.outside_eq] at he
  rcases Finset.mem_union.mp he with he | he
  · rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact fromEndpoint u (by simp [hev]) hu
    · exact fromEndpoint v (by simp [hev]) hv
  · rcases (P.mem_edgesOf hev).mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact fromLower u (by simp [hev]) hu
    · exact fromLower v (by simp [hev]) hv

/-- The union of the two selected colour classes is precisely C--L.
This also records that every C--L edge is coloured. -/
def PairClasses {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F) (a b : Colour) : Prop :=
  ∀ e, (e ∈ F ∧ φ.colour e ∈ ({a,b} : Finset Colour)) ↔ e ∈ P.edgesOf 0 1

theorem PairClasses.sameYClasses {F F' : Finset G.edgeSet}
    {φ : PartialColouring (L2 G) F} {ψ : PartialColouring (L2 G) F'} {a b : Colour}
    (hc : P.PairClasses φ a b) (hs : φ.SameYClasses ψ {a,b}) : P.PairClasses ψ a b := by
  intro e
  constructor
  · rintro ⟨he,hy⟩
    obtain ⟨he',hcol⟩ := (hs (ψ.colour e) hy e).mpr ⟨he,rfl⟩
    exact (hc e).mp ⟨he',hcol.symm ▸ hy⟩
  · intro he
    obtain ⟨he',hy⟩ := (hc e).mpr he
    obtain ⟨he'',hcol⟩ := (hs (φ.colour e) hy e).mp ⟨he',rfl⟩
    exact ⟨he'',hcol.symm ▸ hy⟩

theorem PairClasses.holeMove {F : Finset G.edgeSet} {φ : PartialColouring (L2 G) F}
    {a b p : Colour} {h f : G.edgeSet} (hc : P.PairClasses φ a b)
    (hh : h ∉ F) (hs : φ.Single h p f) (hp : p ∉ ({a,b} : Finset Colour)) :
    P.PairClasses (φ.holeMove hs) a b := by
  have hi : (fun a b : G.edgeSet => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  have hm := PairClasses.sameYClasses P hc (φ.holeMove_sameYClasses hh hs hp)
  rw [hi] at hm
  exact hm

theorem PairClasses.swap {F : Finset G.edgeSet} {φ : PartialColouring (L2 G) F}
    {a b : Colour} (hc : P.PairClasses φ a b) {S : Set G.edgeSet}
    (hS : φ.KempeClosed a b S) : P.PairClasses (φ.swap a b S hS) a b := by
  intro e
  rw [← hc e]
  simp only [PartialColouring.swap,PartialColouring.swapColour]
  by_cases he : e ∈ S
  · simp only [ite_eq_left he,Finset.mem_insert,Finset.mem_singleton,Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left,Equiv.swap_apply_right]
    tauto
  · simp [he]

theorem outside_direct {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {a b : Colour} (hab : a ≠ b) (hc : P.PairClasses φ a b)
    {e : G.edgeSet} (he : e ∈ P.outside) : φ.DirectAt e a b := by
  obtain ⟨c,hk,hsee⟩ := P.outside_centre he
  have hcard : (P.edgesOf 0 1 ∩ incident G c).card = 2 := by
    simpa [incidenceCount,hk,weight] using P.cl_incidence c
  obtain ⟨f,g,hfg,hset⟩ := Finset.card_eq_two.mp hcard
  have hf : f ∈ P.edgesOf 0 1 ∩ incident G c := by rw [hset]; simp
  have hg : g ∈ P.edgesOf 0 1 ∩ incident G c := by rw [hset]; simp
  have hfg' : (L2 G).Adj f g := ⟨hfg,c,(mem_incident G c f).mp (Finset.mem_inter.mp hf).2,
    c,(mem_incident G c g).mp (Finset.mem_inter.mp hg).2,Or.inl rfl⟩
  obtain ⟨hfF,hfc⟩ := (hc f).mpr (Finset.mem_inter.mp hf).1
  obtain ⟨hgF,hgc⟩ := (hc g).mpr (Finset.mem_inter.mp hg).1
  have hcol := φ.proper hfF hgF hfg'
  simp only [Finset.mem_insert,Finset.mem_singleton] at hfc hgc
  rcases hfc with hfa | hfb <;> rcases hgc with hga | hgb
  · exact (hcol (hfa.trans hga.symm)).elim
  · exact ⟨f,g,⟨hfF,hsee f hf,hfa⟩,⟨hgF,hsee g hg,hgb⟩,hfg'⟩
  · exact ⟨g,f,⟨hgF,hsee g hg,hga⟩,⟨hfF,hsee f hf,hfb⟩,hfg'.symm⟩
  · exact (hcol (hfb.trans hgb.symm)).elim

theorem outside_tangled {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {a b : Colour} (hab : a ≠ b) (hc : P.PairClasses φ a b)
    {e : G.edgeSet} (he : e ∈ P.outside) : φ.AllTangled {a,b} e := by
  obtain ⟨f,g,hf,hg,hfg⟩ := P.outside_direct φ hab hc he
  intro x hx y hy hxy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · exact φ.directAt_tangled ⟨f,g,hf,hg,hfg⟩
  · exact φ.directAt_tangled ⟨g,f,hg,hf,hfg.symm⟩
  · exact (hxy rfl).elim

/-- This invariant rules out filling with a or b, or separating that pair,
after any sequence of the two operations whose preservation is proved above. -/
theorem uncoloured_pair_blocked {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    {a b : Colour} (hab : a ≠ b) (hc : P.PairClasses φ a b)
    {e : G.edgeSet} (he : e ∉ F) :
    ¬ φ.Free e a ∧ ¬ φ.Free e b ∧ ¬ φ.Separable e a b := by
  have hout : e ∈ P.outside := Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _,fun hm => he ((hc e).mpr hm).1⟩
  obtain ⟨f,g,hf,hg,hfg⟩ := P.outside_direct φ hab hc hout
  exact ⟨fun h => h ⟨f,hf⟩,fun h => h ⟨g,hg⟩,
    (φ.tangledAt_iff_not_separable e a b).mp (φ.directAt_tangled ⟨f,g,hf,hg,hfg⟩)⟩
variable {h : G.edgeSet} (φ : PartialColouring (L2 G) (Finset.univ.erase h))
  {a b : Colour} (hab : a ≠ b) (hc : P.PairClasses φ a b)

include φ hc in
theorem hole_outside : h ∈ P.outside := by
  simp only [outside,Finset.mem_sdiff,Finset.mem_univ,true_and]
  intro he
  exact Finset.notMem_erase h Finset.univ ((hc h).mpr he).1

include hab hc in
theorem pair_S_eq : φ.colourSetS h {a,b} = P.outside := by
  ext e
  have hi : (fun a b : G.edgeSet => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  have hD : insert h (Finset.univ.erase h) = (Finset.univ : Finset G.edgeSet) := by simp
  simp (config := { instances := true }) only
    [colourSetS,hi,hD,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hne,_⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun he => hne ((hc e).mpr he).1 ((hc e).mpr he).2⟩
  · intro he
    refine ⟨fun heF hcol => (Finset.mem_sdiff.mp he).2 ((hc e).mp ⟨heF,hcol⟩),?_⟩
    exact P.outside_tangled φ hab hc he

include hc in
theorem pair_yNeighbours (e : G.edgeSet) :
    φ.yNeighbours {a,b} e = (P.edgesOf 0 1).filter ((L2 G).Adj e) := by
  ext f
  simp only [yNeighbours,Finset.mem_filter]
  have := hc f
  tauto

include P in
theorem full_domain_degree (hg : 7 ≤ G.egirth) (e : G.edgeSet) :
    (domainNeighbours (L2 G) (insert h (Finset.univ.erase h)) e).card = 24 := by
  have he : domainNeighbours (L2 G) (insert h (Finset.univ.erase h)) e = conflicts G e := by
    ext f; simp [domainNeighbours]
  rw [he,regular_girth_conflicts_card G P.degree hg]

include hab hc in
theorem cu_core_numbers (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 0 2) :
    (φ.yNeighbours {a,b} e).card = 5 ∧
      (domainNeighbours (L2 G) P.outside e).card = 19 ∧
      φ.colourSetThreshold h {a,b} e = 17 := by
  have hy : (φ.yNeighbours {a,b} e).card = 5 := by
    rw [P.pair_yNeighbours φ hc]
    exact P.cl_conflicts_cu hg he
  have ho := P.outside_degree hg e
  rw [P.cl_conflicts_cu hg he] at ho
  have hd := P.full_domain_degree (h := h) hg e
  refine ⟨hy,by simpa only [domainNeighbours] using (show (P.outside.filter ((L2 G).Adj e)).card = 19 by omega),?_⟩
  rw [φ.twoColour_threshold h e hab,hy]
  have hi : (fun a b : G.edgeSet => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simp (config := { instances := true }) only [hi]
  rw [hd]
  norm_num

include hab hc in
theorem lu_core_numbers (hg : 7 ≤ G.egirth) {e : G.edgeSet} (he : e ∈ P.edgesOf 1 2) :
    (φ.yNeighbours {a,b} e).card = 6 ∧
      (domainNeighbours (L2 G) P.outside e).card = 18 ∧
      φ.colourSetThreshold h {a,b} e = 18 := by
  have hy : (φ.yNeighbours {a,b} e).card = 6 := by
    rw [P.pair_yNeighbours φ hc]
    exact P.cl_conflicts_lu hg he
  have ho := P.outside_degree hg e
  rw [P.cl_conflicts_lu hg he] at ho
  have hd := P.full_domain_degree (h := h) hg e
  refine ⟨hy,by simpa only [domainNeighbours] using (show (P.outside.filter ((L2 G).Adj e)).card = 18 by omega),?_⟩
  rw [φ.twoColour_threshold h e hab,hy]
  have hi : (fun a b : G.edgeSet => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simp (config := { instances := true }) only [hi]
  rw [hd]
  norm_num

include hab hc in
/-- P6's core computation, for the actual L² graph and actual two-colour classes. -/
theorem pair_core_eq (hg : 7 ≤ G.egirth) : φ.colourSetCore h {a,b} = P.outside := by
  apply Finset.Subset.antisymm
  · exact (φ.colourSetCore_isCore h {a,b}).1.trans (P.pair_S_eq φ hab hc).subset
  · apply φ.colourSetCore_greatest
    refine ⟨(P.pair_S_eq φ hab hc).symm.subset,?_⟩
    intro e he
    rw [P.outside_eq] at he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨_,hd,ht⟩ := P.cu_core_numbers φ hab hc hg he
      rw [hd,ht]; norm_num
    · obtain ⟨_,hd,ht⟩ := P.lu_core_numbers φ hab hc hg he
      rw [hd,ht]; norm_num

include hab hc in
theorem hole_in_pair_core (hg : 7 ≤ G.egirth) : h ∈ φ.colourSetCore h {a,b} := by
  rw [P.pair_core_eq φ hab hc hg]
  exact P.hole_outside φ hc

end Se20Insertion.P6.Pattern
