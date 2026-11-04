import Se20Fractional.TheoremF

/-! Partial work on the finite reduction for Proposition D.
This file is deliberately outside the default library import graph. -/
namespace Se20Fractional.DReduction
open Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def endpoints (Q : Finset G.edgeSet) : Finset V :=
  Q.biUnion (fun e => e.val.toFinset)

@[simp] theorem mem_endpoints (Q : Finset G.edgeSet) (v : V) :
    v ∈ endpoints Q ↔ ∃ e ∈ Q, v ∈ e.val := by
  simp [endpoints, Sym2.mem_toFinset]

noncomputable def closedRegion (G : SimpleGraph V) (a b : V) : Finset V :=
  insert a (insert b (endpointRegion G a b))

theorem closedRegion_card_le (hΔ : ∀ v, G.degree v ≤ 4) {a b : V} (hab : G.Adj a b) :
    (closedRegion G a b).card ≤ 8 := by
  have hr := endpointRegion_card G a b hab
  have ha := hΔ a
  have hb := hΔ b
  have hc : (closedRegion G a b).card ≤ (endpointRegion G a b).card + 2 := by
    unfold closedRegion
    have h₁ := Finset.card_insert_le a (insert b (endpointRegion G a b))
    have h₂ := Finset.card_insert_le b (endpointRegion G a b)
    omega
  omega

theorem outside_edge_card_le_one {a b : V} (hab : G.Adj a b) (e : G.edgeSet)
    (hconflict : (L2 G).Adj ⟨s(a,b),hab⟩ e) :
    (e.val.toFinset \ closedRegion G a b).card ≤ 1 := by
  obtain ⟨w, hwe, hwR⟩ := (l2_adj_region G a b hab e).mp hconflict
  have hwW : w ∈ closedRegion G a b := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem hwR)
  have hne : (e.val.toFinset ∩ closedRegion G a b).Nonempty :=
    ⟨w, Finset.mem_inter.mpr ⟨Sym2.mem_toFinset.mpr hwe, hwW⟩⟩
  have hc := Finset.card_sdiff_add_card_inter e.val.toFinset (closedRegion G a b)
  have htwo : e.val.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag _
    (G.not_isDiag_of_mem_edgeSet e.property)
  have hp := Finset.card_pos.mpr hne
  omega

/-- All endpoints of a clique of m edges lie in at most m+7 vertices. -/
theorem endpoint_bound (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hQne : Q.Nonempty) : (endpoints Q).card ≤ Q.card + 7 := by
  obtain ⟨z, hzQ⟩ := hQne
  rcases z with ⟨z,hzG⟩
  induction z using Sym2.ind with
  | _ a b =>
    let z : G.edgeSet := ⟨s(a,b),hzG⟩
    let W := closedRegion G a b
    have hW : W.card ≤ 8 := closedRegion_card_le hΔ hzG
    have hOut : endpoints Q \ W =
        (Q.erase z).biUnion (fun e => e.val.toFinset \ W) := by
      ext w
      simp only [Finset.mem_sdiff, mem_endpoints, Finset.mem_biUnion,
        Finset.mem_erase, Sym2.mem_toFinset]
      constructor
      · rintro ⟨⟨e, heQ, hwe⟩, hwW⟩
        refine ⟨e, ⟨?_, heQ⟩, hwe, hwW⟩
        intro hez
        subst e
        have hwab : w = a ∨ w = b := Sym2.mem_iff.mp hwe
        rcases hwab with rfl | rfl <;> simp [W, closedRegion] at hwW
      · rintro ⟨e, ⟨_, heQ⟩, hwe, hwW⟩
        exact ⟨⟨e, heQ, hwe⟩, hwW⟩
    have hOutside : (endpoints Q \ W).card ≤ (Q.erase z).card := by
      rw [hOut]
      calc
        _ ≤ ∑ e ∈ Q.erase z, (e.val.toFinset \ W).card := Finset.card_biUnion_le
        _ ≤ ∑ _e ∈ Q.erase z, 1 := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨hez, heQ⟩ := Finset.mem_erase.mp he
          exact outside_edge_card_le_one hzG e (hQ z hzQ e heQ hez.symm)
        _ = _ := by simp
    have hpart := Finset.card_sdiff_add_card_inter (endpoints Q) W
    have hinter := Finset.card_le_card (Finset.inter_subset_right : endpoints Q ∩ W ⊆ W)
    have herase := Finset.card_erase_add_one (a := z) hzQ
    omega

theorem endpoint_bound_23 (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (h16 : Q.card = 16) : (endpoints Q).card ≤ 23 := by
  have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have h := endpoint_bound hΔ Q hQ hne
  omega

/-- A counterexample to D contains an exact 16-edge clique with the necessary
local inequalities, and its endpoint support has size at most 23. -/
theorem obstruction_of_not_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : ¬ PropositionD G) :
    ∃ Q : Finset G.edgeSet, Q.card = 16 ∧ Clique (L2 G) Q ∧ (endpoints Q).card ≤ 23 ∧
      ∀ a b : V, ∀ hab : G.Adj a b, (⟨s(a,b),hab⟩ : G.edgeSet) ∈ Q →
        4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card ≤ 4 := by
  have hbad : ∃ R : Finset G.edgeSet, Clique (L2 G) R ∧ 16 ≤ R.card ∧
      ∀ y ∈ R, 20 ≤ degreeOn (L2 G) univ y := by
    unfold PropositionD at hD
    push_neg at hD
    obtain ⟨R, hR, h16, hd⟩ := hD
    exact ⟨R, hR, h16, fun y hy => by have := hd y hy; omega⟩
  obtain ⟨R, hR, h16, hd⟩ := hbad
  obtain ⟨Q, hQR, hQcard⟩ := Finset.exists_subset_card_eq h16
  have hQ : Clique (L2 G) Q := fun a ha b hb hab => hR a (hQR ha) b (hQR hb) hab
  refine ⟨Q, hQcard, hQ, endpoint_bound_23 hΔ Q hQ hQcard, ?_⟩
  intro a b hab he
  have hlo := hd ⟨s(a,b),hab⟩ (hQR he)
  have hhi := degree_formula_bound G hΔ a b hab
  omega

#print axioms endpoint_bound_23
#print axioms obstruction_of_not_D

section Embeddings
variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}

theorem embedding_degree_le (f : G ↪g H) (v : V) : G.degree v ≤ H.degree (f v) := by
  have h := Fintype.card_le_of_embedding (f.mapNeighborSet v)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using h

/-- Induced embeddings preserve and reflect the line-square conflict relation. -/
theorem l2_embedding_iff (f : G ↪g H) (e g : G.edgeSet) :
    (L2 H).Adj (f.mapEdgeSet e) (f.mapEdgeSet g) ↔ (L2 G).Adj e g := by
  change (_ ≠ _ ∧ ∃ a ∈ Sym2.map f e.val, ∃ b ∈ Sym2.map f g.val, a = b ∨ H.Adj a b) ↔ _
  constructor
  · rintro ⟨hne, a, ha, b, hb, hab⟩
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hb
    refine ⟨fun h => hne (congrArg f.mapEdgeSet h), x, hx, y, hy, ?_⟩
    exact hab.elim (fun h => Or.inl (f.injective h)) (fun h => Or.inr (f.map_adj_iff.mp h))
  · rintro ⟨hne, a, ha, b, hb, hab⟩
    refine ⟨fun h => hne (f.mapEdgeSet.injective h), f a, Sym2.mem_map.mpr ⟨a,ha,rfl⟩,
      f b, Sym2.mem_map.mpr ⟨b,hb,rfl⟩, ?_⟩
    exact hab.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (f.map_adj_iff.mpr h))

theorem embedding_region (f : G ↪g H) {a b u : V} (hu : u ∈ endpointRegion G a b) :
    f u ∈ endpointRegion H (f a) (f b) := by
  obtain ⟨huN, hua, hub⟩ := (mem_endpointRegion G a b u).mp hu
  refine (mem_endpointRegion H _ _ _).mpr ⟨?_, fun h => hua (f.injective h),
    fun h => hub (f.injective h)⟩
  exact huN.elim (fun h => Or.inl (f.map_adj_iff.mpr h)) (fun h => Or.inr (f.map_adj_iff.mpr h))

theorem embedding_common_le (f : G ↪g H) (a b : V) :
    commonCount G a b ≤ commonCount H (f a) (f b) := by
  apply Finset.card_le_card_of_injOn f
  · intro u hu
    change u ∈ G.neighborFinset a ∩ G.neighborFinset b at hu
    change f u ∈ H.neighborFinset (f a) ∩ H.neighborFinset (f b)
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu ⊢
    exact ⟨f.map_adj_iff.mpr hu.1, f.map_adj_iff.mpr hu.2⟩
  · exact fun _ _ _ _ h => f.injective h

theorem embedding_internal_le (f : G ↪g H) (a b : V) :
    (internalEdges G (endpointRegion G a b)).card ≤
      (internalEdges H (endpointRegion H (f a) (f b))).card := by
  apply Finset.card_le_card_of_injOn (Sym2.map f)
  · intro e he
    change Sym2.map f e ∈ internalEdges H (endpointRegion H (f a) (f b))
    obtain ⟨heG, heR⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨H.mem_edgeFinset.mpr
      (f.map_mem_edgeSet_iff.mpr (G.mem_edgeFinset.mp heG)), ?_⟩
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hw
    exact embedding_region f (heR u hu)
  · intro e he g hg h
    exact f.toEmbedding.sym2Map.injective h

theorem embedding_local_le (f : G ↪g H) (a b : V) :
    4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card ≤
      4 * commonCount H (f a) (f b) +
        (internalEdges H (endpointRegion H (f a) (f b))).card := by
  have ht := embedding_common_le f a b
  have he := embedding_internal_le f a b
  omega

/-- Padding a graph by isolated vertices preserves its neighbourhood finsets. -/
theorem neighborFinset_map (f : V ↪ W) (a : V) :
    (G.map f).neighborFinset (f a) = (G.neighborFinset a).map f := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.map_adj, Finset.mem_map]
  constructor
  · rintro ⟨x,y,hxy,hxa,hyw⟩
    have hxa' := f.injective hxa
    subst x
    exact ⟨y, hxy, hyw⟩
  · rintro ⟨y,hy,hyw⟩
    exact ⟨a,y,hy,rfl,hyw⟩

theorem region_map (f : V ↪ W) (a b : V) :
    endpointRegion (G.map f) (f a) (f b) = (endpointRegion G a b).map f := by
  let j := SimpleGraph.Embedding.map f G
  ext w
  constructor
  · intro hw
    obtain ⟨hN,hwa,hwb⟩ := (mem_endpointRegion (G.map f) (f a) (f b) w).mp hw
    have hwf : ∃ u, f u = w := by
      rcases hN with hN | hN
      all_goals obtain ⟨x,u,_,_,hu⟩ := (G.map_adj f _ _).mp hN; exact ⟨u,hu⟩
    obtain ⟨u,rfl⟩ := hwf
    refine Finset.mem_map.mpr ⟨u, ?_, rfl⟩
    apply (mem_endpointRegion G a b u).mpr
    exact ⟨hN.elim (fun h => Or.inl (j.map_adj_iff.mp h))
      (fun h => Or.inr (j.map_adj_iff.mp h)),
      fun h => hwa (congrArg f h), fun h => hwb (congrArg f h)⟩
  · rintro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
    exact embedding_region j hu

theorem common_map (f : V ↪ W) (a b : V) :
    commonCount (G.map f) (f a) (f b) = commonCount G a b := by
  letI : DecidableRel (G.map f).Adj := fun a b => Classical.propDecidable _
  unfold commonCount
  have heq : (G.map f).neighborFinset (f a) ∩ (G.map f).neighborFinset (f b) =
      (G.neighborFinset a ∩ G.neighborFinset b).map f := by
    let j := SimpleGraph.Embedding.map f G
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_map]
    constructor
    · rintro ⟨hA,hB⟩
      obtain ⟨x,u,hxu,hxa,huw⟩ := (G.map_adj f _ _).mp hA
      have hxa' := f.injective hxa
      subst x
      subst w
      exact ⟨u,⟨hxu,j.map_adj_iff.mp hB⟩,rfl⟩
    · rintro ⟨u,⟨hua,hub⟩,rfl⟩
      exact ⟨j.map_adj_iff.mpr hua,j.map_adj_iff.mpr hub⟩
  calc
    _ = ((G.neighborFinset a ∩ G.neighborFinset b).map f).card := congrArg Finset.card heq
    _ = _ := Finset.card_map _

theorem internal_map (f : V ↪ W) (R : Finset V) :
    (internalEdges (G.map f) (R.map f)).card = (internalEdges G R).card := by
  have heq : internalEdges (G.map f) (R.map f) = (internalEdges G R).map f.sym2Map := by
    ext e
    simp only [internalEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      G.edgeSet_map f, Set.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨⟨g,hg,rfl⟩,hR⟩
      refine ⟨g, ⟨hg, ?_⟩, rfl⟩
      intro u hu
      have hfu : f u ∈ Sym2.map f g := Sym2.mem_map.mpr ⟨u,hu,rfl⟩
      obtain ⟨x,hx,hxu⟩ := hR (f u) hfu
      exact f.injective hxu ▸ hx
    · rintro ⟨g,⟨hg,hR⟩,rfl⟩
      refine ⟨⟨g,hg,rfl⟩, ?_⟩
      intro w hw
      obtain ⟨u,hu,rfl⟩ := Sym2.mem_map.mp hw
      exact ⟨u,hR u hu,rfl⟩
  rw [heq, Finset.card_map]

theorem local_map (f : V ↪ W) (a b : V) :
    4 * commonCount (G.map f) (f a) (f b) +
      (internalEdges (G.map f) (endpointRegion (G.map f) (f a) (f b))).card =
      4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card := by
  rw [common_map, region_map, internal_map]

theorem degree_map_le_four (f : V ↪ W) (hΔ : ∀ v, G.degree v ≤ 4) :
    ∀ w, (G.map f).degree w ≤ 4 := by
  intro w
  by_cases hw : w ∈ Set.range f
  · obtain ⟨v,rfl⟩ := hw
    rw [G.degree_map_apply]
    exact hΔ v
  · have hn : (G.map f).neighborFinset w = ∅ := by
      ext u
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      intro h
      obtain ⟨a,b,_,ha,_⟩ := (G.map_adj f w u).mp h
      exact hw ⟨a,ha⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
    norm_num

end Embeddings

def LocallyLow (G : SimpleGraph V) (Q : Finset G.edgeSet) : Prop :=
  ∀ a b : V, ∀ hab : G.Adj a b, (⟨s(a,b),hab⟩ : G.edgeSet) ∈ Q →
    4 * commonCount G a b + (internalEdges G (endpointRegion G a b)).card ≤ 4

theorem clique_degree_lower (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q)
    (e : G.edgeSet) (he : e ∈ Q) : Q.card - 1 ≤ degreeOn (L2 G) univ e := by
  have hs : Q.erase e ⊆ neighbors (L2 G) univ e := by
    intro f hf
    obtain ⟨hne, hfQ⟩ := Finset.mem_erase.mp hf
    exact (mem_neighbors _ _ _ _).mpr ⟨Finset.mem_univ _, hQ e he f hfQ hne.symm⟩
  have h := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem he] at h
  exact h

/-- The six numerical root cases used by the existing independent encoder.
This proves the case elimination, but does not assume or prove a labelled
root-neighbour pattern or the encoder's lexicographic symmetry conditions. -/
theorem root_degree_cases (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (h16 : Q.card = 16) (hLow : LocallyLow G Q)
    (a b : V) (hab : G.Adj a b) (he : (⟨s(a,b),hab⟩ : G.edgeSet) ∈ Q)
    (horder : G.degree a ≤ G.degree b) :
    (G.degree a = 2 ∧ G.degree b = 4 ∧ commonCount G a b = 0) ∨
    (G.degree a = 3 ∧ G.degree b = 3 ∧ commonCount G a b = 0) ∨
    (G.degree a = 3 ∧ G.degree b = 4 ∧ commonCount G a b = 0) ∨
    (G.degree a = 3 ∧ G.degree b = 4 ∧ commonCount G a b = 1) ∨
    (G.degree a = 4 ∧ G.degree b = 4 ∧ commonCount G a b = 0) ∨
    (G.degree a = 4 ∧ G.degree b = 4 ∧ commonCount G a b = 1) := by
  have hd := clique_degree_lower Q hQ ⟨s(a,b),hab⟩ he
  have hf := degree_formula G a b hab
  have hr := endpointRegion_card G a b hab
  have hsum : (∑ w ∈ endpointRegion G a b, G.degree w) ≤
      4 * (endpointRegion G a b).card := by
    calc
      _ ≤ ∑ _w ∈ endpointRegion G a b, 4 := Finset.sum_le_sum (fun w _ => hΔ w)
      _ = _ := by simp [Nat.mul_comm]
  have hl := hLow a b hab he
  have ha := hΔ a
  have hb := hΔ b
  omega

theorem induced_edge_lift (S : Finset V) (e : G.edgeSet)
    (he : ∀ v ∈ e.val, v ∈ S) :
    ∃ e' : (G.induce (S : Set V)).edgeSet,
      (SimpleGraph.Embedding.induce (G := G) (S : Set V)).mapEdgeSet e' = e := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.ind with
  | _ a b =>
    let a' : (S : Set V) := ⟨a, he a (by simp)⟩
    let b' : (S : Set V) := ⟨b, he b (by simp)⟩
    let e' : (G.induce (S : Set V)).edgeSet := ⟨s(a',b'), heG⟩
    exact ⟨e', rfl⟩

/-- Restriction to exactly V(Q), including preservation of all required data. -/
theorem induced_obstruction (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet)
    (hQ : Clique (L2 G) Q) (hLow : LocallyLow G Q) :
    ∃ R : (Finset (G.induce (endpoints Q : Set V)).edgeSet),
      R.card = Q.card ∧ Clique (L2 (G.induce (endpoints Q : Set V))) R ∧
      LocallyLow (G.induce (endpoints Q : Set V)) R ∧
      (∀ v, (G.induce (endpoints Q : Set V)).degree v ≤ 4) ∧
      (∀ v, v ∈ endpoints R) := by
  let S := endpoints Q
  let H := G.induce (S : Set V)
  let j : H ↪g G := SimpleGraph.Embedding.induce (S : Set V)
  let R : Finset H.edgeSet := univ.filter (fun e => j.mapEdgeSet e ∈ Q)
  have hlift (e : G.edgeSet) (he : e ∈ Q) : ∃ e' : H.edgeSet, j.mapEdgeSet e' = e :=
    induced_edge_lift S e (fun v hv => (mem_endpoints Q v).mpr ⟨e,he,hv⟩)
  have hR (e : H.edgeSet) : e ∈ R ↔ j.mapEdgeSet e ∈ Q := by simp [R]
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.card_bij (fun e _ => j.mapEdgeSet e)
    · exact fun e he => (hR e).mp he
    · exact fun e he f hf h => j.mapEdgeSet.injective h
    · intro e he
      obtain ⟨e',he'⟩ := hlift e he
      exact ⟨e', (hR e').mpr (he' ▸ he), he'⟩
  · intro e he f hf hne
    apply (l2_embedding_iff j e f).mp
    exact hQ _ ((hR e).mp he) _ ((hR f).mp hf)
      (fun h => hne (j.mapEdgeSet.injective h))
  · intro a b hab he
    have heQ := (hR ⟨s(a,b),hab⟩).mp he
    have hlo := hLow a.val b.val hab heQ
    exact (embedding_local_le j a b).trans hlo
  · intro v
    exact (embedding_degree_le j v).trans (hΔ v.val)
  · intro v
    obtain ⟨e,heQ,hve⟩ := (mem_endpoints Q v.val).mp v.property
    obtain ⟨e',he'⟩ := hlift e heQ
    have hmem : v.val ∈ Sym2.map j e'.val := by
      have hval := congrArg Subtype.val he'
      rw [← hval] at hve
      exact hve
    obtain ⟨u,hue,huv⟩ := Sym2.mem_map.mp hmem
    have huv' : u = v := Subtype.ext huv
    subst u
    exact (mem_endpoints R v).mpr ⟨e', (hR e').mpr (he' ▸ heQ), hue⟩

/-- The finite graph statement still requiring certification. It has no symmetry
breaking: unused vertices are isolated, and every selected edge is an actual edge. -/
def Obstruction23 (H : SimpleGraph (Fin 23)) (Q : Finset H.edgeSet) : Prop :=
  (∀ v, H.degree v ≤ 4) ∧ Q.card = 16 ∧ Clique (L2 H) Q ∧ LocallyLow H Q ∧
    ∀ v, (∃ u, H.Adj v u) → v ∈ endpoints Q

theorem obstruction23_of_not_D (hΔ : ∀ v, G.degree v ≤ 4) (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 23), ∃ Q : Finset H.edgeSet, Obstruction23 H Q := by
  obtain ⟨Q,h16,hQ,h23,hLow⟩ := obstruction_of_not_D hΔ hD
  obtain ⟨R,hRcard,hRcl,hRlow,hRΔ,hRcover⟩ := induced_obstruction hΔ Q hQ hLow
  let S := endpoints Q
  let H := G.induce (S : Set V)
  have hc : Fintype.card (S : Set V) ≤ Fintype.card (Fin 23) := by
    change Fintype.card S ≤ Fintype.card (Fin 23)
    rw [Fintype.card_coe, Fintype.card_fin]
    exact h23
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  let j := SimpleGraph.Embedding.map f H
  let T := R.map j.mapEdgeSet
  refine ⟨H.map f, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using degree_map_le_four f hRΔ v
  · change (R.map j.mapEdgeSet).card = 16
    rw [Finset.card_map, hRcard, h16]
  · intro a ha b hb hab
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hb
    exact (l2_embedding_iff j e g).mpr (hRcl e he g hg
      (fun h => hab (congrArg j.mapEdgeSet h)))
  · intro a b hab he
    obtain ⟨x,y,hxy,hxa,hyb⟩ := (H.map_adj f a b).mp hab
    subst a; subst b
    obtain ⟨e,heR,heq⟩ := Finset.mem_map.mp he
    have heq' : e = (⟨s(x,y),hxy⟩ : H.edgeSet) := by
      apply j.mapEdgeSet.injective
      exact heq
    subst e
    rw [local_map f x y]
    exact hRlow x y hxy heR
  · intro v hv
    obtain ⟨w,hvw⟩ := hv
    obtain ⟨x,y,hxy,hxv,hyw⟩ := (H.map_adj f v w).mp hvw
    obtain ⟨e,heR,hxe⟩ := (mem_endpoints R x).mp (hRcover x)
    refine (mem_endpoints T v).mpr ⟨j.mapEdgeSet e, Finset.mem_map.mpr ⟨e,heR,rfl⟩, ?_⟩
    exact Sym2.mem_map.mpr ⟨x,hxe,hxv⟩

/-- This is a reduction theorem, not a proof of the finite premise. -/
theorem propositionD_of_no_obstruction23 (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 23), ∀ Q : Finset H.edgeSet, ¬ Obstruction23 H Q) :
    PropositionD G := by
  by_contra hD
  obtain ⟨H,Q,h⟩ := obstruction23_of_not_D hΔ hD
  exact hfinite H Q h

theorem obstruction23_map {H : SimpleGraph (Fin 23)} {Q : Finset H.edgeSet}
    (h : Obstruction23 H Q) (f : Fin 23 ↪ Fin 23) :
    Obstruction23 (H.map f) (Q.map (SimpleGraph.Embedding.map f H).mapEdgeSet) := by
  obtain ⟨hΔ,h16,hQ,hLow,hcover⟩ := h
  let j := SimpleGraph.Embedding.map f H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using degree_map_le_four f hΔ v
  · rw [Finset.card_map, h16]
  · intro a ha b hb hab
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hb
    exact (l2_embedding_iff j e g).mpr (hQ e he g hg
      (fun h => hab (congrArg j.mapEdgeSet h)))
  · intro a b hab he
    obtain ⟨x,y,hxy,hxa,hyb⟩ := (H.map_adj f a b).mp hab
    subst a; subst b
    obtain ⟨e,heQ,heq⟩ := Finset.mem_map.mp he
    have heq' : e = (⟨s(x,y),hxy⟩ : H.edgeSet) := j.mapEdgeSet.injective heq
    subst e
    rw [local_map f x y]
    exact hLow x y hxy heQ
  · intro v hv
    obtain ⟨w,hvw⟩ := hv
    obtain ⟨x,y,hxy,hxv,hyw⟩ := (H.map_adj f v w).mp hvw
    obtain ⟨e,heQ,hxe⟩ := (mem_endpoints Q x).mp (hcover x ⟨y,hxy⟩)
    refine (mem_endpoints _ v).mpr ⟨j.mapEdgeSet e, Finset.mem_map.mpr ⟨e,heQ,rfl⟩, ?_⟩
    exact Sym2.mem_map.mpr ⟨x,hxe,hxv⟩

/-- Only the root-edge symmetry, requiring no sorted adjacency matrix. -/
theorem exists_root_permutation (a b : Fin 23) (hab : a ≠ b) :
    ∃ f : Fin 23 ≃ Fin 23, f a = 0 ∧ f b = 1 := by
  let s := Equiv.swap a 0
  have hsa : s a = 0 := Equiv.swap_apply_left _ _
  have hsb : s b ≠ 0 := by
    intro h
    exact hab (s.injective (hsa.trans h.symm))
  let t := Equiv.swap (s b) 1
  refine ⟨s.trans t, ?_, ?_⟩
  · change t (s a) = 0
    rw [hsa]
    exact Equiv.swap_apply_of_ne_of_ne hsb.symm (by decide)
  · exact Equiv.swap_apply_left _ _

def RootObstruction23 (H : SimpleGraph (Fin 23)) (Q : Finset H.edgeSet) : Prop :=
  Obstruction23 H Q ∧ ∃ hab : H.Adj 0 1, (⟨s(0,1),hab⟩ : H.edgeSet) ∈ Q

theorem root_obstruction23_of_not_D (hΔ : ∀ v, G.degree v ≤ 4)
    (hD : ¬ PropositionD G) :
    ∃ H : SimpleGraph (Fin 23), ∃ Q : Finset H.edgeSet, RootObstruction23 H Q := by
  obtain ⟨H,Q,h⟩ := obstruction23_of_not_D hΔ hD
  have hnonempty : Q.Nonempty := Finset.card_pos.mp (by rw [h.2.1]; decide)
  obtain ⟨e,heQ⟩ := hnonempty
  rcases e with ⟨e,heH⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hab : H.Adj a b := heH
    obtain ⟨f,hfa,hfb⟩ := exists_root_permutation a b hab.ne
    let j := SimpleGraph.Embedding.map f.toEmbedding H
    let R := Q.map j.mapEdgeSet
    have hadj : (H.map f.toEmbedding).Adj 0 1 := by
      rw [← hfa, ← hfb]
      exact j.map_adj_iff.mpr hab
    refine ⟨H.map f.toEmbedding, R, obstruction23_map h f.toEmbedding, hadj, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨s(a,b),hab⟩, heQ, ?_⟩
    apply Subtype.ext
    change s(f a,f b) = s(0,1)
    rw [hfa,hfb]

theorem propositionD_of_no_root_obstruction23 (hΔ : ∀ v, G.degree v ≤ 4)
    (hfinite : ∀ H : SimpleGraph (Fin 23), ∀ Q : Finset H.edgeSet,
      ¬ RootObstruction23 H Q) : PropositionD G := by
  by_contra hD
  obtain ⟨H,Q,h⟩ := root_obstruction23_of_not_D hΔ hD
  exact hfinite H Q h

#print axioms l2_embedding_iff
#print axioms embedding_local_le
#print axioms local_map
#print axioms root_degree_cases
#print axioms induced_obstruction
#print axioms obstruction23_of_not_D
#print axioms propositionD_of_no_obstruction23
#print axioms root_obstruction23_of_not_D
#print axioms propositionD_of_no_root_obstruction23

end Se20Fractional.DReduction
