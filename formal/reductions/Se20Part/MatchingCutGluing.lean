import Se20Part.MatchingCutGeometry
import Se20Part.SmallCutPalette
import Se20Part.CutSideColouring

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance matchingCutGluingDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Gluing across a matching cut of size at most five, with both side colourings
kept up to a single palette permutation on the second side. -/
theorem matching_cut_gluing (hΔ : MaxDegreeFour G) (n : ℕ) (hn : n ≤ 5)
    (C : MatchingCut G (Fin n))
    (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (ψ : PartialColouring (L2 G) (sideEdges G (Finset.univ \ C.side))) :
    ∃ (θ : (L2 G).Coloring Colour) (p : Colour ≃ Colour),
      (∀ e ∈ sideEdges G C.side, θ e = φ.colour e) ∧
      ∀ e ∈ sideEdges G (Finset.univ \ C.side), θ e = p (ψ.colour e) := by
  let S := fun i => (sideStar G C.swap.side (C.right i)).image ψ.colour
  let T := fun i => (sideStar G C.side (C.left i)).image φ.colour
  let L := fun i => Finset.univ \ (sideNear G C.swap.side (C.right i)).image ψ.colour
  let K := fun i => Finset.univ \ (sideNear G C.side (C.left i)).image φ.colour
  have hS : ∀ i, (S i).card ≤ 3 := fun i =>
    Finset.card_image_le.trans (C.swap.endpoint_counts hΔ i).1
  have hT : ∀ i, (T i).card ≤ 3 := fun i =>
    Finset.card_image_le.trans (C.endpoint_counts hΔ i).1
  have hL : ∀ i, 8 ≤ (L i).card := by
    intro i
    have h := Finset.card_image_le (s := sideNear G C.swap.side (C.right i)) (f := ψ.colour)
    have hc : (sideNear G C.swap.side (C.right i)).card ≤ 12 := by
      simpa only [MatchingCut.swap] using (C.swap.endpoint_counts hΔ i).2
    dsimp [L]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    norm_num
    omega
  have hK : ∀ i, 8 ≤ (K i).card := by
    intro i
    have h := Finset.card_image_le (s := sideNear G C.side (C.left i)) (f := φ.colour)
    have hc := (C.endpoint_counts hΔ i).2
    dsimp [K]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    norm_num
    omega
  have hdisS : ∀ i, Disjoint (L i) (S i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro c hc hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr
      ⟨e,sideStar_subset_near G _ _ he,rfl⟩)
  have hdisT : ∀ i, Disjoint (K i) (T i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro c hc hs
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr
      ⟨e,sideStar_subset_near G _ _ he,rfl⟩)
  have hpalette : ∃ (p : Colour ≃ Colour) (x y : Fin n → Colour),
      Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ p (x i) = y i) ∧
      ∀ c, ¬ starForbidden S T c (p c) := by
    by_cases he : n = 5
    · subst n
      exact matching_cut_five_palette rfl S T L K hS hT hL hK hdisS hdisT
    · exact matching_cut_small_palette rfl n (by omega) S T L K hS hT hL hK hdisS
  obtain ⟨p,x,y,hx,hy,hmem,hp⟩ := hpalette
  have hcross : ∀ e ∈ sideEdges G C.side, ∀ f ∈ sideEdges G C.swap.side,
      (L2 G).Adj e f → φ.colour e ≠ p (ψ.colour f) := by
    intro e he f hf hef heq
    obtain ⟨u,hu,v,hv,huv⟩ := (cut_cross_conflict_iff G C.side he hf).mp hef
    have huA := (mem_sideEdges G _ _).mp he u hu
    have hvB := (Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp hf v hv)).2
    obtain ⟨i,hi,hj⟩ := C.complete u huA v hvB huv
    apply hp (ψ.colour f)
    refine ⟨i,Finset.mem_image.mpr ⟨f,?_,rfl⟩,?_⟩
    · exact Finset.mem_inter.mpr ⟨(mem_incident G _ _).mpr (hj.symm ▸ hv),hf⟩
    · rw [← heq]
      exact Finset.mem_image.mpr ⟨e,Finset.mem_inter.mpr
        ⟨(mem_incident G _ _).mpr (hi.symm ▸ hu),he⟩,rfl⟩
  have hnewA : ∀ i e, e ∈ sideEdges G C.side → (L2 G).Adj (C.edge i) e → y i ≠ φ.colour e := by
    intro i e he hie heq
    apply (Finset.mem_sdiff.mp (hmem i).2.1).2
    exact Finset.mem_image.mpr ⟨e,C.cut_conflict_near i he hie,heq.symm⟩
  have hnewB : ∀ i e, e ∈ sideEdges G C.swap.side → (L2 G).Adj (C.edge i) e → y i ≠ p (ψ.colour e) := by
    intro i e he hie heq
    apply (Finset.mem_sdiff.mp (hmem i).1).2
    have hc : e ∈ sideNear G C.swap.side (C.right i) := C.swap.cut_conflict_near i he
      (by simpa only [MatchingCut.swap_edge] using hie)
    exact Finset.mem_image.mpr ⟨e,hc,p.injective ((hmem i).2.2.trans heq) |>.symm⟩
  let c : G.edgeSet → Colour := fun e => if e ∈ sideEdges G C.side then φ.colour e
    else if e ∈ sideEdges G C.swap.side then p (ψ.colour e)
    else if he : ∃ i, C.edge i = e then y he.choose else 0
  have hcA : ∀ e ∈ sideEdges G C.side, c e = φ.colour e := fun e he => if_pos he
  have hcB : ∀ e ∈ sideEdges G C.swap.side, c e = p (ψ.colour e) := by
    intro e he
    have hn := fun h => Finset.disjoint_left.mp C.side_disjoint h he
    simp only [c,if_neg hn,if_pos he]
  have hcE : ∀ i, c (C.edge i) = y i := by
    intro i
    have he : ∃ j, C.edge j = C.edge i := ⟨i,rfl⟩
    have hnB : C.edge i ∉ sideEdges G C.swap.side := by
      simpa only [MatchingCut.swap] using C.edge_not_other_side i
    simp only [c,if_neg (C.edge_not_side i),if_neg hnB,
      dif_pos he,C.edge_injective he.choose_spec]
  have hproper : ∀ e f, (L2 G).Adj e f → c e ≠ c f := by
    intro e f hef
    rcases C.edge_cases e with he | he | ⟨i,rfl⟩ <;>
      rcases C.edge_cases f with hf | hf | ⟨j,rfl⟩
    · rw [hcA e he,hcA f hf]; exact φ.proper he hf hef
    · rw [hcA e he,hcB f hf]; exact hcross e he f hf hef
    · rw [hcA e he,hcE j]; exact (hnewA j e he hef.symm).symm
    · rw [hcB e he,hcA f hf]; exact (hcross f hf e he hef.symm).symm
    · rw [hcB e he,hcB f hf]; exact fun h => ψ.proper he hf hef (p.injective h)
    · rw [hcB e he,hcE j]; exact (hnewB j e he hef.symm).symm
    · rw [hcE i,hcA f hf]; exact hnewA i f hf hef
    · rw [hcE i,hcB f hf]; exact hnewB i f hf hef
    · rw [hcE i,hcE j]; exact fun h => hef.ne (congrArg C.edge (hy h))
  exact ⟨SimpleGraph.Coloring.mk c (fun {e f} h => hproper e f h),p,hcA,hcB⟩

/-- The original five-cut interface, as a specialization of the construction. -/
theorem matching_five_cut_gluing (hΔ : MaxDegreeFour G) (C : MatchingCut G (Fin 5))
    (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (ψ : PartialColouring (L2 G) (sideEdges G (Finset.univ \ C.side))) :
    ∃ (θ : (L2 G).Coloring Colour) (p : Colour ≃ Colour),
      (∀ e ∈ sideEdges G C.side, θ e = φ.colour e) ∧
      ∀ e ∈ sideEdges G (Finset.univ \ C.side), θ e = p (ψ.colour e) :=
  matching_cut_gluing G hΔ 5 (by decide) C φ ψ

/-- The source theorem's induced-side hypotheses suffice, including size zero. -/
theorem matching_cut_strongColourable (hΔ : MaxDegreeFour G) (n : ℕ) (hn : n ≤ 5)
    (C : MatchingCut G (Fin n))
    (hA : StrongColourable (G.induce (C.side : Set V)) 20)
    (hB : StrongColourable (G.induce ((Finset.univ \ C.side : Finset V) : Set V)) 20) :
    StrongColourable G 20 := by
  obtain ⟨φ⟩ := (side_colourable_iff G C.side).mp hA
  obtain ⟨ψ⟩ := (side_colourable_iff G (Finset.univ \ C.side)).mp hB
  obtain ⟨θ,_⟩ := matching_cut_gluing G hΔ n hn C φ ψ
  exact ⟨θ⟩

end Se20Part
