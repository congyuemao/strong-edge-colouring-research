import Se20Insertion.PatternVerification
import Se20Insertion.ShellCover

noncomputable section
open scoped Classical
namespace Se20Insertion.TreePattern

theorem sixteen_nonedge_card (S : Finset Position) (hS : S.card = 16) :
    66 ≤ ((graph.induce (S : Set Position))ᶜ).edgeFinset.card := by
  let N := graph.induce (S : Set Position)
  have hd : Disjoint N.edgeFinset Nᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hu : N.edgeFinset ∪ Nᶜ.edgeFinset = (⊤ : SimpleGraph S).edgeFinset := by
    ext p
    refine Sym2.inductionOn p ?_
    intro x y
    by_cases hxy : x = y <;> simp [hxy,SimpleGraph.compl_adj] <;> tauto
  have hc := Finset.card_union_of_disjoint hd
  rw [hu,SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe,hS] at hc
  have hn : N.edgeFinset.card ≤ 54 := by
    have hb := (sixteen_induced_edges S hS).1
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hb
  norm_num [Nat.choose] at hc
  have hb : 66 ≤ Nᶜ.edgeFinset.card := by omega
  convert hb using 1

/-- 11.5: sixteen single positions in the exact 24-position pattern give
66 distinct unordered colour pairs with nonadjacent representatives joined
by Kempe chains. ShellChains proves that every internal edge of these chains
avoids the closed vertex neighbourhood of both endpoints of the hole. -/
theorem sixty_six_chains {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}
    (φ : PartialColouring (L2 G) F) {e : G.edgeSet} (hstop : φ.Stuck e)
    (ι : Position → G.edgeSet) (hinj : Function.Injective ι)
    (hpattern : ∀ x y, (L2 G).Adj (ι x) (ι y) → graph.Adj x y)
    (S : Finset Position) (hS : S.card = 16)
    (hs : ∀ x ∈ S, φ.Single e (φ.colour (ι x)) (ι x)) :
    ∃ P : Finset (Sym2 Colour), 66 ≤ P.card ∧
      ∀ t ∈ P, ∃ a b f g, t = s(a,b) ∧ a ≠ b ∧
        φ.Single e a f ∧ φ.Single e b g ∧ ¬ (L2 G).Adj f g ∧
        φ.SameComponent a b f g := by
  let N := graph.induce (S : Set Position)
  let c : S → Colour := fun x => φ.colour (ι x.val)
  have hc : Function.Injective c := by
    intro x y heq
    apply Subtype.ext
    apply hinj
    have hx := hs x.val x.prop
    have hy := hs y.val y.prop
    exact (hy.2 (ι x.val) ⟨hx.1.1,hx.1.2.1,heq⟩)
  let P := Nᶜ.edgeFinset.image (Sym2.map c)
  refine ⟨P,?_,?_⟩
  · rw [Finset.card_image_of_injective _ (Sym2.map.injective hc)]
    exact sixteen_nonedge_card S hS
  · intro t ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨x,y,hp'⟩ : ∃ x y, p = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) p
    subst p
    have hxy : Nᶜ.Adj x y := Nᶜ.mem_edgeFinset.mp hp
    have hne : c x ≠ c y := fun h => hxy.1 (hc h)
    refine ⟨c x,c y,ι x.val,ι y.val,rfl,hne,hs x.val x.prop,hs y.val y.prop,?_,?_⟩
    · intro ha
      exact hxy.2 (hpattern x.val y.val ha)
    · exact φ.stuck_single_chain hstop hne (hs x.val x.prop) (hs y.val y.prop)

/-- The blocked colour count supplies the sixteen positions automatically
when the exact pattern labels the whole conflict neighbourhood. -/
theorem sixty_six_chains_of_stuck {V : Type*} [Fintype V] {G : SimpleGraph V}
    {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F) {e : G.edgeSet}
    (hstop : φ.Stuck e) (ι : Position ≃ ↥(conflicts G e))
    (hpattern : ∀ x y, (L2 G).Adj (ι x).val (ι y).val → graph.Adj x y) :
    ∃ P : Finset (Sym2 Colour), 66 ≤ P.card ∧
      ∀ t ∈ P, ∃ a b f g, t = s(a,b) ∧ a ≠ b ∧
        φ.Single e a f ∧ φ.Single e b g ∧ ¬ (L2 G).Adj f g ∧
        φ.SameComponent a b f g := by
  let j : Position → G.edgeSet := fun x => (ι x).val
  have hj : Function.Injective j := Subtype.val_injective.comp ι.injective
  let A := (Finset.univ : Finset Position).filter (fun x => φ.Single e (φ.colour (j x)) (j x))
  let C := φ.singleColours e
  have h24 : (conflicts G e).card = 24 := by
    have hc := Fintype.card_congr ι
    simpa only [Fintype.card_coe,positions_card] using hc.symm
  have hc := φ.blocked_single_count e hstop.1
  have hle : (φ.colouredNeighbours e).card ≤ (conflicts G e).card := by
    apply Finset.card_le_card
    intro f hf
    exact (mem_conflicts G e f).mpr (Finset.mem_filter.mp hf).2
  have hc16 : 16 ≤ C.card := by dsimp [C]; omega
  have reps (c : C) : ∃ f, φ.Single e c.val f := (φ.mem_singleColours e c.val).mp c.prop
  let f : C → G.edgeSet := fun c => (reps c).choose
  have hf (c : C) : φ.Single e c.val (f c) := (reps c).choose_spec
  let pos : C → Position := fun c => ι.symm ⟨f c,(mem_conflicts G e (f c)).mpr (hf c).1.2.1⟩
  have hpos (c : C) : j (pos c) = f c := by simp [j,pos]
  have hposA (c : C) : pos c ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hpos]
    exact (hf c).1.2.2.symm ▸ hf c
  have hi : Function.Injective (fun c : C => (⟨pos c,hposA c⟩ : A)) := by
    intro a b hab
    have heq : f a = f b := by
      have hp := congrArg (fun x : A => j x.val) hab
      simpa only [hpos] using hp
    apply Subtype.ext
    exact (hf a).1.2.2.symm.trans ((congrArg φ.colour heq).trans (hf b).1.2.2)
  have hca : C.card ≤ A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hi
  obtain ⟨S,hSA,hS⟩ := Finset.exists_subset_card_eq (hc16.trans hca)
  exact sixty_six_chains φ hstop j hj hpattern S hS
    (fun x hx => (Finset.mem_filter.mp (hSA hx)).2)

end Se20Insertion.TreePattern

