import Se20Part.MatchingTriangle
import Se20Part.GirthDegree

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem mem_hubs (e f : G.edgeSet) :
    f ∈ hubs G e ↔ f ≠ e ∧ ∃ v ∈ e.val, v ∈ f.val := by simp [hubs]

local instance : DecidableEq G.edgeSet := Classical.decEq _

def Linked (T : Finset G.edgeSet) : Prop :=
  ∀ e ∈ T, ∀ f ∈ T, e ≠ f → f ∉ hubs G e

def Diffuse (T : Finset G.edgeSet) : Prop := ¬ Compact G T

theorem two_hubs_compact (e f g : G.edgeSet)
    (hf : f ∈ hubs G e) (hg : g ∈ hubs G e) : Compact G {e,f,g} := by
  obtain ⟨_,x,hxe,hxf⟩ := (mem_hubs G _ _).mp hf
  obtain ⟨_,z,hze,hzg⟩ := (mem_hubs G _ _).mp hg
  obtain ⟨u,v,he⟩ : ∃ u v, e.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) e.val
  obtain ⟨y,hf⟩ := Sym2.mem_iff_exists.mp hxf
  obtain ⟨t,hg⟩ := Sym2.mem_iff_exists.mp hzg
  have hs : edgeSupport G {e,f,g} ⊆ {u,v,y,t} := by
    intro a ha
    obtain ⟨b,hb,hab⟩ := Finset.mem_biUnion.mp ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    have hx : x = u ∨ x = v := by simpa [he,Sym2.mem_iff] using hxe
    have hz : z = u ∨ z = v := by simpa [he,Sym2.mem_iff] using hze
    rcases hb with rfl|rfl|rfl <;> simp only [he,hf,hg,Sym2.mem_toFinset,Sym2.mem_iff] at hab <;>
      simp only [Finset.mem_insert,Finset.mem_singleton] <;> aesop
  exact (Finset.card_le_card hs).trans (by
    have h1 := Finset.card_insert_le u {v,y,t}
    have h2 := Finset.card_insert_le v {y,t}
    have h3 := Finset.card_insert_le y {t}
    simp only [Finset.card_singleton] at h3
    omega)

theorem diffuse_at_most_one_hub {T : Finset G.edgeSet} (hT : T.card = 3)
    (hD : Diffuse G T) {e : G.edgeSet} (he : e ∈ T)
    {f g : G.edgeSet} (hf : f ∈ T) (hg : g ∈ T)
    (hfhub : f ∈ hubs G e) (hghub : g ∈ hubs G e) : f = g := by
  by_contra hfg
  have hef := ((mem_hubs G _ _).mp hfhub).1.symm
  have heg := ((mem_hubs G _ _).mp hghub).1.symm
  have hs : {e,f,g} = T := Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨he,hf,hg⟩)
    (by simp [hT,hef,heg,hfg])
  exact hD (hs ▸ two_hubs_compact G e f g hfhub hghub)

theorem diffuse_erase_linked {T : Finset G.edgeSet} (hT : T.card = 3)
    (hD : Diffuse G T) {e f : G.edgeSet} (he : e ∈ T) (hf : f ∈ T)
    (hfhub : f ∈ hubs G e) : Linked G (T.erase e) := by
  intro a ha b hb hab hbh
  obtain ⟨hae,ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbe,hb⟩ := Finset.mem_erase.mp hb
  have hfe := ((mem_hubs G _ _).mp hfhub).1
  have hs : T.erase e = {a,b} := (Finset.eq_of_subset_of_card_le
    (show {a,b} ⊆ T.erase e by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_erase]
      exact ⟨⟨hae,ha⟩,⟨hbe,hb⟩⟩) (by
      have hc := Finset.card_erase_add_one he
      rw [Finset.card_pair hab]
      omega)).symm
  have hf' : f = a ∨ f = b := by
    have hh : f ∈ T.erase e := Finset.mem_erase.mpr ⟨hfe,hf⟩
    simpa [hs] using hh
  rcases hf' with rfl|rfl
  · have hh := diffuse_at_most_one_hub G hT hD hf he hb (hubs_symm G hfhub) hbh
    exact hbe hh.symm
  · have hh := diffuse_at_most_one_hub G hT hD hf he ha (hubs_symm G hfhub) (hubs_symm G hbh)
    exact hae hh.symm

theorem triangle_has_hub (hg : 7 ≤ G.egirth) {T : Finset G.edgeSet}
    (hT : T.card = 3) (hcl : (L2 G).IsClique (T : Set G.edgeSet)) :
    ∃ e ∈ T, ∃ f ∈ T, f ∈ hubs G e := by
  by_contra! hn
  apply no_matching_clique_three G hg T hT hcl
  intro e he f hf hef v hve hvf
  exact hn e he f hf ((mem_hubs G _ _).mpr ⟨hef.symm,v,hve,hvf⟩)

/-- If the two edges left behind are disjoint, a triangle at girth seven
has a hub at its distinguished edge. -/
theorem linked_triangle_has_hub (hg : 7 ≤ G.egirth) {T : Finset G.edgeSet}
    (hT : T.card = 3) (hcl : (L2 G).IsClique (T : Set G.edgeSet))
    (e : G.edgeSet) (he : e ∈ T) (hl : Linked G (T.erase e)) :
    ∃ f ∈ T, f ∈ hubs G e := by
  obtain ⟨a,ha,b,hb,hh⟩ := triangle_has_hub G hg hT hcl
  by_cases hae : a = e
  · subst a; exact ⟨b,hb,hh⟩
  by_cases hbe : b = e
  · subst b; exact ⟨a,ha,hubs_symm G hh⟩
  exact False.elim (hl a (Finset.mem_erase.mpr ⟨hae,ha⟩)
    b (Finset.mem_erase.mpr ⟨hbe,hb⟩) ((mem_hubs G _ _).mp hh).1.symm hh)

/-- The common connector in the diffuse configuration is an actual ambient
edge, incident with each of the three selected edges. -/
theorem shared_triangle_bridge (hg : 7 ≤ G.egirth) (e f g : G.edgeSet)
    (hfe : f ∈ hubs G e) (hge : g ∉ hubs G e) (hgf : g ∉ hubs G f)
    (heg : (L2 G).Adj e g) (hfg : (L2 G).Adj f g) :
    ∃ δ : G.edgeSet, δ ∈ hubs G e ∧ δ ∈ hubs G f ∧ δ ∈ hubs G g := by
  obtain ⟨hfne,p,hpe,hpf⟩ := (mem_hubs G _ _).mp hfe
  obtain ⟨a,he⟩ := Sym2.mem_iff_exists.mp hpe
  obtain ⟨b,hf⟩ := Sym2.mem_iff_exists.mp hpf
  obtain ⟨c,d,hgcd⟩ : ∃ c d, g.val = s(c,d) := Sym2.ind (fun c d => ⟨c,d,rfl⟩) g.val
  have hpa : G.Adj p a := G.mem_edgeSet.mp (he ▸ e.prop)
  have hpb : G.Adj p b := G.mem_edgeSet.mp (hf ▸ f.prop)
  have hcd : G.Adj c d := G.mem_edgeSet.mp (hgcd ▸ g.prop)
  have hab : a ≠ b := by
    intro h
    exact hfne (Subtype.ext (by rw [he,hf,h]))
  have hav (q : V) (hqe : q ∈ e.val) (hqg : q ∈ g.val) : False :=
    hge ((mem_hubs G _ _).mpr ⟨heg.ne.symm,q,hqe,hqg⟩)
  have hbv (q : V) (hqf : q ∈ f.val) (hqg : q ∈ g.val) : False :=
    hgf ((mem_hubs G _ _).mpr ⟨hfg.ne.symm,q,hqf,hqg⟩)
  have hpc : p ≠ c := fun h => hav p hpe (by simp [hgcd,h])
  have hpd : p ≠ d := fun h => hav p hpe (by simp [hgcd,h])
  have hac : a ≠ c := fun h => hav a (by simp [he]) (by simp [hgcd,h])
  have had : a ≠ d := fun h => hav a (by simp [he]) (by simp [hgcd,h])
  have hbc : b ≠ c := fun h => hbv b (by simp [hf]) (by simp [hgcd,h])
  have hbd : b ≠ d := fun h => hbv b (by simp [hf]) (by simp [hgcd,h])
  have cross (r : V) (q : G.edgeSet) (hq : q.val = s(p,r))
      (hrc : r ≠ c) (hrd : r ≠ d) (hqg : (L2 G).Adj q g) :
      G.Adj p c ∨ G.Adj p d ∨ G.Adj r c ∨ G.Adj r d := by
    obtain ⟨_,u,hu,v,hv,huv⟩ := hqg
    simp only [hq,hgcd,Sym2.mem_iff] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
      rcases huv with huv|huv <;> simp_all
  have conn : G.Adj p c ∨ G.Adj p d := by
    by_contra! hn
    have hacd : G.Adj a c ∨ G.Adj a d :=
      ((cross a e he hac had heg).resolve_left hn.1).resolve_left hn.2
    have hbcd : G.Adj b c ∨ G.Adj b d :=
      ((cross b f hf hbc hbd hfg).resolve_left hn.1).resolve_left hn.2
    have hg5 : 5 ≤ G.egirth := le_trans (by norm_num) hg
    rcases hacd with hac'|had' <;> rcases hbcd with hbc'|hbd'
    · rcases GirthFive.square_backtrack hg5 hpa hac' hbc'.symm hpb.symm with h|h
      · exact hpc h
      · exact hab h
    · let w : G.Walk p p := .cons hpa (.cons hac' (.cons hcd (.cons hbd'.symm (.cons hpb.symm .nil))))
      have hw : w.IsCycle := by
        rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
        simp [w,SimpleGraph.Walk.isPath_def,hpa.ne,hpb.ne,hcd.ne,
          hab,hpc,hpd,hac,had,hbc,hbd,Ne.symm hpa.ne,Ne.symm hpb.ne,
          Ne.symm hbc,Ne.symm hbd,Ne.symm hpc,Ne.symm hpd]
      have hh := hg.trans hw.egirth_le_length
      norm_num [w] at hh
    · let w : G.Walk p p := .cons hpa (.cons had' (.cons hcd.symm (.cons hbc'.symm (.cons hpb.symm .nil))))
      have hw : w.IsCycle := by
        rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
        simp [w,SimpleGraph.Walk.isPath_def,hpa.ne,hpb.ne,hcd.ne,
          hab,hpc,hpd,hac,had,hbc,hbd,Ne.symm hpa.ne,Ne.symm hpb.ne,
          Ne.symm hbc,Ne.symm hbd,Ne.symm hcd.ne,Ne.symm hpc,Ne.symm hpd]
      have hh := hg.trans hw.egirth_le_length
      norm_num [w] at hh
    · rcases GirthFive.square_backtrack hg5 hpa had' hbd'.symm hpb.symm with h|h
      · exact hpd h
      · exact hab h
  have build (q : V) (hq : q ∈ g.val) (hpq : G.Adj p q) :
      ∃ δ : G.edgeSet, δ ∈ hubs G e ∧ δ ∈ hubs G f ∧ δ ∈ hubs G g := by
    let δ : G.edgeSet := ⟨s(p,q),G.mem_edgeSet.mpr hpq⟩
    have hδe : δ ≠ e := by
      intro hh
      exact hav q (hh ▸ (show q ∈ δ.val by simp [δ])) hq
    have hδf : δ ≠ f := by
      intro hh
      exact hbv q (hh ▸ (show q ∈ δ.val by simp [δ])) hq
    have hδg : δ ≠ g := by
      intro hh
      exact hav p hpe (hh ▸ (show p ∈ δ.val by simp [δ]))
    exact ⟨δ,(mem_hubs G _ _).mpr ⟨hδe,p,hpe,by simp [δ]⟩,
      (mem_hubs G _ _).mpr ⟨hδf,p,hpf,by simp [δ]⟩,
      (mem_hubs G _ _).mpr ⟨hδg,q,hq,by simp [δ]⟩⟩
  exact conn.elim (build c (by simp [hgcd])) (build d (by simp [hgcd]))

end Se20Part
