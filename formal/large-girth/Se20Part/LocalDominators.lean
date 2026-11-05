import Se20Part.CycleSelection
import Se20Part.LocalGeometry
import Se20Part.SeedReduction

noncomputable section
open scoped Classical
open SimpleGraph Finset
namespace Se20Part

def NoBacktrack {V : Type*} {G : SimpleGraph V} {u v : V} : G.Walk u v → Prop
  | .nil => True
  | @Walk.cons _ _ x _y _z _ p => (p.Nil ∨ x ≠ p.snd) ∧ NoBacktrack p

theorem short_noBacktrack_isPath {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {u v : V} (p : G.Walk u v)
    (hn : NoBacktrack p) (hl : p.length < g) : p.IsPath := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hp : p.IsPath := ih hn.2 (by simpa using Nat.lt_of_succ_lt hl)
    rw [Walk.cons_isPath_iff]
    refine ⟨hp, ?_⟩
    intro hu
    have heq := short_paths_unique hg (hp.takeUntil hu) (Walk.IsPath.of_adj h.symm)
      (by have := p.length_takeUntil_le_length hu; simp only [Walk.length_cons] at hl; simpa using (show (p.takeUntil u hu).length + 1 < g by omega))
    have hs := congrArg Walk.snd heq
    rw [Walk.snd_takeUntil h.ne p hu] at hs
    have hs' : p.snd = u := by simpa using hs
    rcases hn.1 with hn | hn
    · have : u = v := by simpa only [Walk.nil_iff_support_eq.mp hn, List.mem_singleton] using hu
      exact h.ne this
    · exact hn hs'.symm

theorem short_noBacktrack_edist {V : Type*} {G : SimpleGraph V} {g : ℕ}
    (hg : GirthAtLeast G g) {u v : V} (p : G.Walk u v)
    (hn : NoBacktrack p) (hl : 2 * p.length < g) :
    G.edist u v = p.length := by
  have hp := short_noBacktrack_isPath hg p hn (by omega)
  rw [← p.reachable.coe_dist_eq_edist, ← short_path_geodesic hg p hp hl]

theorem no_shortcut {V : Type*} {G : SimpleGraph V} {g k : ℕ}
    (hg : GirthAtLeast G g) {u v : V} (p : G.Walk u v)
    (hn : NoBacktrack p) (hk : k < p.length) (hl : p.length + k < g)
    (q : G.Walk u v) (hq : q.length ≤ k) : False := by
  have hp := short_noBacktrack_isPath hg p hn (by omega)
  have heq := short_paths_unique hg hp q.bypass_isPath
    (by have := q.length_bypass_le_length; omega)
  have hh := congrArg Walk.length heq
  have := q.length_bypass_le_length
  omega

theorem external_six_endpoint_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {e : G.edgeSet} (hsix : Nat.card (External G e) = 6)
    {u : V} (hu : u ∈ e.val) : G.degree u = 4 := by
  obtain ⟨v, he⟩ := Sym2.mem_iff_exists.mp hu
  have huv : G.Adj u v := by simpa [he] using e.property
  let s := (G.neighborFinset u).erase v
  let t := (G.neighborFinset v).erase u
  have hsub : (External G e).toFinset ⊆ s ∪ t := by
    intro w hw
    obtain ⟨hwn, a, ha, haw⟩ := Set.mem_toFinset.mp hw
    have hwu : w ≠ u := by intro h; apply hwn; simp [he, h]
    have hwv : w ≠ v := by intro h; apply hwn; simp [he, h]
    simp only [he, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact mem_union_left _ (by simp [s, hwv, haw])
    · exact mem_union_right _ (by simp [t, hwu, haw])
  have hs : s.card = G.degree u - 1 := card_erase_of_mem (by simpa using huv)
  have ht : t.card = G.degree v - 1 := card_erase_of_mem (by simpa using huv.symm)
  have hb := (card_le_card hsub).trans (card_union_le s t)
  rw [hs, ht] at hb
  have hu' := hd u
  have hv' := hd v
  have hc : Nat.card (External G e) = (External G e).toFinset.card := by
    rw [Nat.card_eq_fintype_card]; simp
  omega

theorem problem_branch {V : Type*} [Fintype V] {G : SimpleGraph V}
    {M : Set G.edgeSet} {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    ∃ w z a, r.val = s(w,z) ∧ a ∈ h.val ∧ G.Adj w a ∧ a ≠ z := by
  have hne : h ≠ r := fun h => hr (h ▸ hh.1)
  by_cases hmeet : ∃ w, w ∈ r.val ∧ w ∈ h.val
  · obtain ⟨w, hwr, hwh⟩ := hmeet
    obtain ⟨z, hrz⟩ := Sym2.mem_iff_exists.mp hwr
    obtain ⟨a, hha⟩ := Sym2.mem_iff_exists.mp hwh
    have hwa : G.Adj w a := by simpa [hha] using h.property
    refine ⟨w, z, a, hrz, ?_, hwa, ?_⟩
    · simp [hha]
    · intro haz
      exact hne (Subtype.ext (by rw [hha, hrz, haz]))
  · obtain ⟨_, a, hah, w, hwr, haw⟩ := hh.2.1
    have hawn : a ≠ w := fun haw => hmeet ⟨w, hwr, haw ▸ hah⟩
    have hwa : G.Adj w a := (haw.resolve_left hawn).symm
    obtain ⟨z, hrz⟩ := Sym2.mem_iff_exists.mp hwr
    refine ⟨w, z, a, hrz, hah, hwa, ?_⟩
    intro haz
    exact hmeet ⟨a, by simp [hrz, haz], hah⟩

structure DefectArm {V : Type*} (G : SimpleGraph V) (r d : G.edgeSet) where
  w : V
  z : V
  a : V
  p : V
  t : V
  root : r.val = s(w,z)
  edge : d.val = s(p,t)
  wa : G.Adj w a
  ap : G.Adj a p
  pt : G.Adj p t
  az : a ≠ z
  pw : p ≠ w
  ta : t ≠ a

theorem problem_arm {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hd : MaxDegreeFour G) {M : Set G.edgeSet} (hm : IsMatching M)
    {r h : G.edgeSet} (hr : r ∉ M) (hh : ProblemAt G M r h) :
    ∃ d : M, ∃ A : DefectArm G r d.val,
      A.a ∈ h.val ∧ (L2 G).Adj h d.val := by
  obtain ⟨w,z,a,hrz,hah,hwa,haz⟩ := problem_branch hr hh
  obtain ⟨b, hhab⟩ := Sym2.mem_iff_exists.mp hah
  have hdeg := external_six_endpoint_degree hd hh.2.2.1 hah
  have hex : ∃ p ∈ G.neighborFinset a, p ∉ ({w,b} : Finset V) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have : ({w,b} : Finset V).card ≤ 2 := by
      calc
        _ ≤ ({b} : Finset V).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    rw [G.card_neighborFinset_eq_degree, hdeg]
    omega
  obtain ⟨p, hp, hpn⟩ := hex
  have hap : G.Adj a p := by simpa using hp
  have hpw : p ≠ w := by simpa using (not_or.mp (by simpa using hpn)).1
  have hpb : p ≠ b := by simpa using (not_or.mp (by simpa using hpn)).2
  have hpe : p ∈ External G h := by
    refine ⟨?_, a, hah, hap⟩
    simpa [hhab, Sym2.mem_iff] using And.intro hap.ne.symm hpb
  obtain ⟨d, hdm, hpd⟩ := hh.2.2.2 hpe
  obtain ⟨t, hdt⟩ := Sym2.mem_iff_exists.mp hpd
  have hpt : G.Adj p t := by simpa [hdt] using d.property
  have hdh : d ≠ h := fun h => hpe.1 (h ▸ hpd)
  have hta : t ≠ a := by
    intro hta
    apply hdh
    apply hm hdm hh.1 (v := a)
    · simp [hdt, hta]
    · exact hah
  refine ⟨⟨d, hdm⟩, ⟨w,z,a,p,t,hrz,hdt,hwa,hap,hpt,haz,hpw,hta⟩, hah, ?_⟩
  exact (matching_conflict_iff hm hh.1 hdm).mpr ⟨p, hpe, hpd⟩

theorem DefectArm.root_adj {V : Type*} {G : SimpleGraph V} {r d : G.edgeSet}
    (A : DefectArm G r d) : G.Adj A.w A.z := by
  simpa [A.root] using r.property

theorem DefectArm.layers {V : Type*} {G : SimpleGraph V} {r d : G.edgeSet}
    (hg : GirthAtLeast G 11) (A : DefectArm G r d) :
    VertexEdgeDistance G A.p r 2 ∧ VertexEdgeDistance G A.t r 3 := by
  have hpw : G.edist A.p A.w = 2 := by
    apply short_noBacktrack_edist hg (.cons A.ap.symm (.cons A.wa.symm .nil))
    · simp [NoBacktrack, A.pw]
    · norm_num
  have hpz : G.edist A.p A.z = 3 := by
    apply short_noBacktrack_edist hg (.cons A.ap.symm (.cons A.wa.symm
      (.cons A.root_adj .nil)))
    · simp [NoBacktrack, A.pw, A.az]
    · norm_num
  have htw : G.edist A.t A.w = 3 := by
    apply short_noBacktrack_edist hg (.cons A.pt.symm (.cons A.ap.symm (.cons A.wa.symm .nil)))
    · simp [NoBacktrack, A.pw, A.ta]
    · norm_num
  have htz : G.edist A.t A.z = 4 := by
    apply short_noBacktrack_edist hg (.cons A.pt.symm (.cons A.ap.symm
      (.cons A.wa.symm (.cons A.root_adj .nil))))
    · simp [NoBacktrack, A.pw, A.ta, A.az]
    · norm_num
  constructor
  · refine ⟨?_, A.w, by simp [A.root], hpw⟩
    intro x hx
    rw [A.root, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [hpw, hpz]
  · refine ⟨?_, A.w, by simp [A.root], htw⟩
    intro x hx
    rw [A.root, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [htw, htz]

theorem DefectArm.separated {V : Type*} {G : SimpleGraph V} {r d d' : G.edgeSet}
    (hg : GirthAtLeast G 11) (A : DefectArm G r d) (B : DefectArm G r d')
    (hab : A.a ≠ B.a) : ¬ EdgeWithin G 3 d d' := by
  rintro ⟨x,hx,y,hy,q,hq⟩
  rw [A.edge, Sym2.mem_iff] at hx
  rw [B.edge, Sym2.mem_iff] at hy
  have hroot : s(A.w,A.z) = s(B.w,B.z) := A.root.symm.trans B.root
  rcases Sym2.eq_iff.mp hroot with ⟨hw,hz⟩ | ⟨hw,hz⟩
  · have wba : G.Adj A.w B.a := hw ▸ B.wa
    have bpw : B.p ≠ A.w := by simpa only [hw] using B.pw
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact no_shortcut hg (.cons A.ap.symm (.cons A.wa.symm
        (.cons wba (.cons B.ap .nil)))) (by simp [NoBacktrack, A.pw, hab, bpw.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.ap.symm (.cons A.wa.symm
        (.cons wba (.cons B.ap (.cons B.pt .nil)))))
        (by simp [NoBacktrack, A.pw, hab, bpw.symm, B.ta.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.pt.symm (.cons A.ap.symm (.cons A.wa.symm
        (.cons wba (.cons B.ap .nil)))))
        (by simp [NoBacktrack, A.ta, A.pw, hab, bpw.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.pt.symm (.cons A.ap.symm (.cons A.wa.symm
        (.cons wba (.cons B.ap (.cons B.pt .nil))))))
        (by simp [NoBacktrack, A.ta, A.pw, hab, bpw.symm, B.ta.symm])
        (by norm_num) (by norm_num) q hq
  · have zba : G.Adj A.z B.a := hz ▸ B.wa
    have baw : B.a ≠ A.w := by simpa only [hw] using B.az
    have bpz : B.p ≠ A.z := by simpa only [hz] using B.pw
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact no_shortcut hg (.cons A.ap.symm (.cons A.wa.symm
        (.cons A.root_adj (.cons zba (.cons B.ap .nil)))))
        (by simp [NoBacktrack, A.pw, A.az, baw.symm, bpz.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.ap.symm (.cons A.wa.symm
        (.cons A.root_adj (.cons zba (.cons B.ap (.cons B.pt .nil))))))
        (by simp [NoBacktrack, A.pw, A.az, baw.symm, bpz.symm, B.ta.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.pt.symm (.cons A.ap.symm (.cons A.wa.symm
        (.cons A.root_adj (.cons zba (.cons B.ap .nil))))))
        (by simp [NoBacktrack, A.ta, A.pw, A.az, baw.symm, bpz.symm])
        (by norm_num) (by norm_num) q hq
    · exact no_shortcut hg (.cons A.pt.symm (.cons A.ap.symm (.cons A.wa.symm
        (.cons A.root_adj (.cons zba (.cons B.ap (.cons B.pt .nil)))))))
        (by simp [NoBacktrack, A.ta, A.pw, A.az, baw.symm, bpz.symm, B.ta.symm])
        (by norm_num) (by norm_num) q hq

/-- Lemma 3.6, including simultaneous separation of all local choices. -/
theorem local_dominators : LocalDominatorsStatement := by
  intro V _ G hd hg M hm r hr
  choose d A ha hadj using fun h : {h // ProblemAt G M r h} => problem_arm hd hm hr h.property
  refine ⟨d, fun h => ⟨hadj h, (A h).p, (A h).t, (A h).edge,
    ((A h).layers hg).1, ((A h).layers hg).2⟩, ?_⟩
  intro h h' hne
  apply DefectArm.separated hg (A h) (A h')
  intro heq
  exact hne (Subtype.ext (hm h.property.1 h'.property.1 (ha h) (heq ▸ ha h')))

end Se20Part
