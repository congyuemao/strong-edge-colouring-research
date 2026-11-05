import Se20Part.Contraction

noncomputable section
open scoped Classical
namespace Se20Part
open SimpleGraph

/-- Remark 3.3: each incidence chooses one of two ports. -/
def splitGraph {V : Type*} (H : SimpleGraph V) (port : V → V → Bool) :
    SimpleGraph (V × Bool) where
  Adj p q := (p.1 = q.1 ∧ p.2 ≠ q.2) ∨
    (H.Adj p.1 q.1 ∧ port p.1 q.1 = p.2 ∧ port q.1 p.1 = q.2)
  symm := ⟨by
    rintro p q (h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro p h; rcases h with h | h; exact h.2 rfl; exact H.irrefl h.1⟩

def splitEdge {V : Type*} (H : SimpleGraph V) (port : V → V → Bool) (v : V) :
    (splitGraph H port).edgeSet :=
  ⟨s((v, false), (v, true)), Or.inl ⟨rfl, Bool.false_ne_true⟩⟩

theorem splitEdge_injective {V : Type*} (H : SimpleGraph V) (port : V → V → Bool) :
    Function.Injective (splitEdge H port) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simpa [splitEdge, Sym2.eq_iff] using h'

theorem split_matching {V : Type*} (H : SimpleGraph V) (port : V → V → Bool) :
    IsMatching (Set.range (splitEdge H port)) := by
  rintro e ⟨x, rfl⟩ f ⟨y, rfl⟩ v hvx hvy
  have hxy : x = y := by
    simp only [splitEdge, Sym2.mem_iff] at hvx hvy
    rcases hvx with h | h <;> rcases hvy with h' | h' <;>
      exact (congrArg Prod.fst h).symm.trans (congrArg Prod.fst h')
  subst y
  rfl

theorem split_conflict_iff {V : Type*} (H : SimpleGraph V) (port : V → V → Bool)
    (x y : V) :
    (L2 (splitGraph H port)).Adj (splitEdge H port x) (splitEdge H port y) ↔ H.Adj x y := by
  constructor
  · rintro ⟨hne, a, ha, b, hb, hab⟩
    have hxy : x ≠ y := fun h => hne (congrArg (splitEdge H port) h)
    have ha' : a.1 = x := by simpa [splitEdge, Sym2.mem_iff] using
      (show a.1 = x from (by rcases (Sym2.mem_iff.mp ha) with rfl | rfl <;> rfl))
    have hb' : b.1 = y := by
      rcases (Sym2.mem_iff.mp hb) with rfl | rfl <;> rfl
    rcases hab with h | h
    · exact (hxy (ha'.symm.trans ((congrArg Prod.fst h).trans hb'))).elim
    · rcases h with h | h
      · exact (hxy (ha'.symm.trans (h.1.trans hb'))).elim
      · simpa [ha', hb'] using h.1
  · intro h
    refine ⟨fun he => h.ne (splitEdge_injective H port he),
      (x, port x y), ?_, (y, port y x), ?_, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
    · cases port x y <;> simp [splitEdge]
    · cases port y x <;> simp [splitEdge]

def splitIso {V : Type*} (H : SimpleGraph V) (port : V → V → Bool) :
    H ≃g ConflictGraph (splitGraph H port) (Set.range (splitEdge H port)) where
  toEquiv := Equiv.ofInjective _ (splitEdge_injective H port)
  map_rel_iff' := by
    intro x y
    exact split_conflict_iff H port x y

private theorem internal_edge {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (h : (splitGraph H port).Adj p q) (he : p.1 = q.1) :
    s(p, q) = s((p.1, false), (p.1, true)) := by
  rcases p with ⟨x, i⟩
  rcases q with ⟨y, j⟩
  dsimp at he
  subst y
  have hij : i ≠ j := h.resolve_right (by simp) |>.2
  cases i <;> cases j <;> simp_all [Sym2.eq_swap]

/-- Project a walk, erasing the edges inside split vertices. -/
def projectSplitWalk {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (w : (splitGraph H port).Walk p q) : H.Walk p.1 q.1 :=
  match w with
  | .nil => .nil
  | @Walk.cons _ _ u v _ h w =>
    if he : u.1 = v.1 then (projectSplitWalk w).copy he.symm rfl
    else .cons ((h.resolve_left (fun h => he h.1)).1) (projectSplitWalk w)

theorem projectSplitWalk_length_le {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (w : (splitGraph H port).Walk p q) :
    (projectSplitWalk w).length ≤ w.length := by
  induction w with
  | nil => simp [projectSplitWalk]
  | cons h w ih =>
    simp only [projectSplitWalk]
    split_ifs <;> simp_all <;> omega

private theorem projected_edge_mem {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (w : (splitGraph H port).Walk p q) (x y : V)
    (he : s(x,y) ∈ (projectSplitWalk w).edges) :
    s((x, port x y), (y, port y x)) ∈ w.edges := by
  induction w with
  | nil => simp [projectSplitWalk] at he
  | @cons u v z h w ih =>
    by_cases huv : u.1 = v.1
    · simp only [projectSplitWalk, dite_eq_left huv, Walk.edges_copy] at he
      exact List.mem_cons_of_mem _ (ih he)
    · simp only [projectSplitWalk, dite_eq_right huv, Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · have hh := h.resolve_left (fun h => huv h.1)
        rcases Sym2.eq_iff.mp he with he | he
        · have hu : (x, port x y) = u := Prod.ext he.1 (by simpa [he.1, he.2] using hh.2.1)
          have hv : (y, port y x) = v := Prod.ext he.2 (by simpa [he.1, he.2] using hh.2.2)
          simp [hu, hv]
        · have hu : (y, port y x) = u := Prod.ext he.2 (by simpa [he.1, he.2] using hh.2.1)
          have hv : (x, port x y) = v := Prod.ext he.1 (by simpa [he.1, he.2] using hh.2.2)
          simp [hu, hv, Sym2.eq_swap]
      · exact List.mem_cons_of_mem _ (ih he)

theorem projectSplitWalk_isTrail {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (w : (splitGraph H port).Walk p q) (hw : w.IsTrail) :
    (projectSplitWalk w).IsTrail := by
  induction w with
  | nil => simp [projectSplitWalk]
  | @cons u v z h w ih =>
    have ht := (Walk.isTrail_cons _ _).mp hw
    by_cases huv : u.1 = v.1
    · simpa [projectSplitWalk, huv] using ih ht.1
    · simp only [projectSplitWalk, dite_eq_right huv, Walk.isTrail_cons]
      refine ⟨ih ht.1, ?_⟩
      intro he
      have he' := projected_edge_mem w u.1 v.1 he
      have hh := h.resolve_left (fun h => huv h.1)
      have hu : (u.1, port u.1 v.1) = u := Prod.ext rfl hh.2.1
      have hv : (v.1, port v.1 u.1) = v := Prod.ext rfl hh.2.2
      exact ht.2 (by simpa [hu, hv] using he')

private theorem project_nil_edges {V : Type*} {H : SimpleGraph V} {port : V → V → Bool}
    {p q : V × Bool} (w : (splitGraph H port).Walk p q)
    (hw : (projectSplitWalk w).Nil) :
    ∀ e ∈ w.edges, e = s((p.1, false), (p.1, true)) := by
  induction w with
  | nil => simp
  | @cons u v z h w ih =>
    by_cases huv : u.1 = v.1
    · have hw' : (projectSplitWalk w).Nil := by simpa [projectSplitWalk, huv] using hw
      intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact internal_edge h huv
      · simpa [huv] using ih hw' e he
    · simp [projectSplitWalk, huv] at hw

theorem split_girth {V : Type*} {H : SimpleGraph V} (port : V → V → Bool)
    {g : ℕ} (hg : GirthAtLeast H g) : GirthAtLeast (splitGraph H port) g := by
  intro p w hw
  have hn : ¬ (projectSplitWalk w).Nil := by
    intro hn
    have hs : w.edges.toFinset ⊆ {s((p.1, false), (p.1, true))} := by
      intro e he
      simpa using project_nil_edges w hn e (List.mem_toFinset.mp he)
    have hc := Finset.card_le_card hs
    rw [List.toFinset_card_of_nodup hw.edges_nodup, Walk.length_edges] at hc
    have ht := hw.three_le_length
    simp only [Finset.card_singleton] at hc
    omega
  have ht : (projectSplitWalk w).IsCircuit :=
    ⟨projectSplitWalk_isTrail w hw.isTrail, by simpa using hn⟩
  have he := ht.egirth_le_length
  have hg' := (girthAtLeast_iff_egirth H g).mp hg
  have hl : g ≤ (projectSplitWalk w).length := by exact_mod_cast hg'.trans he
  exact hl.trans (projectSplitWalk_length_le w)

def splitSlot {V : Type*} [Fintype V] (H : SimpleGraph V) (hd : DegreeLE H 6)
    (v : V) : H.neighborSet v ↪ Fin 6 :=
  (Function.Embedding.nonempty_of_card_le (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hd v)).some

def balancedPort {V : Type*} [Fintype V] (H : SimpleGraph V) (hd : DegreeLE H 6)
    (x y : V) : Bool :=
  if h : H.Adj x y then decide ((splitSlot H hd x ⟨y,h⟩).val < 3) else false

private theorem slot_inj_of_port_mod {V : Type*} [Fintype V]
    {H : SimpleGraph V} (hd : DegreeLE H 6) {x y z : V}
    (hy : H.Adj x y) (hz : H.Adj x z)
    (hp : balancedPort H hd x y = balancedPort H hd x z)
    (hm : (splitSlot H hd x ⟨y,hy⟩).val % 3 = (splitSlot H hd x ⟨z,hz⟩).val % 3) : y = z := by
  simp only [balancedPort, dite_eq_left hy, dite_eq_left hz, decide_eq_decide] at hp
  have hyb := (splitSlot H hd x ⟨y,hy⟩).isLt
  have hzb := (splitSlot H hd x ⟨z,hz⟩).isLt
  have hs : splitSlot H hd x ⟨y,hy⟩ = splitSlot H hd x ⟨z,hz⟩ := by
    apply Fin.ext
    omega
  exact congrArg Subtype.val ((splitSlot H hd x).injective hs)

theorem split_maxDegree_four {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hd : DegreeLE H 6) : MaxDegreeFour (splitGraph H (balancedPort H hd)) := by
  intro p
  let G := splitGraph H (balancedPort H hd)
  have hcross (q : G.neighborSet p) (h : q.val.1 ≠ p.1) : H.Adj p.1 q.val.1 :=
    (q.property.resolve_left (fun he => h he.1.symm)).1
  let code : G.neighborSet p → Option (Fin 3) := fun q =>
    if h : q.val.1 = p.1 then none else
      some ⟨(splitSlot H hd p.1 ⟨q.val.1, hcross q h⟩).val % 3, Nat.mod_lt _ (by norm_num)⟩
  have hi : Function.Injective code := by
    intro q r he
    apply Subtype.ext
    by_cases hq : q.val.1 = p.1 <;> by_cases hr : r.val.1 = p.1
    · have hq' : p.2 ≠ q.val.2 :=
        (q.property.resolve_right (fun h => H.irrefl (hq ▸ h.1))).2
      have hr' : p.2 ≠ r.val.2 :=
        (r.property.resolve_right (fun h => H.irrefl (hr ▸ h.1))).2
      apply Prod.ext (hq.trans hr.symm)
      cases hp : p.2 <;> cases hqq : q.val.2 <;> cases hrr : r.val.2 <;> simp_all
    · simp [code, hq, hr] at he
    · simp [code, hq, hr] at he
    · have hqp := q.property.resolve_left (fun h => hq h.1.symm)
      have hrp := r.property.resolve_left (fun h => hr h.1.symm)
      have hm : (splitSlot H hd p.1 ⟨q.val.1, hcross q hq⟩).val % 3 =
          (splitSlot H hd p.1 ⟨r.val.1, hcross r hr⟩).val % 3 := by
        simpa [code, hq, hr, Fin.ext_iff] using he
      have hfst := slot_inj_of_port_mod hd (hcross q hq) (hcross r hr)
        (hqp.2.1.trans hrp.2.1.symm) hm
      exact Prod.ext hfst (hqp.2.2.symm.trans (by simpa [hfst] using hrp.2.2))
  have hc := Fintype.card_le_of_injective code hi
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_option, Fintype.card_fin] using hc

/-- Remark 3.3, including the degree bound, graph isomorphism, and all girth lower bounds. -/
theorem remark_3_3 {V : Type*} [Fintype V] (H : SimpleGraph V) (hd : DegreeLE H 6) :
    ∃ (G : SimpleGraph (V × Bool)) (M : Set G.edgeSet),
      MaxDegreeFour G ∧ IsMatching M ∧ Nonempty (H ≃g ConflictGraph G M) ∧
        ∀ g, GirthAtLeast H g → GirthAtLeast G g := by
  refine ⟨splitGraph H (balancedPort H hd), Set.range (splitEdge H (balancedPort H hd)),
    split_maxDegree_four hd, split_matching _ _, ⟨splitIso _ _⟩, ?_⟩
  exact fun _ h => split_girth _ h

end Se20Part
