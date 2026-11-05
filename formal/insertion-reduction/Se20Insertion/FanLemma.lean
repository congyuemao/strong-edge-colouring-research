import Se20Insertion.ChordalFan
import Se20Insertion.Neighbourhood87

noncomputable section
open scoped Classical
namespace Se20Insertion
namespace FanLemma
variable {V : Type*} {G : SimpleGraph V}

/-- The endpoint or joining-edge witness is retained in `T`. -/
def Realizes (T : SimpleGraph V) (e f : G.edgeSet) : Prop :=
  ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ T.Adj a b

/-- Only the edges used by the path and its two attachments need survive in
the forest. `T` need not be an induced subgraph, connected, or finite. -/
theorem fan_of_forest (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsAcyclic)
    {p : ℕ → G.edgeSet} {n : ℕ} (hp : ChordalFan.InducedPath (L2 G) p n)
    {v : G.edgeSet} (hv : ∀ i ≤ n, v ≠ p i)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ n, (p i).val ∈ T.edgeSet)
    (h0 : Realizes T v (p 0)) (hn : Realizes T v (p n))
    (hstep : ∀ i < n, Realizes T (p i) (p (i+1))) :
    ∀ i ≤ n, (L2 G).Adj v (p i) := by
  let q : ℕ → T.edgeSet := fun i => ⟨(p (min i n)).val, hpT _ (min_le_right _ _)⟩
  let u : T.edgeSet := ⟨v.val,hvT⟩
  have hmap : ∀ i ≤ n, (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id) (q i) = p i := by
    intro i hi
    apply Subtype.ext
    simp [q, min_eq_left hi, L2Map, SimpleGraph.Hom.mapEdgeSet]
  have hmapu : (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id) u = v := by
    apply Subtype.ext
    simp [u, L2Map, SimpleGraph.Hom.mapEdgeSet]
  have hreal : ∀ i ≤ n, ∀ j ≤ n, (p i ≠ p j) →
      Realizes T (p i) (p j) → (L2 T).Adj (q i) (q j) := by
    intro i hi j hj hne hr
    refine ⟨fun he => hne ?_, ?_⟩
    · have he' := congrArg (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id) he
      simpa only [hmap i hi,hmap j hj] using he'
    · simpa only [q, min_eq_left hi,min_eq_left hj,Realizes] using hr
  have hq : ChordalFan.InducedPath (L2 T) q n := by
    constructor
    · intro i hi j hj he
      apply hp.inj i hi j hj
      have he' := congrArg (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id) he
      simpa only [hmap i hi,hmap j hj] using he'
    · intro i hi
      exact hreal i (by omega) (i+1) (by omega) (hp.step i hi).ne (hstep i hi)
    · intro i j hij hj hadj
      have hh := (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id).map_adj hadj
      rw [hmap i (by omega),hmap j hj] at hh
      exact hp.no_chord i j hij hj hh
  have hu : ∀ i ≤ n, u ≠ q i := by
    intro i hi he
    apply hv i hi
    have he' := congrArg (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id) he
    simpa only [hmapu,hmap i hi] using he'
  have hu0 : (L2 T).Adj u (q 0) := ⟨hu 0 (by omega), by simpa [u,q,Realizes] using h0⟩
  have hun : (L2 T).Adj u (q n) := ⟨hu n le_rfl, by simpa [u,q,Realizes] using hn⟩
  have hall := ChordalFan.fan _ (forest_L2_eliminates hT) hq hu hu0 hun
  intro i hi
  have hh := (L2Map (SimpleGraph.Hom.ofLE hTG) Function.injective_id).map_adj (hall i hi)
  simpa only [hmapu,hmap i hi] using hh

end FanLemma

namespace PartialColouring
variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

theorem tangledAt_shortestPath (φ : PartialColouring (L2 G) F) {v : G.edgeSet} {a b : Colour}
    (h : φ.TangledAt v a b) :
    ∃ (x y : φ.Bicoloured a b) (p : (φ.KempeGraph a b).Walk x y),
      φ.Neighbour v a x.val ∧ φ.Neighbour v b y.val ∧
      p.length = (φ.KempeGraph a b).dist x y := by
  obtain ⟨x,y,hx,hy,hx',hy',hr⟩ := h
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  exact ⟨⟨x,hx'⟩,⟨y,hy'⟩,p,hx,hy,hp⟩

theorem kempePath_induced (φ : PartialColouring (L2 G) F) {a b : Colour}
    {x y : φ.Bicoloured a b} (p : (φ.KempeGraph a b).Walk x y)
    (hp : p.length = (φ.KempeGraph a b).dist x y) :
    ChordalFan.InducedPath (L2 G) (fun i => (p.getVert i).val) p.length := by
  have hi := ChordalFan.shortest_induced p hp
  exact ⟨fun i hi' j hj he => hi.inj i hi' j hj (Subtype.ext he),
    hi.step,hi.no_chord⟩

/-- Lemma 11.48 with a witness forest, not necessarily induced. The shortest
path is between the specified endpoints; no minimization over endpoint choices
is needed. -/
theorem lemma1148 (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ p.length, (p.getVert i).val.val ∈ T.edgeSet)
    (h0 : FanLemma.Realizes T v x.val) (hn : FanLemma.Realizes T v y.val)
    (hstep : ∀ i < p.length, FanLemma.Realizes T (p.getVert i).val (p.getVert (i+1)).val) :
    (∀ i ≤ p.length, (L2 G).Adj v (p.getVert i).val) ∧ φ.DirectAt v a b := by
  have hall := FanLemma.fan_of_forest T hTG hT (φ.kempePath_induced p hp) (v := v)
    (fun i _ he => hv (he.symm ▸ (p.getVert i).prop)) hvT hpT
    (by simpa using h0) (by simpa using hn) hstep
  refine ⟨hall,?_⟩
  have hxy : x ≠ y := by
    intro he
    have hc := congrArg (fun z : φ.Bicoloured a b => φ.colour z.val) he
    exact hab (hx.2.2.symm.trans (hc.trans hy.2.2))
  have hpos : 0 < p.length := by
    by_contra hh
    have hlen : p.length = 0 := by omega
    have he := p.getVert_length
    rw [hlen,SimpleGraph.Walk.getVert_zero] at he
    exact hxy he
  have ha : (L2 G).Adj x.val (p.getVert 1).val := by
    have hh : (L2 G).Adj (p.getVert 0).val (p.getVert 1).val := p.adj_getVert_succ hpos
    simpa using hh
  have hc : φ.colour (p.getVert 1).val = b := by
    rcases (p.getVert 1).prop.2 with hc | hc
    · exact False.elim (φ.proper hx.1 (p.getVert 1).prop.1 ha (hx.2.2.trans hc.symm))
    · exact hc
  exact ⟨x.val,(p.getVert 1).val,hx,⟨(p.getVert 1).prop.1,hall 1 (by omega),hc⟩,ha⟩

/-- In the long case every subgraph retaining the consecutive conflict
witnesses has a cycle; the witnesses need not retain any other conflicts. -/
theorem longChain_witness_cycle (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) (T : SimpleGraph V) (hTG : T ≤ G)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ p.length, (p.getVert i).val.val ∈ T.edgeSet)
    (h0 : FanLemma.Realizes T v x.val) (hn : FanLemma.Realizes T v y.val)
    (hstep : ∀ i < p.length, FanLemma.Realizes T (p.getVert i).val (p.getVert (i+1)).val) :
    ∃ (z : V) (c : T.Walk z z), c.IsCycle := by
  have hn : ¬ T.IsAcyclic := fun hT =>
    hnot (φ.lemma1148 hab hv hx hy p hp T hTG hT hvT hpT h0 hn hstep).2
  simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hn

end PartialColouring

namespace FanLemma
variable {V : Type*} {G : SimpleGraph V}

/-- The induced graph, retaining isolated vertices outside `S` in the type. -/
def span (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem span_le (S : Finset V) : span G S ≤ G := fun _ _ h => h.1

theorem span_support (S : Finset V) {x y : V} (p : (span G S).Walk x y)
    (hx : x ∈ S) : ∀ z ∈ p.support, z ∈ S := by
  induction p with
  | nil => simpa using hx
  | @cons x y z h p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hx
    · exact ih h.2.2 w hw

theorem span_acyclic_of_induce (S : Finset V) (h : (G.induce (↑S : Set V)).IsAcyclic) :
    (span G S).IsAcyclic := by
  intro x c hc
  let d := c.mapLe (span_le S)
  have hd : d.IsCycle := hc.mapLe (span_le S)
  have hs : ∀ z ∈ d.support, z ∈ (↑S : Set V) := by
    simpa [d] using span_support S c (c.adj_snd hc.not_nil).2.1
  apply h (d.induce (↑S : Set V) hs)
  apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce (G := G) (↑S : Set V)).toHom)
  rw [SimpleGraph.Walk.map_induce]
  exact hd

def pathVertices (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ) : Finset V :=
  v.val.toFinset ∪ (Finset.range (n+1)).biUnion (fun i => (p i).val.toFinset)

theorem mem_pathVertices_self (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ)
    {z : V} (hz : z ∈ v.val) : z ∈ pathVertices v p n :=
  Finset.mem_union_left _ (by simpa using hz)

theorem mem_pathVertices_path (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ)
    {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ (p i).val) : z ∈ pathVertices v p n :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr (by omega),by simpa using hz⟩)

theorem pathVertices_card (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ) :
    (pathVertices v p n).card ≤ 2 * (n+2) := by
  have he : ∀ e : G.edgeSet, e.val.toFinset.card = 2 := fun e =>
    Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeSet e.prop)
  have h1 := Finset.card_union_le v.val.toFinset ((Finset.range (n+1)).biUnion (fun i => (p i).val.toFinset))
  have h2 := Finset.card_biUnion_le (s := Finset.range (n+1)) (t := fun i => (p i).val.toFinset)
  simp only [he,Finset.sum_const,Finset.card_range,smul_eq_mul] at h1 h2
  unfold pathVertices
  omega

theorem edge_mem_span (S : Finset V) (e : G.edgeSet) (he : ∀ z ∈ e.val, z ∈ S) :
    e.val ∈ (span G S).edgeSet := by
  obtain ⟨x,y,hexy⟩ : ∃ x y, e.val = s(x,y) := Sym2.ind (fun x y => ⟨x,y,rfl⟩) e.val
  rw [hexy,SimpleGraph.mem_edgeSet]
  exact ⟨G.mem_edgeSet.mp (hexy ▸ e.prop),he x (by simp [hexy]),he y (by simp [hexy])⟩

theorem realizes_span (S : Finset V) {e f : G.edgeSet}
    (he : ∀ z ∈ e.val, z ∈ S) (hf : ∀ z ∈ f.val, z ∈ S) (h : (L2 G).Adj e f) :
    Realizes (span G S) e f := by
  obtain ⟨_,x,hx,y,hy,hxy⟩ := h
  exact ⟨x,hx,y,hy,hxy.elim Or.inl (fun h => Or.inr ⟨h,he x hx,hf y hy⟩)⟩

end FanLemma

namespace PartialColouring
variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

theorem lemma1148_span (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hforest : (FanLemma.span G (FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length)).IsAcyclic) :
    (∀ i ≤ p.length, (L2 G).Adj v (p.getVert i).val) ∧ φ.DirectAt v a b := by
  let S := FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length
  have hvs : ∀ z ∈ v.val, z ∈ S := fun _ hz => FanLemma.mem_pathVertices_self _ _ _ hz
  have hps : ∀ i ≤ p.length, ∀ z ∈ (p.getVert i).val.val, z ∈ S :=
    fun i hi _ hz => FanLemma.mem_pathVertices_path _ _ _ hi hz
  apply φ.lemma1148 hab hv hx hy p hp (FanLemma.span G S) (FanLemma.span_le S) hforest
    (FanLemma.edge_mem_span S v hvs)
    (fun i hi => FanLemma.edge_mem_span S _ (hps i hi))
  · apply FanLemma.realizes_span S hvs _ hx.2.1
    simpa using hps 0 (by omega)
  · apply FanLemma.realizes_span S hvs _ hy.2.1
    simpa using hps p.length le_rfl
  · intro i hi
    exact FanLemma.realizes_span S (hps i (by omega)) (hps (i+1) (by omega)) (p.adj_getVert_succ hi)

/-- The induced-forest hypothesis in the question is sufficient. -/
theorem lemma1148_induced (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hforest : (G.induce (↑(FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length) : Set V)).IsAcyclic) :
    (∀ i ≤ p.length, (L2 G).Adj v (p.getVert i).val) ∧ φ.DirectAt v a b :=
  φ.lemma1148_span hab hv hx hy p hp (FanLemma.span_acyclic_of_induce _ hforest)

/-- A long-type shortest Kempe path spans an actual cycle of `G`. All cycle
vertices are endpoints of `v` or of edges listed on the Kempe path. -/
theorem longChain_cycle (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧
      (∀ w ∈ c.support, w ∈ FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length) ∧
      c.length ≤ 2 * (p.length+2) := by
  let S := FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length
  have hn : ¬ (FanLemma.span G S).IsAcyclic :=
    fun h => hnot (φ.lemma1148_span hab hv hx hy p hp h).2
  obtain ⟨z,c,hc⟩ : ∃ (z : V) (c : (FanLemma.span G S).Walk z z), c.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hn
  have hs := FanLemma.span_support S c (c.adj_snd hc.not_nil).2.1
  have hlen : c.length ≤ S.card := by
    calc
      c.length = c.support.tail.toFinset.card := by
        rw [List.toFinset_card_of_nodup hc.support_nodup]
        simp
      _ ≤ S.card := Finset.card_le_card (fun w hw => hs w (List.mem_of_mem_tail (List.mem_toFinset.mp hw)))
  refine ⟨z,c.mapLe (FanLemma.span_le S),hc.mapLe _,?_,?_⟩
  · simpa using hs
  · simpa using hlen.trans (FanLemma.pathVertices_card v (fun i => (p.getVert i).val) p.length)

/-- Division-free girth bound. Here `p.length` counts Kempe steps; the number
of original edges on `P` is `p.length + 1`. -/
theorem longChain_girth (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    g ≤ 2 * ((p.length+1)+1) := by
  obtain ⟨z,c,hc,_,hlen⟩ := φ.longChain_cycle hab hv hx hy p hp hnot
  have hgc : g ≤ c.length := by exact_mod_cast hg.trans hc.egirth_le_length
  omega

theorem longChain_girth_half (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    (g : ℚ) / 2 - 1 ≤ ((p.length+1 : ℕ) : ℚ) := by
  have hh : (g : ℚ) ≤ 2 * (((p.length+1 : ℕ) : ℚ)+1) := by
    exact_mod_cast φ.longChain_girth hab hv hx hy p hp hnot hg
  linarith

end PartialColouring
end Se20Insertion
