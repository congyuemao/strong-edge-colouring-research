# Fourth pass: the fan lemma and the bound 87

## Flaws and qualifications first

**The bare edge union `v ∪ P` need not contain a cycle.** The cycle conclusion is correct for the graph induced on its endpoints, or for the union with one chosen edge realizing each conflict that does not come from a shared endpoint. These interpretations must not be conflated.

A concrete example is the 10-cycle, with edges `e₀,…,e₉` in cyclic order. Set `v=e₀`, colour `e₂,e₆` with `a`, colour `e₄,e₈` with `b`, and leave the other edges uncoloured. This is a proper partial colouring of `L2(C₁₀)`. The `(a,b)` graph is exactly the path

```text
e₂ — e₄ — e₆ — e₈.
```

The only coloured neighbours of `v` are `e₂` and `e₈`, which do not conflict. Thus this is a long-type tangled pair. Nevertheless, the five original edges `{e₀,e₂,e₄,e₆,e₈}` form a matching. Adding the five conflict witnesses gives the entire 10-cycle; the induced graph on the ten endpoints is also the entire cycle. The new Lean theorem proves the cycle conclusion in these precise senses, not in the bare edge union.

**The length convention matters.** If `m=|P|` counts original edges of `G` listed on the Kempe path, the requested bound is `g ≤ 2(m+1)`, equivalently `m ≥ g/2−1`. Lean's `p.length` counts Kempe steps, so `m=p.length+1` and the checked inequality is `g ≤ 2(p.length+2)`. The example above has `m=4`, three Kempe steps, and girth 10: it attains the bound for `m` and disproves the bound `p.length ≥ g/2−1`. The document's wording is valid if its count means edges of `G` on the path; otherwise it is off by one.

**The unqualified equality 87 remains false.** Maximum degree at most 4 and girth at least 7 imply an upper bound, as requested here. For example, `C₈` has only three edges in the conflict neighbourhood of an edge. No equality under these weaker hypotheses is asserted. This is the qualification already identified in `REPORT3.md`.

**Lemma 11.48 itself is correct, and its induced-tree hypothesis is unnecessarily strong.** It is enough that a subgraph `T ≤ G` is a forest, contains `v` and every original edge listed on `P`, and retains a conflict witness for each consecutive pair in `v,P,v`. The proof does not require `G[V(T)]=T`, connectedness, finiteness of `G` or `T`, or retention of any other conflicts. The path only needs to be induced in `L2 G`; being shortest between its specified Kempe endpoints implies that property. No shortest-choice condition over all possible endpoint pairs is needed.

## Results and files

All four requested parts are implemented. No pre-existing theorem statement was changed.

| File | Contents |
|---|---|
| [ForestL2.lean](Se20Insertion/ForestL2.lean) | Root each forest component, define edge height, prove lower-height neighbours form a clique, and obtain a simplicial edge in every finite nonempty set. |
| [ChordalFan.lean](Se20Insertion/ChordalFan.lean) | Indexed induced paths, the fan theorem for an elimination rank, shortest-path inducedness, and `forest_L2_chordal`: every indexed induced cycle has length 3. |
| [Neighbourhood87.lean](Se20Insertion/Neighbourhood87.lean) | At most six near neighbours; local degrees at most 14 or 5; at most 87 neighbourhood edges; unordered direct colour pairs and their bound 87. |
| [FanLemma.lean](Se20Insertion/FanLemma.lean) | Transfer through a witness forest, the actual partial-colouring/Kempe-path version of Lemma 11.48, its induced-forest specialization, cycles in the long case, and both integer and rational girth inequalities. |
| [AxiomAudit.lean](Se20Insertion/AxiomAudit.lean) | Adds 22 audits to the existing 65. |
| [build.ps1](build.ps1) | Adds the four modules in dependency order before the audit. |

The existing root module imports `AxiomAudit`, so it also imports all four new modules.

The numerical statements retain `[Fintype V]` from the existing `MaxDegreeFour` interface. The forest chordality, fan, cycle, and girth statements do not require a finite ambient graph.

## Proof details and scope

For chordality, choose one root per forest component and give an edge the larger distance of its two endpoints from the root. Adjacent vertices have depths differing by one, and a vertex has at most one neighbour of smaller depth. For an edge `e=pc` with `c` deeper, every conflicting edge of height at most that of `e` contains either `p` or the parent of `p`. Hence any two such edges conflict. This is an elimination rank, including for infinite forests. In particular, any nonempty finite edge set has a simplicial member of maximal height.

The abstract fan proof works on an indexed induced path. A vertex of maximum rank on that path cannot be internal, since its predecessor and successor would conflict. If `v` has still larger rank, the two endpoints conflict and the induced path has one step. Otherwise remove a maximal endpoint: its next vertex conflicts with `v`, and induction applies. Applied to an induced cycle with one vertex removed, the fan theorem gives a forbidden chord unless the cycle is a triangle. `forest_L2_chordal` explicitly states that cycle conclusion.

For a witness forest `T`, retain only the consecutive path conflicts and the two attachments to `v`. The path is still induced in `L2 T`, since every conflict in `T` is a conflict in `G`. The fan theorem supplies all the missing adjacencies to `v` in `L2 T`, and these transfer to `L2 G`. For the two-colour conclusion, the first step of the path leaves its `a` endpoint for a `b` vertex by properness. Both are neighbours of `v` and conflict with each other.

`v ∉ φ.Bicoloured a b` is the exact not-coloured-`a,b` condition: it includes an uncoloured `v` and ignores its unused colour value. The uncoloured vertices elsewhere in `G` never enter the Kempe graph. The colour-level theorems assume `a ≠ b`. The graph-level theorem needs no colouring at all and only assumes `v` is absent from the path.

The chosen realizing edges add no new vertices: each joins an endpoint of one listed edge to an endpoint of the next. Thus the vertex set of `E'` in the question is exactly `pathVertices v p n`. `lemma1148_induced` uses `G.induce` on that precise set. More strongly, `longChain_witness_cycle` proves that **every** subgraph retaining the required edges and witnesses has a cycle when there is no direct pair. Taking the induced endpoint graph gives an actual cycle of `G` whose vertices all lie in `pathVertices`. Its length is at most the number of those vertices, which is at most `2(m+1)`. No degree assumption is used in any of these results.

For the numerical bound, `neighbourhoodGraph G v` is literally `L2 G` induced on the full open conflict neighbourhood of `v`. The existing `common_near_card` and `common_far_card` concern closed neighbourhoods. Applying them to the local neighbours of `w` **together with `w` itself** gives the checked open-degree bounds 14 and 5. With `n ≤ 24` and `t ≤ 6`, the handshake identity gives

```text
2 |E(L2[N(v)])| ≤ 14t + 5(n−t) = 5n + 9t ≤ 174.
```

`directPairs` counts unordered colour pairs, not ordered pairs or witnesses with multiplicity. Properness forces the two colours in a direct witness to be distinct. Mapping each neighbourhood edge to its endpoint-colour pair covers every direct pair; the size of that image is at most the number of neighbourhood edges. `directAt_tangled` separately verifies that a direct witness is indeed a tangled pair. The bound applies to every partial colouring, with no stuckness or regularity hypothesis.

## Exact Lean statements

The following declarations are copied from the sources with theorem proof bodies omitted. All sections are noncomputable and use `open scoped Classical`. The ambient variables for each group are shown; `Colour` remains the existing `Fin 20`.

```lean
namespace Se20Insertion.ForestL2

variable {V : Type*} {G : SimpleGraph V}

def height (G : SimpleGraph V) (e : G.edgeSet) : ℕ :=
  e.val.lift ⟨fun x y => max (depth G x) (depth G y), fun _ _ => max_comm _ _⟩

theorem exists_simplicial (hG : G.IsAcyclic) (S : Finset G.edgeSet) (hS : S.Nonempty) :
    ∃ e ∈ S, ∀ f ∈ S, ∀ k ∈ S, (L2 G).Adj e f → (L2 G).Adj e k →
      f ≠ k → (L2 G).Adj f k

end Se20Insertion.ForestL2
```

```lean
namespace Se20Insertion.ChordalFan

variable {W : Type*} {H : SimpleGraph W}

structure InducedPath (H : SimpleGraph W) (p : ℕ → W) (n : ℕ) : Prop where
  inj : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j
  step : ∀ i < n, H.Adj (p i) (p (i+1))
  no_chord : ∀ i j, i+1 < j → j ≤ n → ¬ H.Adj (p i) (p j)

def Eliminates (H : SimpleGraph W) (r : W → ℕ) : Prop :=
  ∀ v x y, r x ≤ r v → r y ≤ r v → H.Adj v x → H.Adj v y → x ≠ y → H.Adj x y

theorem fan (r : W → ℕ) (hr : Eliminates H r) {n : ℕ} {p : ℕ → W}
    (hp : InducedPath H p n) {v : W} (hv : ∀ i ≤ n, v ≠ p i)
    (h0 : H.Adj v (p 0)) (hn : H.Adj v (p n)) :
    ∀ i ≤ n, H.Adj v (p i)

theorem shortest_induced {x y : W} (p : H.Walk x y) (hp : p.length = H.dist x y) :
    InducedPath H p.getVert p.length

end Se20Insertion.ChordalFan

namespace Se20Insertion

theorem forest_L2_chordal {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {n : ℕ} (hn : 3 ≤ n) (p : ℕ → G.edgeSet)
    (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hstep : ∀ i < n-1, (L2 G).Adj (p i) (p (i+1)))
    (hclose : (L2 G).Adj (p 0) (p (n-1)))
    (hchord : ∀ i j, i+1 < j → j < n → (i ≠ 0 ∨ j ≠ n-1) →
      ¬ (L2 G).Adj (p i) (p j)) : n = 3

end Se20Insertion
```

```lean
namespace Se20Insertion.FanLemma

variable {V : Type*} {G : SimpleGraph V}

def Realizes (T : SimpleGraph V) (e f : G.edgeSet) : Prop :=
  ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ T.Adj a b

theorem fan_of_forest (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsAcyclic)
    {p : ℕ → G.edgeSet} {n : ℕ} (hp : ChordalFan.InducedPath (L2 G) p n)
    {v : G.edgeSet} (hv : ∀ i ≤ n, v ≠ p i)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ n, (p i).val ∈ T.edgeSet)
    (h0 : Realizes T v (p 0)) (hn : Realizes T v (p n))
    (hstep : ∀ i < n, Realizes T (p i) (p (i+1))) :
    ∀ i ≤ n, (L2 G).Adj v (p i)

def pathVertices (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ) : Finset V :=
  v.val.toFinset ∪ (Finset.range (n+1)).biUnion (fun i => (p i).val.toFinset)

theorem pathVertices_card (v : G.edgeSet) (p : ℕ → G.edgeSet) (n : ℕ) :
    (pathVertices v p n).card ≤ 2 * (n+2)

end Se20Insertion.FanLemma
```

```lean
namespace Se20Insertion.PartialColouring

variable {V : Type*} {G : SimpleGraph V} {F : Finset G.edgeSet}

theorem tangledAt_shortestPath (φ : PartialColouring (L2 G) F) {v : G.edgeSet} {a b : Colour}
    (h : φ.TangledAt v a b) :
    ∃ (x y : φ.Bicoloured a b) (p : (φ.KempeGraph a b).Walk x y),
      φ.Neighbour v a x.val ∧ φ.Neighbour v b y.val ∧
      p.length = (φ.KempeGraph a b).dist x y

theorem lemma1148 (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsAcyclic)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ p.length, (p.getVert i).val.val ∈ T.edgeSet)
    (h0 : FanLemma.Realizes T v x.val) (hn : FanLemma.Realizes T v y.val)
    (hstep : ∀ i < p.length, FanLemma.Realizes T (p.getVert i).val (p.getVert (i+1)).val) :
    (∀ i ≤ p.length, (L2 G).Adj v (p.getVert i).val) ∧ φ.DirectAt v a b

theorem longChain_witness_cycle (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) (T : SimpleGraph V) (hTG : T ≤ G)
    (hvT : v.val ∈ T.edgeSet) (hpT : ∀ i ≤ p.length, (p.getVert i).val.val ∈ T.edgeSet)
    (h0 : FanLemma.Realizes T v x.val) (hn : FanLemma.Realizes T v y.val)
    (hstep : ∀ i < p.length, FanLemma.Realizes T (p.getVert i).val (p.getVert (i+1)).val) :
    ∃ (z : V) (c : T.Walk z z), c.IsCycle

theorem lemma1148_induced (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hforest : (G.induce (↑(FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length) : Set V)).IsAcyclic) :
    (∀ i ≤ p.length, (L2 G).Adj v (p.getVert i).val) ∧ φ.DirectAt v a b

theorem longChain_cycle (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧
      (∀ w ∈ c.support, w ∈ FanLemma.pathVertices v (fun i => (p.getVert i).val) p.length) ∧
      c.length ≤ 2 * (p.length+2)

theorem longChain_girth (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    g ≤ 2 * ((p.length+1)+1)

theorem longChain_girth_half (φ : PartialColouring (L2 G) F) {a b : Colour} (hab : a ≠ b)
    {v : G.edgeSet} (hv : v ∉ φ.Bicoloured a b)
    {x y : φ.Bicoloured a b} (hx : φ.Neighbour v a x.val) (hy : φ.Neighbour v b y.val)
    (p : (φ.KempeGraph a b).Walk x y) (hp : p.length = (φ.KempeGraph a b).dist x y)
    (hnot : ¬ φ.DirectAt v a b) {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    (g : ℚ) / 2 - 1 ≤ ((p.length+1 : ℕ) : ℚ)

end Se20Insertion.PartialColouring
```

```lean
namespace Se20Insertion.GirthGeometry

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def nearNeighbours (v : G.edgeSet) : Finset G.edgeSet :=
  (conflicts G v).filter (fun w => ∃ a, a ∈ v.val ∧ a ∈ w.val)

def neighbourhoodGraph (v : G.edgeSet) := (L2 G).induce (↑(conflicts G v) : Set G.edgeSet)

theorem nearNeighbours_card (hΔ : MaxDegreeFour G) (v : G.edgeSet) :
    (nearNeighbours G v).card ≤ 6

theorem neighbourhood_degree (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (v : G.edgeSet) (w : (↑(conflicts G v) : Set G.edgeSet)) :
    (neighbourhoodGraph G v).degree w ≤
      if w.val ∈ nearNeighbours G v then 14 else 5

theorem neighbourhood_edges_le_87 (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth)
    (v : G.edgeSet) : Nat.card (neighbourhoodGraph G v).edgeSet ≤ 87

end Se20Insertion.GirthGeometry
```

```lean
namespace Se20Insertion.PartialColouring

variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def DirectAt (φ : PartialColouring H F) (v : W) (a b : Colour) : Prop :=
  ∃ x y, φ.Neighbour v a x ∧ φ.Neighbour v b y ∧ H.Adj x y

def directPairs (φ : PartialColouring H F) (v : W) : Finset (Sym2 Colour) :=
  Finset.univ.filter (fun c => ∃ a b, c = s(a,b) ∧ φ.DirectAt v a b)

theorem directAt_tangled (φ : PartialColouring H F) {v : W} {a b : Colour}
    (h : φ.DirectAt v a b) : φ.TangledAt v a b

theorem directPairs_le_neighbourhood_edges {V : Type*} [Fintype V]
    {G : SimpleGraph V} {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (v : G.edgeSet) : (φ.directPairs v).card ≤
      Nat.card (GirthGeometry.neighbourhoodGraph G v).edgeSet

theorem directPairs_le_87 {V : Type*} [Fintype V]
    {G : SimpleGraph V} {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hΔ : MaxDegreeFour G) (hg : 7 ≤ G.egirth) (v : G.edgeSet) :
    (φ.directPairs v).card ≤ 87

end Se20Insertion.PartialColouring
```

## Validation and axiom audit

The final `./build.ps1` run exited with code **0**. It rebuilt every existing module, all four new modules, `AxiomAudit.lean`, and the root `Se20Insertion.lean` import. The complete output is [BUILD4.log](BUILD4.log). The toolchain remains `leanprover/lean4:v4.35.0-rc4`. Existing modules emit linter/deprecation warnings; the four new modules emit no warnings or errors in this run.

The source scan

```powershell
rg -n '\b(sorry|admit|axiom|native_decide|ofReduceBool)\b' Se20Insertion -g '*.lean'
```

returned no matches (ripgrep exit code 1). No new axiom declarations or proof placeholders were introduced. All **87** audited declarations, including the **22** additions, depend exactly on `propext`, `Classical.choice`, and `Quot.sound`. The full exact audit output is [AXIOMS4.txt](AXIOMS4.txt). Below is the exact output for the 22 additions, preserving Lean's line breaks.

```text
'Se20Insertion.ForestL2.lower_neighbours_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ForestL2.exists_simplicial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ChordalFan.fan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.ChordalFan.shortest_induced' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.forest_L2_eliminates' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.forest_L2_chordal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.FanLemma.fan_of_forest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.tangledAt_shortestPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.lemma1148' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.longChain_witness_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.lemma1148_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.lemma1148_induced' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.FanLemma.pathVertices_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.longChain_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.longChain_girth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.longChain_girth_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.nearNeighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.neighbourhood_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.GirthGeometry.neighbourhood_edges_le_87' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.directAt_tangled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Se20Insertion.PartialColouring.directPairs_le_neighbourhood_edges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Se20Insertion.PartialColouring.directPairs_le_87' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is not done

No requested theorem is left as a conjecture or a proof placeholder. The equality 87 under additional regularity assumptions was not formalized; this task asks for the upper bound. No explicit finite perfect-elimination permutation is constructed: the checked rank and the explicit induced-cycle theorem supply the requested chordality. The counterexamples above are mathematical descriptions, not additional Lean example definitions. No experiments or computational claims in the reference document were rerun. No claim about Conjectures 11.46, 11.50, or 11.51 beyond the earlier conditional results is added. No outside reviewer or delegated agent was used.
