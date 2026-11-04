# Counting, hole walks, and the remaining gap

**[PROVED: audit conclusion.] No substantive flaw was found in Theorem 11.44, with finiteness explicit and (c) interpreted as a pattern in the fixed colouring.** An explicit proof should handle `c(f) = 0` separately before invoking a partner's neighbourhood intersection. In that case the required inequality is immediate. The proof below supplies that case and proves the intersection assertions without relying on numerical checks.

**[PROVED: additional logical issue.] Condition (a), not only condition (c), needs justification when choosing a set from a reachable class.** In general, a coloured vertex that can become the hole need not see all other colours in the original colouring. A six-vertex example below proves this, even when no sequence of hole moves and Kempe swaps can complete the colouring. This is an abstract conflict-graph example, not a counterexample in the required high-girth class.

**[COMPUTED: obstruction within the required class.]** There is a finite simple 4-regular graph of girth 8, with only one edge uncoloured and 20 colours, in which a shortest static singleton path is executable, avoids both partners of a static double move, and nevertheless destroys that double move. The complete state and an independently checked certificate are supplied. Thus shortest paths and avoidance of the two partner vertices alone do not repair the argument.

**[CONJECTURED; not established here.]** Every one-hole state in the requested class can be completed by hole moves and Kempe swaps. I did not prove this, and found no counterexample to it. The results below are an audited counting theorem, a quantitative extension, a constructive sufficient criterion for insertion, and precise limitations of several proposed routes. None is presented as a proof of universal insertion.

All mathematical statements concern finite graphs. No claim about the literature or novelty of these subsidiary results is made.

**Notation and scope.** Write `H = L(G)^2`; its vertices are the edges of the *whole* graph `G`. Adjacency in `H` is always computed in `G`, including when an edge of `G` is uncoloured. Write `x ~ y`, `N(x)`, and `N[x]` for adjacency, open neighbourhood, and closed neighbourhood in `H`. The palette has `q` colours, usually `q = 20`. A state is a proper colouring of `H - h`, with exactly one hole `h`. Let

\[
\mu_x(a)=|\{y\in N(x):\phi(y)=a\}|.
\]

An arc `x -> y` in the **static singleton digraph** means that `y` is coloured, `x ~ y`, and `mu_x(phi(y)) = 1`, all in the original state. A hole move uses the same test in the *current* state. These two usages must not be interchanged.

A **static double** is a triple `(g,f,w)` with `f,w` coloured, `g ~ f ~ w`, `g != w`, `g` not adjacent to `w`, and, putting `a = phi(f)`, `b = phi(w)`,

\[
\mu_g(a)=\mu_w(a)=\mu_f(b)=1.
\]

The root `g` may be coloured in this definition. If it is the actual hole, the two hole moves `g -> f -> w`, followed by filling `w` with `a`, complete the colouring. Equivalently, `{f,w}` is an entire `(a,b)` Kempe component, and swapping that component frees `a` at `g`.

**P1 [PROVED]. Theorem 11.44 is valid.**

Hypotheses: `G` is finite, simple, 4-regular, and has girth at least 7; `phi` is a proper 20-colouring of `H-h`. There is no set `R` containing `h` such that:

1. `h` sees all 20 colours and each coloured vertex in `R` sees all 19 colours other than its own;
2. `R` is closed under the static singleton arcs;
3. no static double has its root in `R`.

*The local geometry.* Fix `f = uv`. Let `A` be the three other edges at `u`, and `B` the three other edges at `v`. For `uu_i in A`, let `X_i` be the three other edges at `u_i`; define the three sets `Y_j` on the `v` side similarly. Put `X = union X_i` and `Y = union Y_j`.

These are disjoint, and

\[
N(f)=A\mathbin{\dot\cup}B\mathbin{\dot\cup}X\mathbin{\dot\cup}Y,
\qquad |N(f)|=3+3+9+9=24.
\]

For a near edge `w in A`,

\[
N(f)\cap N[w]=A\cup B\cup X,
\]

which has size 15. For a far edge `w in X_i`,

\[
N(f)\cap N[w]=A\cup X_i,
\]

which has size 6. The corresponding formulas hold on the other side. A near partner at each end therefore restricts a common intersection to `A union B`, of size 6. These formulas follow by listing shared endpoints and joining edges. Any additional identification or joining edge between the displayed branches would close a cycle of length at most 6 in `G`, forbidden by the girth assumption.

*Counting.* Suppose such an `R` exists. Put `R' = R - {h}`, `n = |R'|`, and `M = |N(h) intersect R'|`. Since 24 neighbours cover 20 colours at `h`, at least 16 neighbours have single colours. Closure gives `M >= 16`, in particular `n > 0`.

For `x in R'`, define:

- `epsilon(x) = 1` if `x ~ h`, and 0 otherwise;
- `d(x) = 24 - epsilon(x)`, the number of coloured neighbours;
- `t(x)`, the number of coloured neighbours outside `R`;
- `y(x)`, the number of `z in R' intersect N(x)` at which `phi(x)` is non-single;
- `ns(x)`, the number of coloured neighbours whose colours are non-single at `x`.

Write `T = sum t(x)` and `Y = sum y(x)`. A multiset of `d` entries using 19 colours has at most `2(d-19)` entries in repeated colour classes: for each multiplicity `r >= 2`, `r <= 2(r-1)`. Thus

\[
ns(x)\le 10-2\epsilon(x).
\]

Every neighbour outside `R` is non-single at `x`, by closure. Internal non-single incidences sum to `Y` after reversing the summation order. Consequently

\[
T+Y\le 10n-2M. \tag{1}
\]

Let `U` be the number of mutually single unordered pairs in `H[R']`. Its total degree is `24n-M-T`. Each pair that is not mutually single contributes at least once to `Y`, so

\[
2U\ge 24n-M-T-2Y. \tag{2}
\]

For `f in R'`, let `c(f)` be its number of mutually single partners in `R'`, set `s(f)=t(f)+y(f)`, and put

\[
N_1(f)=\{g\in R'\cap N(f):\mu_g(\phi(f))=1\}.
\]

Then `|N_1(f)| = d(f)-s(f)`. Every partner lies in `N_1(f)`. For any partner `w`, condition 3 implies `N_1(f) subset N[w]`; otherwise a member outside `N[w]` would root a double.

If `c(f)=0`, the next inequality is immediate. Otherwise, if all partners are near edges at the same end of `f`, then `c(f)<=3` and `|N_1(f)|<=15`. If there is a far partner, or near partners at both ends, then `|N_1(f)|<=6` and `c(f)<=|N_1(f)|<=6`. In both cases,

\[
3c(f)\le s(f)+\epsilon(f),
\]

because `s(f)+epsilon(f)=24-|N_1(f)|`. Summing gives

\[
2U\le (Y+T+M)/3. \tag{3}
\]

Combining (1)--(3),

\[
72n\le 7Y+4T+4M
\le 70n-10M-3T.
\]

Hence `2n+10M+3T <= 0`, impossible. This proves the theorem. Finiteness is used in these sums. No reachability assertion has been used or proved. ∎

**P2 [PROVED]. An exact version counts both saturation defects and exposed partners.**

Keep the graph and colouring hypotheses of P1, but assume only that `h` is blocked and `R` contains `h` and is closed under static singleton arcs. Keep `n,M,T,Y,d,t,y,s,epsilon` from the preceding proof. Define

\[
\delta(x)=19-|\{\phi(z):z\in N(x),\ z\ne h\}|,
\qquad D=\sum_{x\in R'}\delta(x),
\]

and

\[
E=\sum_{x\in R'}\sum_a\max(\mu_x(a)-2,0).
\]

Here `D >= 0` measures failures of saturation; `E >= 0` measures multiplicities above two. Let `Z` count unordered conflict pairs in `R'` that are non-single in *both* directions.

Call an ordered mutually single pair `(f,w)` in `R'` **exposed** if some `g in R` roots the static double `(g,f,w)`. Let `B` count these ordered pairs, counting a pair once regardless of the number of witnesses `g`. Let `c_0(f)` count the partners of `f` that are not exposed in this order. Define

\[
L=\sum_{f\in R'}\bigl(s(f)+\epsilon(f)-3c_0(f)\bigr).
\]

Then `L >= 0`, and the following identity holds:

\[
\boxed{14D+3B=2n+10M+3T+7E+6Z+L.} \tag{4}
\]

In particular, `14D+3B >= 2n+10M+3T`, with `M >= 16`.

*Proof.* Apply the geometric argument of P1 just to the non-exposed partners: each such partner has `N_1(f) subset N[w]`. It proves every summand defining `L` is nonnegative.

Closure gives the exact equality `T+Y = sum ns(x)`. For each vertex, summing the identity `r = 2(r-1)-(r-2)` over multiplicities `r>=2` gives

\[
T+Y=10n-2M+2D-E. \tag{5}
\]

Counting the pairs non-single in both directions corrects (2) to

\[
2U=24n-M-T-2Y+2Z. \tag{6}
\]

Counting all partners as non-exposed or exposed gives

\[
2U=(Y+T+M-L)/3+B. \tag{7}
\]

Equating (6) and (7) and substituting (5) yields (4). ∎

This identity makes two obligations explicit. A genuine stuck class would have to pay for static defects `D` and for exposed partners `B` whose repairs cannot be transported. I obtained no bound on those two terms from stuckness that contradicts (4). Setting both to zero recovers P1.

**P3 [PROVED]. Finite abstract counterexamples to two proposed inferences.**

These statements concern arbitrary conflict graphs `H`, not necessarily squares of line graphs.

First take the 5-cycle on vertices `0,1,2,3,4`, add a hub `5` adjacent to every cycle vertex, and leave the hub uncoloured. Colour the cycle

\[
(1,2,3,1,2).
\]

The hub is blocked. The singleton arcs include

\[
5\to2\to1\to0,
\qquad 2\to3\to4.
\]

Thus the static closure contains all vertices. Vertex `0`, of colour 1, sees only colour 2 and is not saturated. The displayed path to `0` is also a legal sequence of hole moves: its donor colours are `3,2,1`. At its end the hub has acquired colour 3, which vertex `0` now sees. The original missing colour has not survived the walk.

No 3-colouring of this wheel exists: the hub forbids its colour on the odd cycle, which cannot be 2-coloured. Therefore no hole moves or Kempe swaps can complete the state. This disproves the inference from a stuck reachable class to saturation of its static closure, and also disproves it for the union of actually reachable hole positions.

For a second example take the 5-cycle on `0,...,4`, a hub `6` adjacent to all five cycle vertices, and an additional vertex `5` adjacent to `3` and `4`. Leave `6` uncoloured and set

\[
(\phi(0),\ldots,\phi(5))=(1,2,3,1,3,2).
\]

Every coloured vertex sees both other colours. The static arcs

\[
6\to1,\quad 1\to0,2,\quad 0\to4,\quad 2\to3,\quad 3\to5
\]

show that the closure is all seven vertices. Conditions (a) and (b) hold. There is a static double `(g,f,w)=(0,1,2)`, with `a=2`, `b=3`. The hole really can move `6 -> 1 -> 0`. But after this walk, vertex `1` has colour 1 and the hub has colour 2; the original double no longer applies. Again the odd wheel subgraph makes every completion impossible, including after arbitrary Kempe swaps.

Thus even finiteness, (a), (b), existence of a static double, and actual reachability of its root do not constitute an abstract insertion lemma.

Both examples lift to 20 colours by adjoining a clique of 17 vertices, joining it to every old vertex, and giving its vertices 17 fresh colours. In the seven-vertex example the resulting graph has 24 vertices, maximum degree 23, and chromatic number 21. Its one-hole 20-colouring still satisfies (a), (b), and has the same static double. These graphs have large cliques and do not satisfy P1's local geometry. They refute abstract deductions, not the requested conjecture. ∎

**P4 [PROVED]. Saturation is inherited through two static steps, but not in general through three.**

Hypotheses: any finite graph `H`, a proper one-hole `q`-colouring, and no completion by filling after at most two hole moves. Every vertex at static singleton distance at most two from `h` is saturated in the original state, with the usual exception of its own colour.

*Proof.* A one-step target `f` must originally see all colours except `a=phi(f)`: the move only supplies `a` at the new hole. For a simple static two-step path `h -> f -> g`, write `a=phi(f)` and `b=phi(g)`. These differ because `f~g`. The first move changes only colour `a`, so the second singleton test for `b` remains valid. The resulting state has `h=a`, `f=b`, and `g` uncoloured. At `g`, the only newly supplied colours could be `a` and `b`. The former was already present there at `f`, and the latter was its own original colour. Consequently a blocked final hole implies that originally `g` saw every colour other than `b`. The first wheel in P3 gives failure at distance three. ∎

**P5 [PROVED]. A constructive criterion using two fixed colour classes.**

Hypotheses: any finite graph `H`, a proper one-hole `q`-colouring, `q>=2`, and distinct colours `a,b`. Let `A,B` be their colour classes, and let the components of `H[A union B]` be the fixed Kempe components.

Define `S_ab` to consist of the vertices outside `A union B` whose neighbourhood meets both sides of at least one of these components. Thus `v` is outside `S_ab` exactly when `(a,b)` is separable at `v`, allowing a missing colour as a special case. Set

\[
d_{ab}(v)=|N(v)\cap(A\cup B)|,
\qquad
\tau(v)=2(q-2)-\deg_H(v)+d_{ab}(v).
\]

Starting with `S_ab`, repeatedly delete a vertex having fewer than `tau(v)` neighbours in the current set. Call the remaining set `C_ab`.

**If `h` is outside `C_ab`, insertion is possible.** The construction uses hole moves whose donor colours avoid `a,b`, then at most one round of swaps of `(a,b)` components, and a final fill. It needs no more than `|S_ab - C_ab|` hole moves.

*Proof.* The colour classes `A,B`, their components, and `S_ab` remain fixed under the stipulated hole moves. Give the deleted vertices their deletion ranks; vertices initially outside `S_ab` have rank `-1`, and vertices in the core have infinite rank.

Suppose the current hole is `v`. A missing colour permits immediate filling. Otherwise all `q-2` colours other than `a,b` occur on its `deg_H(v)-d_ab(v)` neighbours of those colours. At least

\[
2(q-2)-(\deg_H(v)-d_{ab}(v))=\tau(v)
\]

of those neighbours have single colours. Each is a legal hole-move target outside `A union B`.

If `v` has a finite nonnegative deletion rank, it has fewer than `tau(v)` neighbours of greater or equal rank: that was the deletion test. Therefore some legal target has smaller rank. Move there. Ranks strictly decrease, so either a free colour occurs or the hole reaches a vertex outside `S_ab`.

In the latter case no fixed `(a,b)` component meets both its `a`-neighbours and its `b`-neighbours. Swap all components meeting its `a`-neighbours. No `b`-neighbour is swapped, so colour `a` is now absent at the hole. Fill it. Every operation was legal. ∎

For the graph class in P1,

\[
\tau(v)=12+d_{ab}(v)\ge14\quad(v\in S_{ab}).
\]

In particular, a 13-degenerate `H[S_ab]` suffices. The variable threshold is stronger than this uniform version. Any genuinely stuck class must have `h in C_ab` for every colour pair in every reachable state. This is a necessary condition for stuckness, not a theorem that such cores cannot occur.

The same proof explains the benefit over the original static digraph: only the two fixed colour classes enter the definition of `S_ab`; they do not change during the walk. The decreasing rank is evaluated on a fixed graph, while every singleton test is evaluated in the current colouring.

**P6 [PROVED]. A finite structural obstruction to making every fixed pair useful.**

Let `t>=1`. Suppose a finite simple graph `G` has a partition into sets

\[
|C|=t,\qquad |L|=|U|=2t.
\]

Each centre `c in C` has two private neighbours in `L` and two private neighbours in `U`; these stars partition `L union U`. The remaining edges form a simple 3-regular bipartite graph between `L` and `U`. Assume girth at least 7. Then `G` is 4-regular.

Colour the two `C-L` edges at each centre with `a,b`. They form isolated two-vertex components in the conflict graph induced by these two colours: distinct stars have no joining edge between the endpoints of their `C-L` edges.

Assume all remaining edges except a hole `h` are properly coloured from the other 18 colours. For this fixed pair:

1. `S_ab` is exactly the set of all `C-U` and `L-U` edges, of size `8t`.
2. Its variable-threshold core is all of `S_ab`.
3. No hole walk avoiding donor colours `a,b`, even interspersed with `(a,b)` component swaps, can open colour `a` or `b`, or make that pair separable at the hole.

*Proof.* A `C-U` edge sees both `C-L` edges at its centre. An `L-U` edge sees both `C-L` edges at the centre owning its `L` endpoint, one directly and the other through the first. Thus every remaining edge sees both sides of an isolated `(a,b)` component, proving 1.

A `C-U` edge has exactly five fixed-colour neighbours: the two at its centre and the three `C-L` edges belonging to the three `L`-neighbours of its `U` endpoint. An `L-U` edge has exactly six: two at the centre owning its `L` endpoint, two at the centre owning its `U` endpoint, and one for each of the other two `L`-neighbours of that `U` endpoint. Girth at least 7 prevents identifications in these lists. Since total conflict degree is 24, the degrees and thresholds are

| Edge type | Number | `d_ab` | Degree inside `S_ab` | `tau=12+d_ab` |
|---|---:|---:|---:|---:|
| `C-U` | `2t` | 5 | 19 | 17 |
| `L-U` | `6t` | 6 | 18 | 18 |

No vertex can be deleted, proving 2. A permitted hole move never erases a fixed-colour edge, so the hole stays in `S_ab`. Swapping a pair merely exchanges the two colours at its centre; every remaining edge still sees both colours in the same component. This proves 3. ∎

**[PROVED.] These graphs nevertheless have strong colourings with 17 colours.** The `C-L` edges use two colours, and the `C-U` edges use another two. Within either family the conflict graph is a disjoint union of pairs. For the `L-U` edges, conflicts judged in the whole graph are exactly conflicts in the cubic bipartite remainder: an additional joining edge would need both endpoints in `L union U`, and those edges are precisely the remainder. Its conflict graph has maximum degree at most 12 and can be greedily coloured with 13 new colours. The palettes are disjoint, giving `2+2+13=17`. This argument is about existence of a colouring, not reachability from an arbitrary state.

**[COMPUTED.]** [paired_shadow_1.json](paired_shadow_1.json) realizes P6 with `t=40`: 200 vertices, 400 edges, girth 7, and a proper blocked one-hole 20-colouring. Its `(0,1)` core has 320 vertices. The state inserts after one hole move using other colours. Thus this is an actual finite obstruction to the *fixed-pair route*, not to insertion. The certificate also shows that small Kempe components alone cannot force every fixed-pair core to empty.

**P7 [PROVED]. What a class-size extremum and stationarity actually imply.**

These facts hold for any finite conflict graph. Suppose a reachable class under hole moves and Kempe swaps contains no completable state. Choose a state maximizing

\[
\Phi=\sum_{a=1}^q n_a^2,
\]

where `n_a` is the size of colour class `a`. Hole moves preserve `Phi`.

For `n_a>=n_b`, every `(a,b)` component has colour imbalance `d = number of a vertices - number of b vertices` satisfying

\[
0\le d\le n_a-n_b. \tag{8}
\]

Indeed, swapping it changes the potential by `2d(d-(n_a-n_b))`, which must be nonpositive. In particular, equal-size colour classes have only balanced components. An isolated vertex of the larger colour consumes one unit of the total imbalance, so the total number of missing-colour incidences at coloured vertices satisfies

\[
D_{\rm all}\le\sum_{a<b}|n_a-n_b|. \tag{9}
\]

To see (9), for each pair only the larger class can have isolated vertices, by (8), and their number is at most its total surplus over the smaller class. Missing-colour incidences are exactly these isolated vertices, summed over pairs.

If a vertex `g` of colour `c` can be recoloured to `a` by a singleton Kempe swap, maximality gives `n_a <= n_c-1`, since the potential change is `2(n_a-n_c+1)`. The same conclusion holds for a static double `(g,f,w)` with `g` coloured and `a=phi(f)`: first swap the balanced component `{f,w}`, then recolour `g` to `a`. Thus an extremum does not eliminate all static doubles; it restricts their transfers to a smaller target class. No contradiction between these restrictions and (4) was obtained.

For stationarity, take just a finite hole-move component with no free-colour state, and let `R_*` be its set of possible hole positions. If `H` has maximum degree at most `D_0`, then

\[
\delta(H[R_*])\ge 2q-D_0. \tag{10}
\]

For each `x in R_*`, choose a state whose hole is `x`. Its blocked hole has at least `2q-deg_H(x)` single neighbours. All are legal targets in `R_*`, proving (10). Here this lower bound is 16. Uniform counting over the state component also gives equal transition counts from `x` to `y` and from `y` to `x`, by reversibility. These assertions involve different colourings at different hole positions. They do not imply (a) or (c) in a single colouring; P3 demonstrates the distinction. ∎

**[COMPUTED.] Certificate for failure of shortest-path transport in the required graph class.**

The main certificate is [gq_hard_shortest_transport.json](gq_hard_shortest_transport.json). Its graph has 80 vertices, 160 edges, is simple and 4-regular, and has girth 8. Colours are numbered `0,...,19`; edge indices refer to the file's edge array. The initial hole is edge 0, all 20 colours occur around it, and no one-step hole move gives a free colour. The shortest number of hole moves to *some* free-colour state is two.

The following particular path is shortest in the original static singleton digraph, is executable, and avoids both partners:

\[
h=0\ \longrightarrow\ x=15\ \longrightarrow\ g=154.
\]

The original static double has `(g,f,w)=(154,57,114)` and `(a,b)=(18,2)`.

| Role | Edge index | Edge of `G` | Original colour | Colour after the path |
|---|---:|---|---:|---:|
| `h` | 0 | `0-40` | hole | 2 |
| `x` | 15 | `9-43` | 2 | 13 |
| `g` | 154 | `20-78` | 13 | hole |
| `f` | 57 | `14-54` | 18 | 18 |
| `w` | 114 | `21-68` | 2 | 2 |

Initially `(mu_g(a),mu_w(a),mu_f(b))=(1,1,1)`. Afterwards these multiplicities are `(1,1,2)`: `h`, which conflicts with `f`, has acquired colour `b`. Neither partner was visited. The first move of the proposed double is still possible, but its second move is not. All these assertions were checked using a separate implementation of the conflict graph and replay of the actual moves.

This refutes the proposed transport lemma even with a shortest executable static path avoiding `f,w`. It does not assert that every path to `g` fails, or that the state is stuck. In fact, the initial hole already has 65 separable colour pairs, so it is not Kempe-stuck. The separate completion certificate [gq_hard_shortest_trace.json](gq_hard_shortest_trace.json) inserts using one hole move, one Kempe component swap, and a fill. This example tests the transport assertion, not the difficulty of finding some insertion.

**[COMPUTED.] Numerical audit and reproduction.**

The files contain full edge lists and colourings, not just hashes or aggregate scores. `IndependentVerifier.cs` builds the line graph from shared endpoints and squares it. The generator instead uses the endpoint-or-joining-edge definition directly. The independent verifier checks regularity, simplicity, girth by edge-deletion distance searches, properness, the hole-move and Kempe certificates, static distances, and fixed-pair cores.

| State | Vertices of `G` | Girth | Minimum hole moves to a free colour | Initially separable pairs | Pairs certified by P5 | Largest pair core |
|---|---:|---:|---:|---:|---:|---:|
| `gq_hunt_1.json` | 80 | 8 | 2 | 66 | 190/190 | 0 |
| `gq_hard_shortest.json` | 80 | 8 | 2 | 65 | 190/190 | 0 |
| `paired_shadow_1.json` | 200 | 7 | 1 | 107 | 189/190 | 320 |

For `gq_hard_shortest.json`, the static closure is all 160 edges. Identity (4) has

\[
(n,M,T,D,B,E,Z,L)=(159,24,0,480,635,248,706,2095),
\]

and both sides are 8625. For `paired_shadow_1.json`, the values are

\[
(355,23,991,1609,1005,994,1553,5352),
\]

and both sides are 25541. This also illustrates why saturation cannot simply be assumed for the static closure of an otherwise difficult-looking initial state.

The local geometry in P1 was checked at every edge of the 80-vertex graph: 960 ordered near pairs, 2880 ordered far pairs, and 1440 choices of near partners at opposite ends, with no failure. Thirty additional blocked states made by randomized greedy colouring on that graph had all 190 pair cores empty; each inserted after one hole move. These are easy samples, not adversarial evidence for universal insertion.

An exhaustive enumeration of small abstract graphs found the two wheel-based obstructions. For the seven-vertex graph, the closed state component under hole moves and Kempe swaps has 12 states after identifying global colour permutations; these states are listed in `atlas_counterexample_k3_kempe_double.json`. Its non-completability also has the elementary odd-wheel proof in P3, so it does not depend on trusting that enumeration.

A 180-second stochastic attempt to saturate every coloured vertex of the 80-vertex graph did not find a solution. Its best objective was 322, where the objective was three times the number of monochromatic conflict pairs plus the number of missing colours in the required closed neighbourhoods. This is only a failed search, not evidence of unsatisfiability.

Run from this directory in PowerShell:

```powershell
.\verify_artifacts.ps1
.\run_experiments.ps1 -Mode geometry
.\run_experiments.ps1 -Mode audit -InputFile gq_hard_shortest.json
.\run_experiments.ps1 -Mode audit -InputFile paired_shadow_1.json
```

To regenerate the principal examples:

```powershell
.\search_shortest.ps1 -FirstSeed 3 -LastSeed 3
.\run_experiments.ps1 -Mode paired -Centres 40 -Seed 1
.\run_experiments.ps1 -Mode audit -InputFile gq_hard_shortest.json
.\run_experiments.ps1 -Mode audit -InputFile paired_shadow_1.json
```

The graph generators are deterministic for the supplied seeds on the runtime used here. Verification of the saved certificates does not depend on regenerating them. `run_atlas.ps1 -Colours 3 -Kempe -DoubleOnly` reproduces the abstract seven-vertex example. The atlas reader uses the already installed NetworkX atlas data, read-only.

The supplied Python launcher failed because Windows denied execution of its base interpreter. No installation was attempted. The executed computations therefore use C# compiled by PowerShell, with temporary directories set to this workspace. `exploratory.py` is an unexecuted Python draft and is not evidence for any reported result. All created files are in this directory; no push, Lean work, or edits to the helper directory were performed.

**What failed, and the remaining mathematical obligation.**

**[PROVED failure of an inference.]** Using the static closure or a sink strongly connected component as the actual reachable set does not justify saturation in the original colouring. The first example in P3 has unsaturated singleton sinks inside a stuck static closure. P4 supplies saturation only through distance two; I found no argument extending it to arbitrary depth in the required class.

**[COMPUTED failure of a transport rule.]** Choosing a shortest static path and avoiding `f,w` does not preserve a double. The girth-8 certificate gives the precise contamination mechanism. An argument based on dominators of partner *vertices* alone misses this mechanism; it must also control transported colours near the partners.

**[PROVED limitation of the fixed-pair route.]** P6 closes the local pattern into an actual finite high-girth graph, while every two-colour component of the selected pair remains a single edge. Its entire variable-threshold core survives. Therefore a proof using P5 must select a useful pair, combine information from different pairs, or introduce operations beyond keeping that pair fixed. Finiteness and small components do not by themselves make an arbitrary pair useful.

**[PROVED limitation of the chosen potential argument.]** The quadratic potential supplies (8), (9), and strict class-size inequalities for exposed transfers. It does not force `D=B=0`; transfers to smaller classes remain possible. I could not combine those inequalities with (4) to get a contradiction.

**[PROVED limitation of the stationarity calculation obtained here.]** Reversible transition counts and (10) concern state-dependent singleton relations. Substituting those marginals into P1 would replace a fixed-colouring hypothesis by an averaged one without proof. No estimate controlling that replacement was established.

**[CONJECTURED; still open in this report.]** A stuck reachable class in the specified finite high-girth graph class cannot exist. To complete this route, one still needs a valid inequality bounding the saturation defects and unusable exposed partners in (4), or a proof that some reachable state and some colour pair pass P5, or another genuine insertion mechanism. The present work proves none of those universal assertions.
