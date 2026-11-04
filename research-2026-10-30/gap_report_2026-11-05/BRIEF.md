# Brief: close the gap between a counting theorem and insertion (strong edge colouring, Delta = 4, 20 colours)

Open problem: every finite simple graph with maximum degree <= 4 has a strong edge colouring with 20 colours (best published: 21). This is a proof attempt, not a formalization. Be adversarial and honest: a precise failure is useful; a claimed proof with a gap is not. Work only in this directory. Do not push or touch other directories. Nothing may be installed on drive C. At most 4 processes. Python with networkx and pysat is at C:\Users\21161\Documents\ChatGPT\se20-ideas\.venv\Scripts\python.exe (run scripts from this directory with that interpreter; existing helpers are in that se20-ideas folder, read them if useful, do not edit them).

Read reference/NEW_DIRECTIONS_zh.md sections 11.14, 11.17, 11.22, 11.23 and above all 11.24 (Chinese). Summary of 11.24:

Conflict: distinct edges sharing an endpoint or joined by an edge, always judged in the whole graph. A colour is single at x if exactly one coloured neighbour of x has it. Hole move: colour hole x with a colour p single at x, erase the p-neighbour f; f is the new hole. Reversible.

Double move: if a = colour of f is single at g and at w, b = colour of w is single at f, g and w do not conflict, then the hole at g moves to f and then to w, and a is free at w, so the colouring completes.

Theorem 11.44 (proved): G simple 4-regular with girth >= 7, phi a proper 20-colouring of L^2(G) - h. There is no edge set R containing h such that (a) every edge of R sees all colours but its own, (b) x in R and phi(y) single at x imply y in R, (c) no g in R, f, w form a double move in phi. The proof sums over the finite set R: the number of incidences "y non-single at x" is at most 10 per edge, each conflict pair inside R that is not mutually single uses one, and mutually single pairs are limited by c(f) <= s(f)/3; this yields 24 <= 70/3, false. It fails with 19 colours and has no analogue on the infinite tree, which is why it is not blocked by the local obstruction of 11.17.

**The gap.** (c) is stated for the single colouring phi. A real hole walk from h to g recolours the path. If the path passes through f or w, or gives colours a, b to edges near f, w, g, the double move at the end is not available. On the infinite tree, "shadows" are cheap: g can be reached only through f, since a whole subtree has just the near edges as entrance. In a finite graph subtrees close up, and the boundary of a shadow must pay incidences, but this cost is not yet in the inequality. A crude local linear program that ignores the closing is feasible, so the present inequality alone does not finish.

## Your task, in order

1. Try to close the gap: prove that some stuck-free state is reachable, that is, prove insertion by hole moves and Kempe swaps for every state, at least for girth >= 7 and only edge h uncoloured (k = 0). Ideas worth trying, not binding: dominator trees of the digraph x -> y (phi(y) single at x) and counting shadow boundaries; a sink strongly connected component of that digraph; choosing the state in the reachable class that extremizes a potential (number of mutually single pairs, or class sizes); a mass-transport or stationarity argument over the undirected graph of states; adding Kempe swaps of small components to escape shadows.
2. If you cannot close it, find the strongest rigorous statement you can: for instance a theorem of the shape "no state with property X" where X is implied by being stuck in a large explicit class of graphs, or a precise counterexample pattern showing that a route is impossible. Test any candidate numerically on small cases when you can, and try to break it.
3. Also check Theorem 11.44 and report any flaw.

Do not spend effort on Lean. Wall clock limit: about 4 hours (check with Get-Date).

## Output

Write `REPORT.md`: lead with any flaw found, then exactly what is proved, with complete proofs, then what failed and why. Mark each statement as proved, computed, or conjectured. State every hypothesis. Keep it readable; I will verify every step.
