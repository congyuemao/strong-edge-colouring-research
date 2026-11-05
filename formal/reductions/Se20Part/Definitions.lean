import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

/-! All conflicts in this development are in the fixed ambient graph. -/
noncomputable section
open scoped Classical

namespace Se20Part

abbrev Colour := Fin 20

/-- The conflict graph on actual unordered edges of the ambient graph. -/
def L2 {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ a ∈ e.val, ∃ b ∈ f.val, a = b ∨ G.Adj a b
  symm := ⟨by
    rintro e f ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha,
      hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def StrongColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (L2 G).Colorable k

/-- Values outside `F` are unused. Properness refers to the ambient graph `H`. -/
structure PartialColouring {W : Type*} (H : SimpleGraph W) (F : Finset W) where
  colour : W → Colour
  proper : ∀ ⦃x y⦄, x ∈ F → y ∈ F → H.Adj x y → colour x ≠ colour y

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

def Neighbour (φ : PartialColouring H F) (f : W) (a : Colour) (g : W) : Prop :=
  g ∈ F ∧ H.Adj f g ∧ φ.colour g = a

def Free (φ : PartialColouring H F) (f : W) (a : Colour) : Prop :=
  ¬ ∃ g, φ.Neighbour f a g

def Single (φ : PartialColouring H F) (f : W) (p : Colour) (g : W) : Prop :=
  φ.Neighbour f p g ∧ ∀ g', φ.Neighbour f p g' → g' = g

def Bicoloured (φ : PartialColouring H F) (a b : Colour) : Set W :=
  {g | g ∈ F ∧ (φ.colour g = a ∨ φ.colour g = b)}

def KempeGraph (φ : PartialColouring H F) (a b : Colour) :
    SimpleGraph (φ.Bicoloured a b) := H.induce (φ.Bicoloured a b)

/-- Two edges are in the same component of the induced two-colour graph. -/
def SameComponent (φ : PartialColouring H F) (a b : Colour) (x y : W) : Prop :=
  ∃ hx : x ∈ φ.Bicoloured a b, ∃ hy : y ∈ φ.Bicoloured a b,
    (φ.KempeGraph a b).Reachable ⟨x, hx⟩ ⟨y, hy⟩

def Separable (φ : PartialColouring H F) (f : W) (a b : Colour) : Prop :=
  ∀ x y, φ.Neighbour f a x → φ.Neighbour f b y → ¬ φ.SameComponent a b x y

def JointSeparable (φ : PartialColouring H F) (B : Set W) (a b : Colour) : Prop :=
  ∀ f ∈ B, ∀ g ∈ B, ∀ x y,
    φ.Neighbour f a x → φ.Neighbour g b y → ¬ φ.SameComponent a b x y

def Stuck (φ : PartialColouring H F) (e : W) : Prop :=
  (∀ a, ∃ g, φ.Neighbour e a g) ∧
    ∀ a b, a ≠ b → ¬ φ.Separable e a b

/-- A union of whole components of the induced two-colour graph. -/
def KempeClosed (φ : PartialColouring H F) (a b : Colour) (S : Set W) : Prop :=
  S ⊆ φ.Bicoloured a b ∧
    ∀ ⦃x y⦄, x ∈ S → y ∈ φ.Bicoloured a b → H.Adj x y → y ∈ S

def swapColour (φ : PartialColouring H F) (a b : Colour) (S : Set W) (x : W) : Colour :=
  if x ∈ S then Equiv.swap a b (φ.colour x) else φ.colour x

/-- The actual connected components are counted, including isolated coloured edges. -/
def componentCount (φ : PartialColouring H F) : ℕ :=
  ∑ a : Colour, ∑ b : Colour,
    if a < b then Nat.card (φ.KempeGraph a b).ConnectedComponent else 0

/-- `ψ` is obtained by one swap on one entire nonempty component. -/
def OneKempeSwap (φ ψ : PartialColouring H F) : Prop :=
  ∃ a b : Colour, a ≠ b ∧ ∃ x, x ∈ φ.Bicoloured a b ∧
    ∀ y, ψ.colour y = φ.swapColour a b {y | φ.SameComponent a b x y} y

def LocallyMaximal (φ : PartialColouring H F) : Prop :=
  ∀ ψ, φ.OneKempeSwap ψ → ψ.componentCount ≤ φ.componentCount

def Repairable (φ : PartialColouring H F) (e : W) : Prop :=
  (∃ a, φ.Free e a) ∨ (∃ a b, a ≠ b ∧ φ.Separable e a b) ∨
    ∃ p f, φ.Single e p f ∧ ∃ a b,
      a ≠ b ∧ a ≠ p ∧ b ≠ p ∧ φ.Separable f a b

end PartialColouring

def OnTriangle {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : Prop :=
  ∃ u v w, e.val = s(u, v) ∧ G.Adj u w ∧ G.Adj v w


def MaxDegreeFour {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v ≤ 4

def FourRegular {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, G.degree v = 4

end Se20Part
