import ComputableAnalysis.Basic

/-!
# Finite paths and explicit elementary homotopies

The edge and filled-triangle predicates concern geometry only. A homotopy is
finite proof data, not an assertion that all continuation operators agree.
No ambient real line, completion, or topological compactness is imported.
-/
namespace ComputableAnalysis.Continuation

universe u

inductive Path {X : Type u} (Edge : X → X → Prop) : X → X → Type u
  | nil (a) : Path Edge a a
  | cons {a b c} : Edge a b → Path Edge b c → Path Edge a c

namespace Path
variable {X : Type u} {E : X → X → Prop}

def append {a b c : X} (p : Path E a b) (q : Path E b c) : Path E a c :=
  match p with
  | .nil _ => q
  | .cons e p => .cons e (append p q)

@[simp] theorem nil_append {a b : X} (p : Path E a b) :
    append (.nil a) p = p := rfl

@[simp] theorem append_nil {a b : X} (p : Path E a b) :
    append p (.nil b) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

@[simp] theorem append_assoc {a b c d : X}
    (p : Path E a b) (q : Path E b c) (r : Path E c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

def reverse (symm : ∀ {a b}, E a b → E b a) {a b : X}
    (p : Path E a b) : Path E b a :=
  match p with
  | .nil a => .nil a
  | .cons e p => append (reverse symm p) (.cons (symm e) (.nil _))

def length {a b : X} : Path E a b → Nat
  | .nil _ => 0
  | .cons _ p => length p + 1

end Path

/-- Elementary moves: erase a stationary step or backtrack, or replace two
sides of a supplied filled triangle by its third side; close under composition.
The triangle predicate must be justified by the particular domain geometry. -/
inductive Homotopy {X : Type u} (E : X → X → Prop) (Face : X → X → X → Prop) :
    {a b : X} → Path E a b → Path E a b → Prop
  | refl (p) : Homotopy E Face p p
  | symm : Homotopy E Face p q → Homotopy E Face q p
  | trans : Homotopy E Face p q → Homotopy E Face q r → Homotopy E Face p r
  | cons (e : E a b) : Homotopy E Face p q →
      Homotopy E Face (.cons e p) (.cons e q)
  | stationary (e : E a a) : Homotopy E Face (.cons e (.nil a)) (.nil a)
  | backtrack (e : E a b) (f : E b a) :
      Homotopy E Face (.cons e (.cons f (.nil a))) (.nil a)
  | triangle (e : E a b) (f : E b c) (g : E a c) (h : Face a b c) :
      Homotopy E Face (.cons e (.cons f (.nil c))) (.cons g (.nil c))
  | append {a b c} {p q : Path E a b} (h : Homotopy E Face p q)
      (r : Path E b c) : Homotopy E Face (p.append r) (q.append r)

/-- Simple connectedness for this finite geometric presentation.
It supplies fillings, not endpoint agreement of any analytic computation.
Relating it to a different topological path notion requires a separate theorem. -/
structure FiniteSimplyConnected {X : Type u} (E : X → X → Prop)
    (Face : X → X → X → Prop) where
  route : ∀ a b, Path E a b
  fill : ∀ {a b} (p q : Path E a b), Homotopy E Face p q

/-- In a convex presentation every pair is an edge and every triangle is
filled. This constructs the contractions by induction on the path. -/
theorem homotopy_direct {X : Type u} {E : X → X → Prop}
    {Face : X → X → X → Prop} (edge : ∀ a b, E a b)
    (face : ∀ a b c, Face a b c) {a b : X} (p : Path E a b) :
    Homotopy E Face p (.cons (edge a b) (.nil b)) := by
  induction p with
  | nil a => exact .symm (.stationary (edge a a))
  | @cons a b c e p ih =>
      exact .trans (.cons e ih) (.triangle e (edge b c) (edge a c) (face a b c))

def convexFiniteSimplyConnected {X : Type u} {E : X → X → Prop}
    {Face : X → X → X → Prop} (edge : ∀ a b, E a b)
    (face : ∀ a b c, Face a b c) : FiniteSimplyConnected E Face where
  route := fun a b => .cons (edge a b) (.nil b)
  fill := fun p q => .trans (homotopy_direct edge face p)
    (.symm (homotopy_direct edge face q))

end ComputableAnalysis.Continuation
