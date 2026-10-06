import Init

/-!
# The algebraic word layer of the sphere Riemann–Hilbert program

These are reversible maps on an arbitrary fiber, not analytic continuation
operators. The analytic continuation layer must use the project's valid
RealRaw/ComplexRaw representations and value equivalence, with audited
imports excluding completed Mathlib scalars. No ODE, complex field, sphere topology, or regular-singular
existence assertion is encoded in this file. Word lists are chronological:
the head acts first. The puncture relation is supplied separately.
-/
namespace ComputableAnalysis.RiemannHilbert

universe u v

/-- A reversible fiber map, with both inverse laws proved. -/
structure FiberIso (V : Type u) where
  forward : V → V
  backward : V → V
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x

namespace FiberIso

variable {V : Type u}

def identity : FiberIso V where
  forward := id
  backward := id
  backward_forward _ := rfl
  forward_backward _ := rfl

def inverse (a : FiberIso V) : FiberIso V where
  forward := a.backward
  backward := a.forward
  backward_forward := a.forward_backward
  forward_backward := a.backward_forward

/-- `followedBy a b` applies `a` first and `b` second. -/
def followedBy (a b : FiberIso V) : FiberIso V where
  forward x := b.forward (a.forward x)
  backward x := a.backward (b.backward x)
  backward_forward x := by simp [a.backward_forward, b.backward_forward]
  forward_backward x := by simp [a.forward_backward, b.forward_backward]

/-- Coordinate change: new coordinates map to old coordinates by `c`. -/
def conjugate (a c : FiberIso V) : FiberIso V :=
  followedBy (followedBy c a) c.inverse

@[simp] theorem conjugate_forward (a c : FiberIso V) (x : V) :
    (a.conjugate c).forward x = c.backward (a.forward (c.forward x)) := rfl

@[simp] theorem conjugate_backward (a c : FiberIso V) (x : V) :
    (a.conjugate c).backward x = c.backward (a.backward (c.forward x)) := rfl

end FiberIso

/-- Formal oriented puncture generator; no topological loop is assumed. -/
inductive Letter (I : Type v) where
  | positive : I → Letter I
  | negative : I → Letter I
  deriving DecidableEq

namespace Letter

def reverse : Letter I → Letter I
  | positive i => negative i
  | negative i => positive i

@[simp] theorem reverse_reverse (l : Letter I) : l.reverse.reverse = l := by
  cases l <;> rfl

end Letter

variable {V : Type u} {I : Type v}

def letterMap (m : I → FiberIso V) : Letter I → FiberIso V
  | .positive i => m i
  | .negative i => (m i).inverse

@[simp] theorem letter_reverse_forward (m : I → FiberIso V) (l : Letter I)
    (x : V) : (letterMap m l.reverse).forward x = (letterMap m l).backward x := by
  cases l <;> rfl

/-- Executable chronological word evaluation. -/
def run (m : I → FiberIso V) : List (Letter I) → V → V
  | [], x => x
  | l :: ls, x => run m ls ((letterMap m l).forward x)

@[simp] theorem run_nil (m : I → FiberIso V) (x : V) : run m [] x = x := rfl

@[simp] theorem run_cons (m : I → FiberIso V) (l : Letter I)
    (ls : List (Letter I)) (x : V) :
    run m (l :: ls) x = run m ls ((letterMap m l).forward x) := rfl

theorem run_append (m : I → FiberIso V) (a b : List (Letter I)) (x : V) :
    run m (a ++ b) x = run m b (run m a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons l ls ih => exact ih ((letterMap m l).forward x)

def reverseWord (w : List (Letter I)) : List (Letter I) :=
  w.reverse.map Letter.reverse

theorem reverseWord_cons (l : Letter I) (w : List (Letter I)) :
    reverseWord (l :: w) = reverseWord w ++ [l.reverse] := by
  simp [reverseWord]

theorem run_reverse_run (m : I → FiberIso V) (w : List (Letter I)) (x : V) :
    run m (reverseWord w) (run m w x) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons l ls ih =>
      rw [reverseWord_cons, run_append]
      change (letterMap m l.reverse).forward
        (run m (reverseWord ls) (run m ls ((letterMap m l).forward x))) = x
      rw [ih]
      simp [letter_reverse_forward, (letterMap m l).backward_forward]

theorem run_run_reverse (m : I → FiberIso V) (w : List (Letter I)) (x : V) :
    run m w (run m (reverseWord w) x) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons l ls ih =>
      rw [reverseWord_cons, run_append, run_cons]
      simp only [run_cons, run_nil, letter_reverse_forward]
      rw [(letterMap m l).forward_backward, ih]

def wordMap (m : I → FiberIso V) (w : List (Letter I)) : FiberIso V where
  forward := run m w
  backward := run m (reverseWord w)
  backward_forward := run_reverse_run m w
  forward_backward := run_run_reverse m w

/-- Adjacent inverse letters cancel in every word context. -/
theorem run_cancel (m : I → FiberIso V) (a b : List (Letter I))
    (l : Letter I) (x : V) :
    run m (a ++ l :: l.reverse :: b) x = run m (a ++ b) x := by
  rw [run_append, run_append]
  simp [run, letter_reverse_forward, (letterMap m l).backward_forward]

/-- A candidate sphere relator acts trivially. This predicate asserts an
algebraic identity only; identifying it with puncture loops needs topology. -/
def SphereRelation (m : I → FiberIso V) (punctures : List I) : Prop :=
  ∀ x, run m (punctures.map Letter.positive) x = x

/-- Insertion of the sphere relator preserves evaluation, given its law. -/
theorem run_sphere_relation (m : I → FiberIso V) (punctures : List I)
    (h : SphereRelation m punctures) (a b : List (Letter I)) (x : V) :
    run m (a ++ punctures.map Letter.positive ++ b) x = run m (a ++ b) x := by
  rw [run_append, run_append, run_append, h]

/-- The congruence generated by inverse cancellation and the supplied ordered
sphere relator. This is a finite presentation, not a topological fundamental
group identification. -/
inductive WordEquivalent (punctures : List I) :
    List (Letter I) → List (Letter I) → Prop where
  | refl (w) : WordEquivalent punctures w w
  | symm {a b} : WordEquivalent punctures a b → WordEquivalent punctures b a
  | trans {a b c} : WordEquivalent punctures a b →
      WordEquivalent punctures b c → WordEquivalent punctures a c
  | context (a b) {w z} : WordEquivalent punctures w z →
      WordEquivalent punctures (a ++ w ++ b) (a ++ z ++ b)
  | cancel (l) : WordEquivalent punctures [l, l.reverse] []
  | sphere : WordEquivalent punctures (punctures.map Letter.positive) []

/-- All relations of the finite presentation preserve the fiber action.
This derives well-definedness; it is not a field of a representation record. -/
theorem run_equivalent (m : I → FiberIso V) (p : List I)
    (hp : SphereRelation m p) {a b : List (Letter I)}
    (h : WordEquivalent p a b) (x : V) : run m a x = run m b x := by
  induction h generalizing x with
  | refl => rfl
  | symm h ih => exact (ih x).symm
  | trans h k ih ik => exact (ih x).trans (ik x)
  | context a b h ih =>
      simp only [run_append]
      rw [ih]
  | cancel l =>
      simp [run, letter_reverse_forward, (letterMap m l).backward_forward]
  | sphere => exact hp x

/-- Generator coordinate changes conjugate every word, with the same basis. -/
theorem run_conjugate (m : I → FiberIso V) (c : FiberIso V)
    (w : List (Letter I)) (x : V) :
    run (fun i => (m i).conjugate c) w x = c.backward (run m w (c.forward x)) := by
  induction w generalizing x with
  | nil => exact (c.backward_forward x).symm
  | cons l ls ih =>
      rw [run_cons, ih]
      have hl : (letterMap (fun i => (m i).conjugate c) l).forward x =
          c.backward ((letterMap m l).forward (c.forward x)) := by
        cases l <;> rfl
      rw [hl, c.forward_backward]
      rfl

theorem sphereRelation_conjugate (m : I → FiberIso V) (c : FiberIso V)
    (p : List I) (h : SphereRelation m p) :
    SphereRelation (fun i => (m i).conjugate c) p := by
  intro x
  rw [run_conjugate, h, c.backward_forward]

/-- The missing final puncture map is constructed as the inverse of the
chronological product of the supplied puncture maps. -/
def closingMap (m : I → FiberIso V) (p : List I) : FiberIso V :=
  (wordMap m (p.map Letter.positive)).inverse

theorem closingMap_relation (m : I → FiberIso V) (p : List I) (x : V) :
    (closingMap m p).forward (run m (p.map Letter.positive) x) = x :=
  run_reverse_run m (p.map Letter.positive) x

/-- The sphere relation uniquely determines the final map, pointwise. -/
theorem closingMap_unique (m : I → FiberIso V) (p : List I) (last : FiberIso V)
    (h : ∀ x, last.forward (run m (p.map Letter.positive) x) = x) (x : V) :
    last.forward x = (closingMap m p).forward x := by
  have hx := h (run m (reverseWord (p.map Letter.positive)) x)
  rw [run_run_reverse] at hx
  exact hx

/-- Intertwining positive generators implies intertwining their inverses;
no inverse-intertwining field is assumed. -/
theorem intertwine_inverse {W : Type u} (a : FiberIso V) (b : FiberIso W)
    (f : V → W) (h : ∀ x, f (a.forward x) = b.forward (f x)) (x : V) :
    f (a.backward x) = b.backward (f x) := by
  have hx := congrArg b.backward (h (a.backward x))
  simpa [a.forward_backward, b.backward_forward] using hx.symm

/-- Morphisms checked on generators commute with all word transports. -/
theorem intertwine_run {W : Type u} (m : I → FiberIso V) (n : I → FiberIso W)
    (f : V → W) (h : ∀ i x, f ((m i).forward x) = (n i).forward (f x))
    (w : List (Letter I)) (x : V) : f (run m w x) = run n w (f x) := by
  induction w generalizing x with
  | nil => rfl
  | cons l ls ih =>
      rw [run_cons, ih, run_cons]
      have hl : f ((letterMap m l).forward x) = (letterMap n l).forward (f x) := by
        cases l with
        | positive i => exact h i x
        | negative i => exact intertwine_inverse (m i) (n i) f (h i) x
      rw [hl]

end ComputableAnalysis.RiemannHilbert
