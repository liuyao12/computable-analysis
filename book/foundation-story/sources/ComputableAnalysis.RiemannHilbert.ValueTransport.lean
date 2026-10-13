import ComputableAnalysis.RiemannHilbert.MonodromyWords

/-!
# Transport on represented values

Equality here is a supplied value equivalence, never equality of raw programs.
The complex fiber instance is constructed in `RepresentedFiber`. These laws
are algebraic consequences of supplied value-preserving reversible maps.
-/
namespace ComputableAnalysis.RiemannHilbert

universe u v w

/-- A map preserving the specified equality of values. -/
structure ValueMap (V : Type u) (W : Type v) [Setoid V] [Setoid W] where
  eval : V → W
  congr : ∀ {x y}, x ≈ y → eval x ≈ eval y

namespace ValueMap

variable {V : Type u} {W : Type v} {Z : Type w}
variable [Setoid V] [Setoid W] [Setoid Z]

def identity : ValueMap V V := ⟨id, fun h => h⟩

def followedBy (f : ValueMap V W) (g : ValueMap W Z) : ValueMap V Z :=
  ⟨fun x => g.eval (f.eval x), fun h => g.congr (f.congr h)⟩

def Equiv (f g : ValueMap V W) : Prop := ∀ x, f.eval x ≈ g.eval x

theorem equiv_refl (f : ValueMap V W) : f.Equiv f := fun _ => Setoid.refl _

theorem equiv_symm {f g : ValueMap V W} (h : f.Equiv g) : g.Equiv f :=
  fun x => Setoid.symm (h x)

theorem equiv_trans {f g h : ValueMap V W} (hf : f.Equiv g) (hg : g.Equiv h) :
    f.Equiv h := fun x => Setoid.trans (hf x) (hg x)

theorem followedBy_congr {f f' : ValueMap V W} {g g' : ValueMap W Z}
    (hf : f.Equiv f') (hg : g.Equiv g') :
    (f.followedBy g).Equiv (f'.followedBy g') := fun x =>
  Setoid.trans (g.congr (hf x)) (hg (f'.eval x))

end ValueMap

/-- Reversibility up to value equality, between possibly different fibers. -/
structure ValueIso (V : Type u) (W : Type v) [Setoid V] [Setoid W] where
  forward : ValueMap V W
  backward : ValueMap W V
  backward_forward : ∀ x, backward.eval (forward.eval x) ≈ x
  forward_backward : ∀ x, forward.eval (backward.eval x) ≈ x

namespace ValueIso

variable {V : Type u} {W : Type v} {Z : Type w}
variable [Setoid V] [Setoid W] [Setoid Z]

def identity : ValueIso V V :=
  ⟨ValueMap.identity, ValueMap.identity, Setoid.refl, Setoid.refl⟩

def inverse (f : ValueIso V W) : ValueIso W V :=
  ⟨f.backward, f.forward, f.forward_backward, f.backward_forward⟩

def followedBy (f : ValueIso V W) (g : ValueIso W Z) : ValueIso V Z where
  forward := f.forward.followedBy g.forward
  backward := g.backward.followedBy f.backward
  backward_forward x := Setoid.trans (f.backward.congr (g.backward_forward _))
    (f.backward_forward x)
  forward_backward x := Setoid.trans (g.forward.congr (f.forward_backward _))
    (g.forward_backward x)

/-- Basis map `c` sends new coordinates to old coordinates. -/
def conjugate (a : ValueIso V V) (c : ValueIso W V) : ValueIso W W :=
  (c.followedBy a).followedBy c.inverse

/-- Value equality can be reflected through an invertible map. -/
theorem forward_reflects (f : ValueIso V W) {x y : V}
    (h : f.forward.eval x ≈ f.forward.eval y) : x ≈ y :=
  Setoid.trans (Setoid.symm (f.backward_forward x))
    (Setoid.trans (f.backward.congr h) (f.backward_forward y))

/-- Agreement of the forward values forces agreement of inverse values. -/
theorem inverse_congr (f g : ValueIso V W) (h : f.forward.Equiv g.forward) :
    f.backward.Equiv g.backward := fun x =>
  Setoid.trans (f.backward.congr (Setoid.symm (g.forward_backward x)))
    (Setoid.trans (f.backward.congr (Setoid.symm (h (g.backward.eval x))))
      (f.backward_forward (g.backward.eval x)))

end ValueIso

namespace ValueTransport

variable {V : Type u} {W : Type v} {I : Type w}
variable [Setoid V] [Setoid W]

def letterMap (m : I → ValueIso V V) : Letter I → ValueIso V V
  | .positive i => m i
  | .negative i => (m i).inverse

def run (m : I → ValueIso V V) : List (Letter I) → V → V
  | [], x => x
  | l :: ls, x => run m ls ((letterMap m l).forward.eval x)

theorem run_congr (m : I → ValueIso V V) (w : List (Letter I)) {x y : V}
    (h : x ≈ y) : run m w x ≈ run m w y := by
  induction w generalizing x y with
  | nil => exact h
  | cons l ls ih => exact ih ((letterMap m l).forward.congr h)

theorem run_append (m : I → ValueIso V V) (a b : List (Letter I)) (x : V) :
    run m (a ++ b) x = run m b (run m a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons l ls ih => exact ih ((letterMap m l).forward.eval x)

/-- Distinct implementations of all generators give the same word value. -/
theorem run_generators_congr (m n : I → ValueIso V V)
    (hf : ∀ i, (m i).forward.Equiv (n i).forward)
    (hb : ∀ i, (m i).backward.Equiv (n i).backward)
    (w : List (Letter I)) (x : V) : run m w x ≈ run n w x := by
  induction w generalizing x with
  | nil => exact Setoid.refl _
  | cons l ls ih =>
      have hl : (letterMap m l).forward.eval x ≈ (letterMap n l).forward.eval x := by
        cases l with
        | positive i => exact hf i x
        | negative i => exact hb i x
      exact Setoid.trans (ih _) (run_congr n ls hl)

/-- Inverse implementations need no independent agreement hypothesis. -/
theorem run_forward_generators_congr (m n : I → ValueIso V V)
    (h : ∀ i, (m i).forward.Equiv (n i).forward)
    (w : List (Letter I)) (x : V) : run m w x ≈ run n w x :=
  run_generators_congr m n h (fun i => ValueIso.inverse_congr (m i) (n i) (h i)) w x

theorem letter_reverse_forward (m : I → ValueIso V V) (l : Letter I) (x : V) :
    (letterMap m l.reverse).forward.eval x = (letterMap m l).backward.eval x := by
  cases l <;> rfl

theorem run_reverse_run (m : I → ValueIso V V) (w : List (Letter I)) (x : V) :
    run m (reverseWord w) (run m w x) ≈ x := by
  induction w generalizing x with
  | nil => exact Setoid.refl _
  | cons l ls ih =>
      rw [reverseWord_cons, run_append]
      change (letterMap m l.reverse).forward.eval
        (run m (reverseWord ls) (run m ls ((letterMap m l).forward.eval x))) ≈ x
      rw [letter_reverse_forward]
      exact Setoid.trans ((letterMap m l).backward.congr (ih _))
        ((letterMap m l).backward_forward x)

theorem run_run_reverse (m : I → ValueIso V V) (w : List (Letter I)) (x : V) :
    run m w (run m (reverseWord w) x) ≈ x := by
  induction w generalizing x with
  | nil => exact Setoid.refl _
  | cons l ls ih =>
      rw [reverseWord_cons, run_append]
      change run m ls ((letterMap m l).forward.eval
        ((letterMap m l.reverse).forward.eval (run m (reverseWord ls) x))) ≈ x
      rw [letter_reverse_forward]
      exact Setoid.trans (run_congr m ls ((letterMap m l).forward_backward _)) (ih x)

def wordMap (m : I → ValueIso V V) (w : List (Letter I)) : ValueIso V V where
  forward := ⟨run m w, run_congr m w⟩
  backward := ⟨run m (reverseWord w), run_congr m (reverseWord w)⟩
  backward_forward := run_reverse_run m w
  forward_backward := run_run_reverse m w

def SphereRelation (m : I → ValueIso V V) (p : List I) : Prop :=
  ∀ x, run m (p.map Letter.positive) x ≈ x

theorem run_equivalent (m : I → ValueIso V V) (p : List I)
    (hp : SphereRelation m p) {a b : List (Letter I)}
    (h : WordEquivalent p a b) (x : V) : run m a x ≈ run m b x := by
  induction h generalizing x with
  | refl => exact Setoid.refl _
  | symm h ih => exact Setoid.symm (ih x)
  | trans h k ih ik => exact Setoid.trans (ih x) (ik x)
  | context a b h ih =>
      simp only [run_append]
      exact run_congr m b (ih _)
  | cancel l =>
      change (letterMap m l.reverse).forward.eval ((letterMap m l).forward.eval x) ≈ x
      rw [letter_reverse_forward]
      exact (letterMap m l).backward_forward x
  | sphere => exact hp x

theorem run_conjugate (m : I → ValueIso V V) (c : ValueIso W V)
    (w : List (Letter I)) (x : W) :
    run (fun i => (m i).conjugate c) w x ≈
      c.backward.eval (run m w (c.forward.eval x)) := by
  induction w generalizing x with
  | nil => exact Setoid.symm (c.backward_forward x)
  | cons l ls ih =>
      change run (fun i => (m i).conjugate c) ls
        ((letterMap (fun i => (m i).conjugate c) l).forward.eval x) ≈ _
      have hl : (letterMap (fun i => (m i).conjugate c) l).forward.eval x =
          c.backward.eval ((letterMap m l).forward.eval (c.forward.eval x)) := by
        cases l <;> rfl
      exact Setoid.trans (ih _) (c.backward.congr
        (run_congr m ls (by rw [hl]; exact c.forward_backward _)))

theorem sphereRelation_conjugate (m : I → ValueIso V V) (c : ValueIso W V)
    (p : List I) (h : SphereRelation m p) :
    SphereRelation (fun i => (m i).conjugate c) p := fun x =>
  Setoid.trans (run_conjugate m c _ x)
    (Setoid.trans (c.backward.congr (h _)) (c.backward_forward x))

def closingMap (m : I → ValueIso V V) (p : List I) : ValueIso V V :=
  (wordMap m (p.map Letter.positive)).inverse

theorem closingMap_relation (m : I → ValueIso V V) (p : List I) (x : V) :
    (closingMap m p).forward.eval (run m (p.map Letter.positive) x) ≈ x :=
  run_reverse_run m _ x

theorem closingMap_unique (m : I → ValueIso V V) (p : List I) (last : ValueIso V V)
    (h : ∀ x, last.forward.eval (run m (p.map Letter.positive) x) ≈ x) (x : V) :
    last.forward.eval x ≈ (closingMap m p).forward.eval x :=
  Setoid.trans (last.forward.congr (Setoid.symm (run_run_reverse m _ x))) (h _)

theorem intertwine_inverse (a : ValueIso V V) (b : ValueIso W W)
    (f : ValueMap V W) (h : ∀ x, f.eval (a.forward.eval x) ≈ b.forward.eval (f.eval x))
    (x : V) : f.eval (a.backward.eval x) ≈ b.backward.eval (f.eval x) := by
  exact Setoid.trans (Setoid.symm (b.backward_forward _))
    (b.backward.congr (Setoid.trans (Setoid.symm (h _))
      (f.congr (a.forward_backward x))))

theorem intertwine_run (m : I → ValueIso V V) (n : I → ValueIso W W)
    (f : ValueMap V W)
    (h : ∀ i x, f.eval ((m i).forward.eval x) ≈ (n i).forward.eval (f.eval x))
    (w : List (Letter I)) (x : V) : f.eval (run m w x) ≈ run n w (f.eval x) := by
  induction w generalizing x with
  | nil => exact Setoid.refl _
  | cons l ls ih =>
      have hl : f.eval ((letterMap m l).forward.eval x) ≈
          (letterMap n l).forward.eval (f.eval x) := by
        cases l with
        | positive i => exact h i x
        | negative i => exact intertwine_inverse (m i) (n i) f (h i) x
      exact Setoid.trans (ih _) (run_congr n ls hl)

end ValueTransport
end ComputableAnalysis.RiemannHilbert
