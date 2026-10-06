import ComputableAnalysis.ComplexMultiplication
import ComputableAnalysis.RiemannHilbert.ValueTransport

/-!
# Finite fibers over valid represented complex scalars

No completed field is introduced. Coordinate equality is `ComplexRaw.Equiv`;
all scalar inputs are arbitrary valid complex representations. Function types
alone do not assert computability; the definitions preserve executable inputs.
-/
namespace ComputableAnalysis.RiemannHilbert

abbrev Scalar := {z : ComplexRaw // z.Valid}
abbrev Fiber (n : Nat) := {x : Fin n → ComplexRaw // ∀ i, (x i).Valid}

namespace Fiber

instance (n : Nat) : Setoid (Fiber n) where
  r x y := ∀ i, (x.val i).Equiv (y.val i)
  iseqv := ⟨fun x i => ComplexRaw.equiv_refl _ (x.property i),
    fun h i => ComplexRaw.equiv_symm (h i),
    fun {x y z} h k i => ComplexRaw.equiv_trans
      (x.property i) (y.property i) (z.property i) (h i) (k i)⟩

def zero (n : Nat) : Fiber n :=
  ⟨fun _ => ComplexRaw.zero, fun _ => ComplexRaw.ofQComplex_valid QComplex.zero⟩

def add (x y : Fiber n) : Fiber n :=
  ⟨fun i => ComplexRaw.add (x.val i) (y.val i),
    fun i => ComplexRaw.add_valid (x.property i) (y.property i)⟩

def scale (a : Scalar) (x : Fiber n) : Fiber n :=
  ⟨fun i => ComplexRaw.mul a.val (x.val i),
    fun i => ComplexRaw.mul_valid a.property (x.property i)⟩

theorem add_congr {x x' y y' : Fiber n} (hx : x ≈ x') (hy : y ≈ y') :
    add x y ≈ add x' y' := fun i => ComplexRaw.add_equiv (hx i) (hy i)

/-- Both coefficient and coordinate representations may be changed. -/
theorem scale_congr {a b : Scalar} {x y : Fiber n}
    (ha : a.val.Equiv b.val) (hx : x ≈ y) : scale a x ≈ scale b y := fun i =>
  ComplexRaw.mul_equiv a.property b.property (x.property i) (y.property i) ha (hx i)

/-- Renaming a finite coordinate frame is an executable value isomorphism. -/
def reindex (f g : Fin n → Fin n) (hgf : ∀ i, g (f i) = i)
    (hfg : ∀ i, f (g i) = i) : ValueIso (Fiber n) (Fiber n) where
  forward := ⟨fun x => ⟨fun i => x.val (f i), fun i => x.property (f i)⟩,
    fun h i => h (f i)⟩
  backward := ⟨fun x => ⟨fun i => x.val (g i), fun i => x.property (g i)⟩,
    fun h i => h (g i)⟩
  backward_forward x i := by
    change (x.val (f (g i))).Equiv (x.val i)
    rw [hfg]
    exact ComplexRaw.equiv_refl _ (x.property i)
  forward_backward x i := by
    change (x.val (g (f i))).Equiv (x.val i)
    rw [hgf]
    exact ComplexRaw.equiv_refl _ (x.property i)

end Fiber

/-- Linearity over every valid represented complex coefficient. -/
def IsLinear (f : ValueMap (Fiber n) (Fiber m)) : Prop :=
  (∀ x y, f.eval (Fiber.add x y) ≈ Fiber.add (f.eval x) (f.eval y)) ∧
  (∀ a x, f.eval (Fiber.scale a x) ≈ Fiber.scale a (f.eval x))

namespace IsLinear

theorem identity (n : Nat) : IsLinear (ValueMap.identity : ValueMap (Fiber n) (Fiber n)) :=
  ⟨fun _ _ => Setoid.refl _, fun _ _ => Setoid.refl _⟩

theorem followedBy {f : ValueMap (Fiber n) (Fiber m)}
    {g : ValueMap (Fiber m) (Fiber k)} (hf : IsLinear f) (hg : IsLinear g) :
    IsLinear (f.followedBy g) :=
  ⟨fun x y => Setoid.trans (g.congr (hf.1 x y)) (hg.1 _ _),
    fun a x => Setoid.trans (g.congr (hf.2 a x)) (hg.2 a _)⟩

/-- Pointwise value agreement transports linearity between implementations. -/
theorem congr {f g : ValueMap (Fiber n) (Fiber m)}
    (hf : IsLinear f) (hfg : f.Equiv g) : IsLinear g := by
  constructor
  · intro x y
    exact Setoid.trans (Setoid.symm (hfg _))
      (Setoid.trans (hf.1 x y) (Fiber.add_congr (hfg x) (hfg y)))
  · intro a x
    exact Setoid.trans (Setoid.symm (hfg _))
      (Setoid.trans (hf.2 a x) (Fiber.scale_congr
        (ComplexRaw.equiv_refl a.val a.property) (hfg x)))

/-- Inverse linearity is a consequence, not an extra assumed field. -/
theorem inverse (f : ValueIso (Fiber n) (Fiber m)) (hf : IsLinear f.forward) :
    IsLinear f.backward := by
  constructor
  · intro x y
    apply f.forward_reflects
    exact Setoid.trans (f.forward_backward _)
      (Setoid.symm (Setoid.trans (hf.1 _ _)
        (Fiber.add_congr (f.forward_backward x) (f.forward_backward y))))
  · intro a x
    apply f.forward_reflects
    exact Setoid.trans (f.forward_backward _)
      (Setoid.symm (Setoid.trans (hf.2 a _)
        (Fiber.scale_congr (ComplexRaw.equiv_refl a.val a.property)
          (f.forward_backward x))))

end IsLinear

/-- A supplied invertible complex-linear map. Its inverse linearity is proved. -/
structure LinearIso (n m : Nat) where
  toValueIso : ValueIso (Fiber n) (Fiber m)
  linear : IsLinear toValueIso.forward

namespace LinearIso

def identity (n : Nat) : LinearIso n n := ⟨ValueIso.identity, IsLinear.identity n⟩

def inverse (f : LinearIso n m) : LinearIso m n :=
  ⟨f.toValueIso.inverse, IsLinear.inverse f.toValueIso f.linear⟩

def followedBy (f : LinearIso n m) (g : LinearIso m k) : LinearIso n k :=
  ⟨f.toValueIso.followedBy g.toValueIso, IsLinear.followedBy f.linear g.linear⟩

def conjugate (a : LinearIso n n) (c : LinearIso m n) : LinearIso m m :=
  (c.followedBy a).followedBy c.inverse

def reindex (f g : Fin n → Fin n) (hgf : ∀ i, g (f i) = i)
    (hfg : ∀ i, f (g i) = i) : LinearIso n n :=
  ⟨Fiber.reindex f g hgf hfg,
    ⟨fun x y i => ComplexRaw.equiv_refl _
      (ComplexRaw.add_valid (x.property (f i)) (y.property (f i))),
     fun a x i => ComplexRaw.equiv_refl _
      (ComplexRaw.mul_valid a.property (x.property (f i)))⟩⟩

end LinearIso

namespace RepresentedMonodromy

variable {I : Type} {n : Nat}

def letterMap (m : I → LinearIso n n) : Letter I → LinearIso n n
  | .positive i => m i
  | .negative i => (m i).inverse

def wordMap (m : I → LinearIso n n) : List (Letter I) → LinearIso n n
  | [] => LinearIso.identity n
  | l :: ls => (letterMap m l).followedBy (wordMap m ls)

/-- Agreement with the generic evaluator is literal: same computation. -/
theorem wordMap_eval (m : I → LinearIso n n) (w : List (Letter I)) (x : Fiber n) :
    (wordMap m w).toValueIso.forward.eval x =
      ValueTransport.run (fun i => (m i).toValueIso) w x := by
  induction w generalizing x with
  | nil => rfl
  | cons l ls ih =>
      change (wordMap m ls).toValueIso.forward.eval
        ((letterMap m l).toValueIso.forward.eval x) = _
      rw [ih]
      cases l <;> rfl

/-- The transported fiber action is linear at arbitrary represented inputs. -/
theorem run_linear (m : I → LinearIso n n) (w : List (Letter I)) :
    IsLinear (ValueTransport.wordMap (fun i => (m i).toValueIso) w).forward := by
  apply IsLinear.congr (wordMap m w).linear
  intro x
  rw [wordMap_eval]
  exact Setoid.refl _

end RepresentedMonodromy
end ComputableAnalysis.RiemannHilbert
