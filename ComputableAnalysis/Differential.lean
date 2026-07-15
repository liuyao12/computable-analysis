import ComputableAnalysis.Calculus

/-!
# Constructive differential calculus

This file contains the small derivative vocabulary needed before proving
calculus identities for the elementary representations.  It is intentionally
interval-valued and rational-only.
-/

namespace ComputableAnalysis

/-- Equality of real-valued functions on rational inputs.

This is the function-level equality notion we use in the project: for every
rational input in the common domain, the two output `RealRaw`s are equivalent
by interval overlap at every precision. -/
def RealFunRaw.EquivalentWith (f g : RealFunRaw)
    (hf : f.Valid) (hg : g.Valid) : Prop :=
  forall x (hfx : f.domain x) (hgx : g.domain x),
    (f.apply hf x hfx).Equiv (g.apply hg x hgx)

def RealFunRaw.Equivalent (f g : RealFunRaw) : Prop :=
  Exists fun hf : f.Valid => Exists fun hg : g.Valid =>
    f.EquivalentWith g hf hg

def derivativeCheckExact (f g : Rat -> Rat) (x h tolerance : Rat) : Bool :=
  if h = 0 then
    false
  else
    decide (qabs (((f (x + h) - f x) / h) - g x) <= tolerance)

namespace ExactFunction

def affine (m c : Rat) (x : Rat) : Rat := m * x + c
def constant (m : Rat) (_x : Rat) : Rat := m
def square (x : Rat) : Rat := x * x
def doubleId (x : Rat) : Rat := 2 * x

/-- Effective derivative of an affine function:
the finite-difference quotient is exactly the constant slope. -/
def affineDerivative (m c : Rat) :
    EffectiveDerivativeExact (affine m c) (constant m) where
  stepRadius := fun eps => eps
  good := by
    intro x h eps hhpos _hhle
    unfold affine constant qabs
    have hcalc :
        (((m * (x + h) + c - (m * x + c)) / h) - m) = 0 := by
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    rw [hcalc]
    simp
    exact Rat.le_of_lt eps.property

theorem affine_derivative_effective (m c : Rat) :
    Nonempty (EffectiveDerivativeExact (affine m c) (constant m)) :=
  ⟨affineDerivative m c⟩

/-- Effective derivative of `x^2`:
the finite-difference quotient is exactly `2x + h`, hence it is within `eps`
of `2x` whenever `0 < h <= eps`. -/
def squareDerivative : EffectiveDerivativeExact square doubleId where
  stepRadius := fun eps => eps
  good := by
    intro x h eps hhpos hhle
    unfold square doubleId qabs
    have hcalc :
        (((x + h) * (x + h) - x * x) / h - 2 * x) = h := by
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    rw [hcalc]
    have hnot : ¬ h < 0 := by grind
    simp [hnot]
    exact hhle

theorem square_derivative_effective :
    Nonempty (EffectiveDerivativeExact square doubleId) :=
  ⟨squareDerivative⟩
end ExactFunction

namespace QInterval

def scaleRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def neg (I : QInterval) : QInterval :=
  { lo := -I.hi, hi := -I.lo }

def sub (I J : QInterval) : QInterval :=
  { lo := I.lo - J.hi, hi := I.hi - J.lo }

def divRat (I : QInterval) (h : Rat) : QInterval :=
  scaleRat (1 / h) I

def differenceQuotient (fxh fx : QInterval) (h : Rat) : QInterval :=
  divRat (sub fxh fx) h

end QInterval

/-- Two interval functions represent the same function on the same rational
interval when all point-values overlap at every precision.

This is deliberately local to a chosen interval; raw partial functions with
different domains do not have a global transitive equivalence relation. -/
def FunctionOnInterval.Equivalent (f g : FunctionOnInterval) : Prop :=
  f.lower = g.lower /\
  f.upper = g.upper /\
  forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
    (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
      (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

/-- Effective derivative on a rational interval.

For every requested output precision, small enough rational steps make the
finite-difference interval lie within the derivative interval's requested
tolerance.  Literal overlap would incorrectly demand equality at every finite
nonzero step. -/
structure HasDerivativeOnInterval (f df : FunctionOnInterval) where
  same_lower : df.lower = f.lower
  same_upper : df.upper = f.upper
  stepPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x h n
      (hx : inDomainInterval f.lower f.upper x)
      (hxh : inDomainInterval f.lower f.upper (x + h))
      (hdx : inDomainInterval df.lower df.upper x),
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
        intervalNearAtPrecision
          (QInterval.differenceQuotient
            (f.compute (x + h) hxh (evalPrecision n))
            (f.compute x hx (evalPrecision n))
            h)
          (df.compute x hdx (evalPrecision n))
          n

/-- A function solving `f' = f` on an interval with a specified initial value.

This is the constructive uniqueness route for comparing exponential
representations without appealing to classical real completeness. -/
structure SolvesSelfDerivativeOnInterval (f : FunctionOnInterval) where
  derivative_self : HasDerivativeOnInterval f f
  initial : Rat
  initial_mem : inDomainInterval f.lower f.upper initial
  initial_value : RealRaw
  initial_value_valid : initial_value.Valid
  initial_value_equiv :
    (PartialRealFunRaw.apply f.raw f.valid_on initial
      (f.defined_on initial initial_mem)).Equiv initial_value

/-- Uniqueness principle for `f' = f`.

The future proof should be constructive: estimate the difference of two
solutions on a finite rational subdivision, rather than invoking a classical
ODE theorem. -/
def SelfDerivativeInitialValueUnique : Prop :=
  forall f g,
    SolvesSelfDerivativeOnInterval f ->
    SolvesSelfDerivativeOnInterval g ->
    FunctionOnInterval.Equivalent f g

end ComputableAnalysis
