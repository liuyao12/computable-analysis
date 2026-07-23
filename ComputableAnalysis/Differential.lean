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

/-- The exact rational difference quotient used by the finite product
identities below. -/
def differenceQuotient (f : Rat -> Rat) (x h : Rat) : Rat :=
  (f (x + h) - f x) / h

/-- The exact finite-difference product decomposition with the second factor
evaluated at the right endpoint.  This is the algebraic core of the product
rule before any continuity or limiting certificate is invoked. -/
theorem product_differenceQuotient_right
    (u v : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) :
    (u (x + h) * v (x + h) - u x * v x) / h =
      u x * ((v (x + h) - v x) / h) +
        v (x + h) * ((u (x + h) - u x) / h) := by
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The equivalent finite-difference product decomposition with both main
terms evaluated at the left endpoint.  The last term is the explicit corner
remainder which a constructive product-derivative proof must bound. -/
theorem product_differenceQuotient_corner
    (u v : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) :
    (u (x + h) * v (x + h) - u x * v x) / h =
      u x * ((v (x + h) - v x) / h) +
        v x * ((u (x + h) - u x) / h) +
          h * ((u (x + h) - u x) / h) *
            ((v (x + h) - v x) / h) := by
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The finite product-rule error is bounded by the two supplied
difference-quotient errors and one explicit corner remainder.  This is a
rational inequality, before it is lifted to interval enclosures or any
continuity certificate. -/
theorem product_differenceQuotient_error_le
    (u du v dv : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) (h0 : 0 <= h) :
    qabs (differenceQuotient (fun z => u z * v z) x h -
      (u x * dv x + v x * du x)) <=
      qabs (u x) * qabs (differenceQuotient v x h - dv x) +
        qabs (v x) * qabs (differenceQuotient u x h - du x) +
          h * qabs (differenceQuotient u x h) *
            qabs (differenceQuotient v x h) := by
  have hdecomp :
      differenceQuotient (fun z => u z * v z) x h -
          (u x * dv x + v x * du x) =
        u x * (differenceQuotient v x h - dv x) +
          v x * (differenceQuotient u x h - du x) +
            h * differenceQuotient u x h * differenceQuotient v x h := by
    unfold differenceQuotient
    rw [product_differenceQuotient_corner u v x h hh]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hdecomp]
  calc
    qabs
        (u x * (differenceQuotient v x h - dv x) +
          v x * (differenceQuotient u x h - du x) +
            h * differenceQuotient u x h * differenceQuotient v x h) <=
        qabs
          (u x * (differenceQuotient v x h - dv x) +
            v x * (differenceQuotient u x h - du x)) +
          qabs (h * differenceQuotient u x h * differenceQuotient v x h) :=
      qabs_add_le _ _
    _ <= (qabs (u x * (differenceQuotient v x h - dv x)) +
          qabs (v x * (differenceQuotient u x h - du x))) +
          qabs (h * differenceQuotient u x h * differenceQuotient v x h) :=
      (Rat.add_le_add_right).2 (qabs_add_le _ _)
    _ = qabs (u x) * qabs (differenceQuotient v x h - dv x) +
          qabs (v x) * qabs (differenceQuotient u x h - du x) +
            h * qabs (differenceQuotient u x h) *
              qabs (differenceQuotient v x h) := by
      rw [qabs_mul, qabs_mul, qabs_mul, qabs_mul,
        qabs_eq_self_of_nonneg h0]
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

/-- Dividing the difference of two exact singleton boxes gives the exact
rational difference quotient.  The sign split in interval division is harmless
here because both endpoints coincide. -/
theorem differenceQuotient_singleton
    (y x h : Rat) :
    differenceQuotient { lo := y, hi := y } { lo := x, hi := x } h =
      { lo := (y - x) / h, hi := (y - x) / h } := by
  unfold differenceQuotient divRat sub scaleRat
  simp [Rat.div_def, Rat.mul_comm]

end QInterval

/-- Two identical exact singleton boxes are near at every requested precision.
This small lemma is the interval-valued replacement for treating a rational
calculation as an exact real value. -/
theorem intervalNearAtPrecision_singleton_self (q : Rat) (n : Nat) :
    intervalNearAtPrecision { lo := q, hi := q } { lo := q, hi := q } n := by
  unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
  have heps : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind [Rat.sub_eq_add_neg]

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

namespace FunctionOnInterval

/-- Exact affine rational functions satisfy the interval-valued derivative
definition on every rational interval.  The certificate uses no limiting
operation: each finite quotient is literally the constant rational slope. -/
def exactRatAffineDerivative (a b m c : Rat) :
    HasDerivativeOnInterval
      (exactRat (fun x => m * x + c) a b)
      (exactRat (fun _x => m) a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := fun _n => 1
  evalPrecision := fun _n => 0
  close := by
    intro x h n _hx _hxh _hdx hh _hsmall
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := m * (x + h) + c, hi := m * (x + h) + c }
        { lo := m * x + c, hi := m * x + c } h)
      { lo := m, hi := m } n
    rw [QInterval.differenceQuotient_singleton]
    have hcalc : (m * (x + h) + c - (m * x + c)) / h = m := by
      rw [Rat.div_def]
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hcalc]
    exact intervalNearAtPrecision_singleton_self m n

/-- The exact unit coordinate has derivative one in the interval-valued
finite-difference sense used by the calculus layer. -/
def exactRatIdDerivative (a b : Rat) :
    HasDerivativeOnInterval
      (exactRat (fun x => x) a b)
      (exactRat (fun _x => 1) a b) := by
  simpa [Rat.one_mul, Rat.add_zero] using
    exactRatAffineDerivative a b 1 0

end FunctionOnInterval

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
