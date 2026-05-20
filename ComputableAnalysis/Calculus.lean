import ComputableAnalysis.Basic

namespace ComputableAnalysis

def mesh (a b : Rat) (n : Nat) : Rat := if n = 0 then 0 else (b - a) / n
def leftPoint (a b : Rat) (n k : Nat) : Rat := a + (k : Rat) * mesh a b n

def riemannLeftExact (g : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  let h := mesh a b n
  (List.range n).foldl (fun acc k => acc + h * g (leftPoint a b n k)) 0

def riemannLeftInterval (g : RealFunRaw) (a b : Rat) (n : Nat) (prec : Nat) : QInterval :=
  let h := mesh a b n
  (List.range n).foldl
    (fun acc k => let I := g.compute (leftPoint a b n k) prec; { lo := acc.lo + h * I.lo, hi := acc.hi + h * I.hi })
    { lo := 0, hi := 0 }

namespace RealFunRaw

def add (f g : RealFunRaw) : RealFunRaw where
  domain := fun x => f.domain x /\ g.domain x
  compute := fun x n =>
    let F := f.compute x n
    let G := g.compute x n
    { lo := F.lo + G.lo, hi := F.hi + G.hi }

def scaleRat (r : Rat) (f : RealFunRaw) : RealFunRaw where
  domain := f.domain
  compute := fun x n =>
    let F := f.compute x n
    if 0 <= r then
      { lo := r * F.lo, hi := r * F.hi }
    else
      { lo := r * F.hi, hi := r * F.lo }

end RealFunRaw

def intervalCloseAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.CloseAt I J (if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) })

/-- Effective modulus on a rational interval.

This is legacy pointwise-style continuity data used by the current FTC target.
Given an output precision `n`, it supplies:

* an input precision saying how close rational inputs must be;
* an evaluation precision saying how accurately to compute the function;
* a proof that sufficiently close inputs produce close output intervals.

This is intentionally interval-based rather than topological. -/
structure EffectiveModulusOn (f : RealFunRaw) (a b : Rat) where
  valid : f.Valid
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n,
      a <= x ->
      x <= b ->
      a <= y ->
      y <= b ->
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalCloseAtPrecision
          (f.compute x (evalPrecision n))
          (f.compute y (evalPrecision n))
          n

/- Constructive interval-sum integration. -/
namespace Integral

/-- Effective choices for computing an integral to a requested precision. -/
structure Plan where
  subdivisions : Nat
  evalPrecision : Nat

/-- A raw integral algorithm on a rational interval.

Given the requested output precision, choose a number of subintervals and an
evaluation precision, then compute the corresponding interval-valued left
sum. -/
structure Raw where
  integrand : RealFunRaw
  lower : Rat
  upper : Rat
  plan : Nat -> Plan

namespace Raw

def compute (I : Raw) (eps : Nat) : QInterval :=
  let p := I.plan eps
  riemannLeftInterval I.integrand I.lower I.upper p.subdivisions p.evalPrecision

def Valid (I : Raw) : Prop :=
  RealRaw.ValidCompute I.compute

def toRealRaw (I : Raw) (_h : I.Valid) : RealRaw where
  compute := I.compute

end Raw

/-- The certificate that an interval-valued integral-sum algorithm is a
well-defined computable real number: boxes are ordered, nested, and their
widths shrink to zero. -/
structure Certificate (I : Raw) where
  width_nonneg : forall eps, 0 <= (I.compute eps).width
  nested :
    forall eps delta, eps <= delta ->
      (I.compute eps).lo <= (I.compute delta).lo /\
      (I.compute delta).lo <= (I.compute delta).hi /\
      (I.compute delta).hi <= (I.compute eps).hi
  widths_shrink : RealRaw.WidthsShrinkToZero I.compute

namespace Certificate

theorem valid {I : Raw} (cert : Certificate I) :
    I.Valid :=
  ⟨cert.width_nonneg, cert.nested, cert.widths_shrink⟩

def realRaw {I : Raw} (cert : Certificate I) : RealRaw :=
  I.toRealRaw cert.valid

end Certificate

/-- The interval-sum algorithm determined by a function, interval, and plan. -/
def algorithm (f : RealFunRaw) (a b : Rat) (plan : Nat -> Plan) :
    Raw where
  integrand := f
  lower := a
  upper := b
  plan := plan

/-- The explicit data needed to construct an integral as a computable
real.  The public object is still `integral`; this structure just stores the
algorithmic choices and the proof that they work. -/
structure Construction (f : RealFunRaw) (a b : Rat) where
  plan : Nat -> Plan
  certificate : Certificate (algorithm f a b plan)

/-- The constructive integral operator. -/
def integral (f : RealFunRaw) (a b : Rat) (c : Construction f a b) : RealRaw :=
  Certificate.realRaw c.certificate

/-- Linearity in the first argument.  The construction data for
the left and right sides may differ; equality is interval-overlap equivalence
of the resulting computable reals. -/
def Linear : Prop :=
  forall (f g : RealFunRaw) (a b : Rat)
    (cf : Construction f a b)
    (cg : Construction g a b)
    (cadd : Construction (RealFunRaw.add f g) a b)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integral f a b cf) (integral g a b cg))),
      (integral (RealFunRaw.add f g) a b cadd).Equiv
        { compute := RealRaw.addCompute (integral f a b cf) (integral g a b cg) }

/-- Rational scalar compatibility. -/
def CompatibleWithScaleRat : Prop :=
  forall (r : Rat) (f : RealFunRaw) (a b : Rat)
    (cf : Construction f a b)
    (cscale : Construction (RealFunRaw.scaleRat r f) a b)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (integral f a b cf))),
      (integral (RealFunRaw.scaleRat r f) a b cscale).Equiv
        { compute := RealRaw.scaleRatCompute r (integral f a b cf) }

/-- Compatibility with adjoining intervals:
`integral a c f = integral a b f + integral b c f`. -/
def AdditiveOnAdjacentIntervals : Prop :=
  forall (f : RealFunRaw) (a b c : Rat)
    (cab : Construction f a b)
    (cbc : Construction f b c)
    (cac : Construction f a c)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integral f a b cab) (integral f b c cbc))),
      (integral f a c cac).Equiv
        { compute := RealRaw.addCompute (integral f a b cab) (integral f b c cbc) }

end Integral

/-- Target: constructive integrability of a real interval evaluator.

This is the theorem we want for the integral before FTC: under the
right effective continuity and boundedness hypotheses, one should be able to
choose plans whose interval sums form a valid `RealRaw`.  The exact
hypotheses will be sharpened as the continuity layer matures. -/
def Integral.ExistsConstruction (f : RealFunRaw) (a b : Rat) : Prop :=
  Nonempty (Integral.Construction f a b)

def endpointDifferenceInterval (F : RealFunRaw) (a b : Rat) (prec : Nat) : QInterval :=
  let A := F.compute a prec
  let B := F.compute b prec
  { lo := B.lo - A.hi, hi := B.hi - A.lo }

def endpointDifferenceCompute (F : RealFunRaw) (a b : Rat) : Nat -> QInterval :=
  fun prec => endpointDifferenceInterval F a b prec

def endpointDifferenceRaw (F : RealFunRaw) (a b : Rat)
    (_h : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) : RealRaw where
  compute := endpointDifferenceCompute F a b

/-- Preferred computable-number form of the definite-integral conclusion:
the integral of `dF` over the specific interval `[a,b]` is equal, as a
computable real number, to `F(b)-F(a)`.

Equality of computable reals is `RealRaw.Equiv`: at every requested precision,
the two rational intervals overlap. -/
def DefiniteIntegralEqualsEndpointDifference
    (F dF : RealFunRaw) (a b : Rat)
    (c : Integral.Construction dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) : Prop :=
  (Integral.integral dF a b c).Equiv
    (endpointDifferenceRaw F a b hendpoint)

/-- The computable-number conclusion of FTC.

Here `F` is the function being differentiated and `dF` is its derivative.  The
statement says that the definite integral of `dF` over `[a,b]`, computed by
finite interval sums, overlaps the endpoint difference `F(b)-F(a)` at every
requested rational precision.  The derivative certificate itself lives in the
differential layer, where functions carry interval domains. -/
structure EffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseN : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b (chooseN eps) (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

def ftcErrorExact (F dF : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  qabs (riemannLeftExact dF a b n - (F b - F a))

def ftcCheckExact (F dF : Rat -> Rat) (a b tolerance : Rat) (n : Nat) : Bool :=
  decide (ftcErrorExact F dF a b n <= tolerance)

/-- Exact rational-function FTC data.

The hypothesis is explicit: `dF` is an effective derivative of `F`.  The
conclusion is the definite-integral statement: for every positive rational
precision, a finite left sum for `dF` over `[a,b]` is within that precision of
`F(b)-F(a)`. -/
structure EffectiveFTCExact (F dF : Rat -> Rat) (a b : Rat) where
  derivative : EffectiveDerivativeExact F dF
  chooseN : QPos -> Nat
  good : forall eps, ftcErrorExact F dF a b (chooseN eps) <= eps.val

def inDomainInterval (a b x : Rat) : Prop :=
  a <= x /\ x <= b

def subintervalOf (I : QInterval) (a b : Rat) : Prop :=
  a <= I.lo /\ I.lo <= I.hi /\ I.hi <= b

/-- A partial function together with a proof that it is defined at every
rational point of a closed rational interval.

This rules out visible rational-domain failures, such as `1/x` on an interval
containing `0`.  It does not by itself rule out a hidden irrational singularity
such as `1 / (x^2 - 2)` on `[1,2]`, because every rational point of `[1,2]`
is still in the pointwise domain.  That stronger exclusion is the job of
`IntervalRegularOn` below. -/
structure FunctionOnInterval where
  raw : PartialRealFunRaw
  lower : Rat
  upper : Rat
  defined_on : forall x, inDomainInterval lower upper x -> raw.definedAt x
  valid_on : forall x h, RealRaw.ValidCompute (raw.compute x h)

namespace FunctionOnInterval

def compute (F : FunctionOnInterval) (x : Rat) (hx : inDomainInterval F.lower F.upper x)
    (n : Nat) : QInterval :=
  F.raw.compute x (F.defined_on x hx) n

end FunctionOnInterval

namespace Integral

/-- Project-facing integral construction for a partial function on a whole
rational interval.

The detailed Riemann-sum construction still needs to be proved.  This shape is
only the first domain gate: `FunctionOnInterval` supplies pointwise rational
evaluation, while the intended integral-existence theorem should consume
`IntervalRegularOn` to exclude hidden singularities inside rational
subintervals. -/
structure ConstructionFor (F : FunctionOnInterval) where
  compute : Nat -> QInterval
  certificate : RealRaw.ValidCompute compute

def integralFor (F : FunctionOnInterval) (c : ConstructionFor F) : RealRaw where
  compute := c.compute

end Integral

def Integral.ExistsConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (Integral.ConstructionFor F)

theorem integral_construction_proves_well_defined_for
    {F : FunctionOnInterval}
    (c : Integral.ConstructionFor F) :
    Integral.ExistsConstructionFor F :=
  ⟨c⟩

/-- Effective modulus for a partial function known to be defined on the whole
interval.  This is the continuity data used by IVT and eventually by the
integral constructor; it includes the domain certificate. -/
structure EffectiveModulusFor (F : FunctionOnInterval) where
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalCloseAtPrecision
          (F.compute x hx (evalPrecision n))
          (F.compute y hy (evalPrecision n))
          n

/-- Generic interval-level regularity.

This is the continuity notion we want calculus theorems to consume.  It does
not mention denominators or formulas.  It says that every sufficiently small
rational subinterval has a computable output interval, and that the output
interval can be made as narrow as requested.  A hidden singularity such as
`1 / (x^2 - 2)` on `[1,2]` should fail this condition, because arbitrarily
small rational subintervals can straddle the irrational pole. -/
structure IntervalRegularOn (F : FunctionOnInterval) where
  evalInterval : (I : QInterval) -> subintervalOf I F.lower F.upper -> Nat -> QInterval
  inputPrecision : Nat -> Nat
  output_width :
    forall I hI n,
      I.width <= (1 / ((inputPrecision n) : Rat)) ->
        0 <= (evalInterval I hI n).width /\
        (evalInterval I hI n).width <= (1 / (n : Rat))
  contains_point_values :
    forall I hI x hx n,
      I.lo <= x ->
      x <= I.hi ->
      QInterval.Overlaps
        (F.compute x hx n)
        (evalInterval I hI n)

/-- A certified continuous function on a rational interval.

This is the theorem-facing package.  `FunctionOnInterval` says the evaluator is
available at rational points on the interval; `regular` is the interval-level
continuity data that lets us choose subdivisions and evaluation precision. -/
structure ContinuousFunctionOnInterval where
  function : FunctionOnInterval
  regular : IntervalRegularOn function

/-- Constructive monotonicity on rational points of the interval.

The proposition allows increasing or decreasing functions; this is order data,
not yet enough to build an inverse algorithm by itself. -/
structure MonotoneOnInterval (F : FunctionOnInterval) where
  increasing : Prop
  monotone_inc :
    increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute x hx n).lo <= (F.compute y hy n).hi
  monotone_dec :
    ¬ increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute y hy n).lo <= (F.compute x hx n).hi

/-- Effective inverse separation.

This is the extra constructive ingredient beyond monotonicity.  It says that
when two rational inputs are separated by the supplied amount, their interval
values are separated enough to locate the inverse at the requested precision.
Without this, a monotone function can be too flat for an effective inverse
algorithm. -/
structure EffectiveInverseSeparation (F : FunctionOnInterval) where
  inputPrecision : Nat -> Nat
  outputPrecision : Nat -> Nat
  separated_inc :
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y)
      n,
      x + (1 / ((inputPrecision n) : Rat)) <= y ->
        (F.compute x hx (outputPrecision n)).hi <=
          (F.compute y hy (outputPrecision n)).lo
  separated_dec :
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y)
      n,
      x + (1 / ((inputPrecision n) : Rat)) <= y ->
        (F.compute y hy (outputPrecision n)).hi <=
          (F.compute x hx (outputPrecision n)).lo

/-- The input data from which an inverse-function algorithm should be
constructible. -/
structure InvertibleFunctionOnInterval where
  continuous : ContinuousFunctionOnInterval
  monotone : MonotoneOnInterval continuous.function
  separation : EffectiveInverseSeparation continuous.function

namespace InvertibleFunctionOnInterval

def function (I : InvertibleFunctionOnInterval) : FunctionOnInterval :=
  I.continuous.function

end InvertibleFunctionOnInterval

/-- A computable target value in the range of an interval function.

The range certificate is intentionally interval-valued.  It says every target
approximation lies between the endpoint value boxes at the chosen precision,
with orientation handled by the inverse construction. -/
structure InRangeRaw (I : InvertibleFunctionOnInterval) where
  value : RealRaw
  in_range : Prop

/-- A raw inverse evaluator on computable real target values.

It is partial because the inverse is only defined on the certified output
range.  The `compute_preimage` field returns a rational interval in the
original domain containing an input whose function value matches the output
target at the requested scale. -/
structure InverseRaw (I : InvertibleFunctionOnInterval) where
  compute_preimage : InRangeRaw I -> Nat -> QInterval
  valid_preimage : forall y, RealRaw.ValidCompute (compute_preimage y)
  preimage_subinterval : forall y n,
    subintervalOf (compute_preimage y n) I.function.lower I.function.upper
  value_overlaps :
    forall y n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage y n)
          (preimage_subinterval y n)
          n)
        (y.value.compute n)

namespace InverseRaw

def apply {I : InvertibleFunctionOnInterval} (inv : InverseRaw I) (y : InRangeRaw I) :
    RealRaw where
  compute := inv.compute_preimage y

theorem apply_valid {I : InvertibleFunctionOnInterval} (inv : InverseRaw I)
    (y : InRangeRaw I) :
    RealRaw.Valid (inv.apply y) :=
  inv.valid_preimage y

theorem apply_stays_in_source {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n, subintervalOf ((inv.apply y).compute n) I.function.lower I.function.upper :=
  inv.preimage_subinterval y

theorem apply_value_overlaps_target {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          ((inv.apply y).compute n)
          (apply_stays_in_source inv y n)
          n)
        (y.value.compute n) :=
  inv.value_overlaps y

end InverseRaw

/-- Constructive inverse function theorem on intervals. -/
def HasInverse : Prop :=
  forall I : InvertibleFunctionOnInterval, Nonempty (InverseRaw I)

/-- The remaining algorithmic step for the inverse function theorem:
construct the inverse intervals by bisection/search. -/
structure InverseBisectionSearch (I : InvertibleFunctionOnInterval) (y : InRangeRaw I) where
  compute_preimage : Nat -> QInterval
  valid_preimage : RealRaw.ValidCompute compute_preimage
  preimage_subinterval :
    forall n, subintervalOf (compute_preimage n) I.function.lower I.function.upper
  value_overlaps :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage n)
          (preimage_subinterval n)
          n)
        (y.value.compute n)

def HasBisectionSearch : Prop :=
  forall I : InvertibleFunctionOnInterval,
    forall y : InRangeRaw I,
      Nonempty (InverseBisectionSearch I y)

def inverseRawOfSearch {I : InvertibleFunctionOnInterval}
    (search : forall y : InRangeRaw I, InverseBisectionSearch I y) :
    InverseRaw I where
  compute_preimage := fun y => (search y).compute_preimage
  valid_preimage := fun y => (search y).valid_preimage
  preimage_subinterval := fun y => (search y).preimage_subinterval
  value_overlaps := fun y => (search y).value_overlaps

theorem inverse_function_from_bisection_search
    (hsearch : forall I : InvertibleFunctionOnInterval,
      forall y : InRangeRaw I, InverseBisectionSearch I y) :
    HasInverse := by
  intro I
  exact ⟨inverseRawOfSearch (hsearch I)⟩
end ComputableAnalysis
