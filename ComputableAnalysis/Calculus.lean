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

private theorem riemannLeftInterval_point_fold_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi)
    (xs : List Nat) (acc : QInterval) (hacc : acc.lo = acc.hi) :
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).lo =
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).hi := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons k rest ih =>
      apply ih
      dsimp
      rw [hacc, hpoint (leftPoint a b subdivisions k)]

theorem riemannLeftInterval_point_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).lo =
      (riemannLeftInterval g a b subdivisions prec).hi := by
  unfold riemannLeftInterval
  exact riemannLeftInterval_point_fold_eq
    g a b subdivisions prec hpoint (List.range subdivisions)
    { lo := 0, hi := 0 } rfl

theorem riemannLeftInterval_point_width_zero
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).width = 0 := by
  have h := riemannLeftInterval_point_eq
    g a b subdivisions prec hpoint
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

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

def precisionAtStage (n : Nat) : QPos :=
  if hn : n = 0 then
      { val := 1, property := by grind }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

def intervalCloseAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.CloseAt I J (precisionAtStage n)

/-- Precision-indexed quantitative closeness for enclosures of possibly
distinct nearby values. -/
def intervalNearAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.NearAt I J (precisionAtStage n)

namespace QInterval

/-- A weak interval order: the two interval enclosures are compatible with
some value of the left endpoint being at most some value of the right endpoint.
This is the order notion used for qualitative monotonicity and convexity
certificates, where finite rational enclosures may still overlap. -/
def WeakLe (I J : QInterval) : Prop :=
  I.lo <= J.hi

/-- A strong interval order: every value in the left interval is at most every
value in the right interval.  This is useful for certified bounds. -/
def StrongLe (I J : QInterval) : Prop :=
  I.hi <= J.lo

def addInterval (I J : QInterval) : QInterval :=
  { lo := I.lo + J.lo, hi := I.hi + J.hi }

def scaleByRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def subInterval (I J : QInterval) : QInterval :=
  { lo := I.lo - J.hi, hi := I.hi - J.lo }

def divByRat (I : QInterval) (h : Rat) : QInterval :=
  scaleByRat (1 / h) I

/-- Interval enclosure of `(Fy - Fx) / dx`.  For a secant slope, `dx` will be
the rational difference `y - x`; the caller carries the proof that `x < y`. -/
def slopeBetween (Fy Fx : QInterval) (dx : Rat) : QInterval :=
  divByRat (subInterval Fy Fx) dx

end QInterval

/-- Effective modulus on a rational interval.

This is legacy pointwise-style continuity data used by the current FTC target.
Given an output precision `n`, it supplies:

* an input precision saying how close rational inputs must be;
* an evaluation precision saying how accurately to compute the function;
* a proof that sufficiently close inputs produce output intervals within the
  requested tolerance.

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
        intervalNearAtPrecision
          (f.compute x (evalPrecision n))
          (f.compute y (evalPrecision n))
          n

/- Constructive interval-sum integration. -/
namespace Integral

/-- Effective choices for computing an integral to a requested precision. -/
structure Plan where
  subdivisions : Nat
  evalPrecision : Nat

/-- The static dyadic mesh size used by the first integral algorithms.
Stage `n` has `2^n` equal subintervals, independent of the integrand values. -/
def staticDyadicSubdivisions (n : Nat) : Nat :=
  2 ^ n

/-- The default static dyadic Riemann plan: stage `n` uses `2^n` equal
subintervals and asks the integrand for precision `n`. -/
def staticDyadicPlan : Nat -> Plan :=
  fun n => { subdivisions := staticDyadicSubdivisions n, evalPrecision := n }

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

/-- The unproved static-dyadic raw Riemann algorithm.  Concrete integral
constructions add the certificate proving that these dyadic boxes are ordered,
nested, and shrinking for the integrand at hand. -/
def staticDyadicAlgorithm (f : RealFunRaw) (a b : Rat) : Raw :=
  algorithm f a b staticDyadicPlan

/-- The explicit data needed to construct an integral as a computable
real.  The public object is still `integral`; this structure just stores the
algorithmic choices and the proof that they work. -/
structure Construction (f : RealFunRaw) (a b : Rat) where
  plan : Nat -> Plan
  certificate : Certificate (algorithm f a b plan)

/-- The constructive integral operator. -/
def integral (f : RealFunRaw) (a b : Rat) (c : Construction f a b) : RealRaw :=
  Certificate.realRaw c.certificate

/-- The exact constant integrand `x ↦ c`, as a raw function. -/
def constantFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun _ => c)

/-- The exact linear primitive `x ↦ c*x`, used for the constant-integral
sanity check. -/
def linearPrimitiveFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun x => c * x)

/-- One-cell Riemann sums already compute constant integrands exactly. -/
def constantPlan : Nat -> Plan :=
  fun _ => { subdivisions := 1, evalPrecision := 0 }

theorem riemannLeftInterval_constant_one
    (c a b : Rat) (prec : Nat) :
    riemannLeftInterval (constantFunRaw c) a b 1 prec =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  unfold riemannLeftInterval constantFunRaw RealFunRaw.exact leftPoint mesh
  simp
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem constant_algorithm_compute
    (c a b : Rat) (n : Nat) :
    (algorithm (constantFunRaw c) a b constantPlan).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [Raw.compute, algorithm, constantPlan]
  exact riemannLeftInterval_constant_one c a b 0

/-- The exact one-cell constant-integrand algorithm is a valid integral
construction on every rational interval. -/
def constantConstruction (c a b : Rat) :
    Construction (constantFunRaw c) a b where
  plan := constantPlan
  certificate := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      rw [constant_algorithm_compute]
      simp [QInterval.width]
      grind [Rat.sub_eq_add_neg]
    · intro n m _hnm
      rw [constant_algorithm_compute, constant_algorithm_compute]
      simp
    · intro eps
      refine ⟨0, ?_⟩
      intro n _hn
      rw [constant_algorithm_compute]
      show (b - a) * c - (b - a) * c <= eps.val
      grind [Rat.sub_eq_add_neg]

theorem constantIntegral_compute
    (c a b : Rat) (n : Nat) :
    (integral (constantFunRaw c) a b (constantConstruction c a b)).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [integral, Certificate.realRaw, Raw.toRealRaw, constantConstruction,
    constant_algorithm_compute]

theorem constantIntegral_valid (c a b : Rat) :
    (integral (constantFunRaw c) a b (constantConstruction c a b)).Valid :=
  (constantConstruction c a b).certificate.valid

/-- Constant integrals respect pointwise addition. -/
theorem constantIntegral_add_equiv (c d a b : Rat) :
    (integral (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).Equiv
        { compute := RealRaw.addCompute
            (integral (constantFunRaw c) a b
              (constantConstruction c a b))
            (integral (constantFunRaw d) a b
              (constantConstruction d a b)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).compute n)
    (RealRaw.addCompute
      (integral (constantFunRaw c) a b (constantConstruction c a b))
      (integral (constantFunRaw d) a b (constantConstruction d a b)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.addCompute
  rw [constantIntegral_compute c a b n, constantIntegral_compute d a b n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals respect rational scalar multiplication. -/
theorem constantIntegral_scaleRat_equiv (r c a b : Rat) :
    (integral (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).Equiv
        { compute := RealRaw.scaleRatCompute r
            (integral (constantFunRaw c) a b
              (constantConstruction c a b)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).compute n)
    (RealRaw.scaleRatCompute r
      (integral (constantFunRaw c) a b (constantConstruction c a b)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.scaleRatCompute
  rw [constantIntegral_compute c a b n]
  unfold QInterval.Overlaps
  by_cases hr : 0 <= r
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals are additive on adjacent rational intervals. -/
theorem constantIntegral_adjacent_additive (k a b c : Rat) :
    (integral (constantFunRaw k) a c
      (constantConstruction k a c)).Equiv
        { compute := RealRaw.addCompute
            (integral (constantFunRaw k) a b
              (constantConstruction k a b))
            (integral (constantFunRaw k) b c
              (constantConstruction k b c)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw k) a c
      (constantConstruction k a c)).compute n)
    (RealRaw.addCompute
      (integral (constantFunRaw k) a b (constantConstruction k a b))
      (integral (constantFunRaw k) b c (constantConstruction k b c)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.addCompute
  rw [constantIntegral_compute k a b n, constantIntegral_compute k b c n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

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

/-- Endpoint differences are valid whenever the primitive is valid at both
endpoints. -/
theorem endpointDifference_valid_of_fun_valid
    {F : RealFunRaw} (hF : F.Valid) {a b : Rat}
    (ha : F.domain a) (hb : F.domain b) :
    RealRaw.ValidCompute (endpointDifferenceCompute F a b) := by
  let A : RealRaw := F.apply hF a ha
  let B : RealRaw := F.apply hF b hb
  have hA : A.Valid := by
    simpa [A, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hsub := RealRaw.subCompute_valid hB hA
  simpa [A, B, endpointDifferenceCompute, endpointDifferenceInterval,
    RealFunRaw.apply, RealFunRaw.applyCompute, RealRaw.subCompute] using hsub

/-- Endpoint differences telescope over adjacent intervals:
\((F(b)-F(a))+(F(c)-F(b))\sim F(c)-F(a)\). -/
theorem endpointDifferenceRaw_adjacent_additive
    {F : RealFunRaw} (hF : F.Valid) {a b c : Rat}
    (ha : F.domain a) (hb : F.domain b) (hc : F.domain c)
    (hab : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (hbc : RealRaw.ValidCompute (endpointDifferenceCompute F b c))
    (hac : RealRaw.ValidCompute (endpointDifferenceCompute F a c)) :
    ((endpointDifferenceRaw F a b hab) +
      (endpointDifferenceRaw F b c hbc)).Equiv
        (endpointDifferenceRaw F a c hac) := by
  let A : RealRaw := F.apply hF a ha
  let B : RealRaw := F.apply hF b hb
  let C : RealRaw := F.apply hF c hc
  have hA : A.Valid := by
    simpa [A, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hC : C.Valid := by
    simpa [C, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF c hc
  simpa [A, B, C, endpointDifferenceRaw, endpointDifferenceCompute,
    endpointDifferenceInterval, RealFunRaw.apply, RealFunRaw.applyCompute,
    RealRaw.sub, RealRaw.subCompute] using
      (RealRaw.sub_add_sub_cancel_middle_equiv hA hB hC)

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

/-- Static-dyadic specialization of `EffectiveFTC`.

This is the certificate shape for the first bounded-integral algorithms:
for each requested rational precision choose a dyadic stage `s`, use
`2^s` equal subintervals of `[a,b]`, and compare the resulting left-Riemann
interval with the endpoint-difference interval. -/
structure StaticDyadicEffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseStage : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b
        (Integral.staticDyadicSubdivisions (chooseStage eps))
        (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

namespace StaticDyadicEffectiveFTC

/-- Forget that the subdivisions were chosen by the static dyadic mesh. -/
def toEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    EffectiveFTC F dF a b where
  chooseN := fun eps => Integral.staticDyadicSubdivisions (h.chooseStage eps)
  chooseEvalPrecision := h.chooseEvalPrecision
  good := h.good

end StaticDyadicEffectiveFTC

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

/-- A rational closed subinterval of a rational closed interval.  This is the
piece size used by the convex/concave calculus certificates below. -/
structure RationalSubinterval (a b : Rat) where
  lower : Rat
  upper : Rat
  lower_mem : a <= lower
  ordered : lower <= upper
  upper_mem : upper <= b

namespace RationalSubinterval

def contains {a b : Rat} (C : RationalSubinterval a b) (x : Rat) : Prop :=
  C.lower <= x /\ x <= C.upper

theorem contains_inDomain {a b : Rat} (C : RationalSubinterval a b)
    {x : Rat} (hx : C.contains x) :
    inDomainInterval a b x :=
  And.intro
    (Rat.le_trans C.lower_mem hx.1)
    (Rat.le_trans hx.2 C.upper_mem)

def whole (a b : Rat) (hab : a <= b) : RationalSubinterval a b where
  lower := a
  upper := b
  lower_mem := Rat.le_refl
  ordered := hab
  upper_mem := Rat.le_refl

def width {a b : Rat} (C : RationalSubinterval a b) : Rat :=
  C.upper - C.lower

def scaleBound {a b : Rat} (C : RationalSubinterval a b)
    (B : QInterval) : QInterval :=
  QInterval.scaleByRat C.width B

end RationalSubinterval

/-- A finite rational partition of `[a,b]`, represented by monotone rational
grid points.  The cells are the short intervals on which derivative bounds are
certified. -/
structure RationalPartition (a b : Rat) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = a
  right_endpoint : point pieces = b
  monotone :
    forall i j, i <= j -> j <= pieces -> point i <= point j

namespace RationalPartition

def cell {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) : RationalSubinterval a b where
  lower := P.point k
  upper := P.point (k + 1)
  lower_mem := by
    have hkPieces : k <= P.pieces := Nat.le_of_lt hk
    have h := P.monotone 0 k (Nat.zero_le k) hkPieces
    simpa [P.left_endpoint] using h
  ordered := by
    exact P.monotone k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
  upper_mem := by
    have h := P.monotone (k + 1) P.pieces (Nat.succ_le_of_lt hk) (Nat.le_refl P.pieces)
    simpa [P.right_endpoint] using h

def boundIntegralSum {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval) : QInterval :=
  (List.range P.pieces).foldl
    (fun acc k =>
      if hk : k < P.pieces then
        QInterval.addInterval acc ((P.cell k hk).scaleBound (bound k hk))
      else
        acc)
    { lo := 0, hi := 0 }

end RationalPartition

/-- A certified enclosure of derivative values on one rational subinterval.

This is the FTC-facing primitive: for every rational point in a short cell,
the pointwise derivative enclosure at the chosen evaluation precision is
contained in the supplied rational interval.  No convexity or differentiability
topology is mentioned here. -/
structure DerivativeBoundOnSubinterval
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (evalPrecision n))

/-- Local endpoint control supplied by a derivative bound.  This is the
constructive substitute for invoking a classical mean-value theorem: the
scaled derivative range encloses the endpoint difference of the primitive on
this short cell. -/
structure LocalFTCFromDerivativeBound
    (F dF : RealFunRaw) {a b : Rat}
    (C : RationalSubinterval a b)
    (B : DerivativeBoundOnSubinterval dF C) where
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  endpointPrecision : Nat -> Nat
  endpoint_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (B.bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

/-- Local finite certificate that a candidate derivative matches the computed
secant behavior of the original function on one rational cell.

The `bound` field is the common rational interval enclosure.  The
`candidate_contained` field says the candidate derivative `dF` lies in that
bound at every rational point of the cell.  The
`endpoint_difference_contained` field says the actual endpoint difference of
`F` on the same cell is contained in the cell width times that bound.  Thus the
candidate derivative is not guessed: it is certified against finite secant
inequalities for the concrete algorithm. -/
structure CandidateDerivativeCellControl
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  derivativeEvalPrecision : Nat -> Nat
  endpointPrecision : Nat -> Nat
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  candidate_domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  candidate_contained :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (derivativeEvalPrecision n))
  endpoint_difference_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

namespace CandidateDerivativeCellControl

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := H.bound
  evalPrecision := H.derivativeEvalPrecision
  domain_on := H.candidate_domain_on
  bound_ordered := H.bound_ordered
  contains_values := H.candidate_contained

def toLocalFTC
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    LocalFTCFromDerivativeBound F dF C H.toDerivativeBound where
  primitive_domain_lower := H.primitive_domain_lower
  primitive_domain_upper := H.primitive_domain_upper
  endpointPrecision := H.endpointPrecision
  endpoint_contained := H.endpoint_difference_contained

end CandidateDerivativeCellControl

/-- FTC data based on derivative bounds over short rational cells.

The FTC-facing assumption is the derivative-range bound on each cell.  How
those bounds are produced is deliberately separate: monotonicity, convexity,
concavity, power-series tails, or formula-specific interval arithmetic can all
feed the same structure.

For each requested rational precision `eps`, the certificate chooses a rational
partition of `[a,b]`, derivative enclosures on its cells, and an endpoint
evaluation precision for `F(b)-F(a)`.  The summed derivative-bound interval is
the Riemann-style enclosure; the theorem-facing obligations are exactly that
this enclosure has width at most `eps`, the endpoint-difference interval has
width at most `eps`, and the two intervals overlap. -/
structure DerivativeBoundFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundOnSubinterval dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          (derivativeBound eps k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace DerivativeBoundFTC

def boundedIntegralInterval
    {F dF : RealFunRaw} {a b : Rat}
  (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  (h.choosePartition eps).boundIntegralSum
    (fun k hk => (h.derivativeBound eps k hk).bound (h.chooseBoundStage eps))

def endpointInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  endpointDifferenceInterval F a b (h.chooseEndpointPrecision eps)

theorem closeAt
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt (h.boundedIntegralInterval eps) (h.endpointInterval eps) eps := by
  exact ⟨h.overlap eps, h.riemann_width eps, h.endpoint_width eps⟩

def boundedIntegralCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.boundedIntegralInterval (precisionAtStage n)

def endpointCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.endpointInterval (precisionAtStage n)

def boundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealRaw where
  compute := h.boundedIntegralCompute

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealRaw where
  compute := h.endpointCompute

/-- The derivative-bound FTC bridge, in computable-real form. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hgood := h.closeAt (precisionAtStage n)
  exact (RealRaw.compareAt_overlap_iff
    h.boundedIntegralRaw h.endpointRaw n n).2 hgood.1

end DerivativeBoundFTC

/-- Top-level derivative-bound FTC bridge.

This is the public theorem name for the finite cell-bound route: once the
derivative-bound certificate supplies overlapping bounded-sum and endpoint
intervals at every requested precision, the two raw real algorithms are
equivalent. -/
theorem derivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw :=
  h.equiv_endpoint

/-- Global finite certificate for the "candidate derivative versus computed
secants" strategy.

For each requested precision, choose a rational partition.  On each cell,
`cellControl` supplies one rational interval family that simultaneously:

* contains the candidate derivative values, and
* contains the actual endpoint secant behavior of `F` after scaling by the
  cell width.

The remaining fields are exactly the numerical FTC closure conditions: the
summed bound interval and the endpoint-difference interval are narrow and
overlap. -/
structure CandidateDerivativeFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  cellControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        CandidateDerivativeCellControl F dF ((choosePartition eps).cell k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CandidateDerivativeFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk =>
    (h.cellControl eps k hk).toDerivativeBound
  localControl := fun eps k hk =>
    (h.cellControl eps k hk).toLocalFTC
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

/-- The closure theorem for the candidate-derivative strategy. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CandidateDerivativeFTC

/-- Top-level closure theorem for the candidate-derivative strategy. -/
theorem candidateDerivativeFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

inductive MonotonicityKind where
  | nondecreasing
  | nonincreasing
deriving DecidableEq, Repr

def endpointDerivativeBound
    (kind : MonotonicityKind) (dF : RealFunRaw)
    {a b : Rat} (C : RationalSubinterval a b) (prec : Nat) : QInterval :=
  match kind with
  | .nondecreasing =>
      { lo := (dF.compute C.lower prec).lo,
        hi := (dF.compute C.upper prec).hi }
  | .nonincreasing =>
      { lo := (dF.compute C.upper prec).lo,
        hi := (dF.compute C.lower prec).hi }

/-- A common way to produce a derivative bound: prove the derivative is
monotone on the short cell, then use endpoint derivative enclosures as the
range bound. -/
structure MonotoneDerivativeBoundMethod
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : MonotonicityKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  endpoint_bound_ordered :
    forall n, 0 <= (endpointDerivativeBound kind dF C (evalPrecision n)).width
  endpoint_contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (endpointDerivativeBound kind dF C (evalPrecision n))
        (dF.compute x (evalPrecision n))

namespace MonotoneDerivativeBoundMethod

def toDerivativeBound
    {dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (M : MonotoneDerivativeBoundMethod dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := fun n => endpointDerivativeBound M.kind dF C (M.evalPrecision n)
  evalPrecision := M.evalPrecision
  domain_on := M.domain_on
  bound_ordered := M.endpoint_bound_ordered
  contains_values := M.endpoint_contains_values

end MonotoneDerivativeBoundMethod

inductive CurvatureKind where
  | convex
  | concave
deriving DecidableEq, Repr

namespace CurvatureKind

def derivativeMonotonicity : CurvatureKind -> MonotonicityKind
  | .convex => .nondecreasing
  | .concave => .nonincreasing

end CurvatureKind

def secantSlopeIntervalOfRealFun
    (F : RealFunRaw) (x y : Rat) (prec : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y prec) (F.compute x prec) (y - x)

/-- Rational secant-slope formulation of convexity/concavity on a short cell.

This is a helper certificate for producing derivative bounds.  The FTC layer
above only consumes `DerivativeBoundOnSubinterval`; it does not depend on this
curvature data directly. -/
structure CurvatureOnSubinterval
    (F : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : CurvatureKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> F.domain x
  secant_slope_order :
    forall n w x y z,
      C.contains w ->
      C.contains x ->
      C.contains y ->
      C.contains z ->
      w < x ->
      x <= y ->
      y < z ->
        match kind with
        | .convex =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
        | .concave =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))

/-- Evidence that a derivative bound was obtained through a curvature
argument: convexity supplies nondecreasing derivative bounds, concavity supplies
nonincreasing derivative bounds.  The result fed to FTC is still just
`toDerivativeBound`. -/
structure DerivativeBoundFromCurvature
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  curvature : CurvatureOnSubinterval F C
  monotoneDerivative : MonotoneDerivativeBoundMethod dF C
  compatible :
    monotoneDerivative.kind = curvature.kind.derivativeMonotonicity

namespace DerivativeBoundFromCurvature

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : DerivativeBoundFromCurvature F dF C) :
    DerivativeBoundOnSubinterval dF C :=
  H.monotoneDerivative.toDerivativeBound

end DerivativeBoundFromCurvature

/-- Curvature-facing FTC certificate.

This is the finite certificate-shaped route for primitives whose derivative
bounds come from curvature on each rational partition cell.  It handles both
convex and concave cells: the curvature kind determines whether endpoint
derivative bounds are nondecreasing or nonincreasing, and the result fed to the
FTC layer is still just a derivative-bound certificate. -/
structure CurvatureFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  curvatureBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((curvatureBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CurvatureFTCCertificate

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk => (h.curvatureBound eps k hk).toDerivativeBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CurvatureFTCCertificate

/-- Convexity-facing FTC certificate.

This is the current finite certificate-shaped route: convexity supplies
monotone derivative bounds on rational partition cells, and those local
bounds feed the general `DerivativeBoundFTC` endpoint bridge.

The later one-sided convex FTC should construct this certificate from exact
convexity, one-sided derivative data, monotone integrability, and telescoping
secant inequalities. -/
structure ConvexFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  convexBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  convex_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (convexBound eps k hk).curvature.kind = CurvatureKind.convex
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((convexBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

/-- Backward-compatible name for the older blueprint/API wording. -/
abbrev LegacyConvexFTC (F dF : RealFunRaw) (a b : Rat) :=
  ConvexFTCCertificate F dF a b

namespace ConvexFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.convexBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConvexFTCCertificate

/-- Concavity-facing FTC certificate.

This is the mirror of `ConvexFTCCertificate`.  It is the named finite
certificate route for primitives, such as arctangent on `[0,1]`, whose
curvature makes the derivative nonincreasing on each rational partition cell.
The certificate still feeds the same curvature and derivative-bound FTC
machinery. -/
structure ConcaveFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  concaveBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  concave_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (concaveBound eps k hk).curvature.kind = CurvatureKind.concave
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((concaveBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((concaveBound eps k hk).toDerivativeBound).bound
            (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((concaveBound eps k hk).toDerivativeBound).bound
              (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace ConcaveFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.concaveBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConcaveFTCCertificate

/- Legacy namespace aliases retained for existing references. -/
namespace LegacyConvexFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    DerivativeBoundFTC F dF a b :=
  ConvexFTCCertificate.toDerivativeBoundFTC h

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  ConvexFTCCertificate.equiv_endpoint h

end LegacyConvexFTC

/-- Compatibility theorem for the old convexity-facing FTC name.

Once a convexity certificate has produced derivative bounds on the chosen
rational partition cells, the finite FTC conclusion is exactly the
derivative-bound endpoint equivalence. -/
theorem legacyConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed convexity-facing FTC bridge used by the integral chapter.

This is currently the derivative-bound formulation: convexity supplies the
local monotone derivative bounds, and the general derivative-bound FTC returns
endpoint equivalence for the integral raw real. -/
theorem convexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed concavity-facing FTC bridge used by the arctangent-integral
route. -/
theorem concaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Curvature-facing FTC bridge.  This is the version useful for both convex
and concave primitives, including the arctangent primitive on the unit
interval. -/
theorem curvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

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

def secantSlopeInterval (F : FunctionOnInterval)
    (x y : Rat)
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y)
    (n : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y hy n) (F.compute x hx n) (y - x)

/-- Restrict an interval-certified function to a smaller rational interval. -/
def restrict (F : FunctionOnInterval) (a b : Rat)
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    FunctionOnInterval where
  raw := F.raw
  lower := a
  upper := b
  defined_on := by
    intro x hx
    exact F.defined_on x
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
  valid_on := by
    intro x hx
    exact F.valid_on x hx

/-- Pointwise sum relation for interval-certified functions on the same
rational interval.  This is a theorem-facing relation: it records that `H`
represents `F + G` on the common interval, without choosing a particular
implementation of the sum evaluator. -/
def PointwiseAdd (F G H : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  F.lower = H.lower /\ F.upper = H.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x)
    (hxH : inDomainInterval H.lower H.upper x),
      (H.raw.evalRaw x (H.defined_on x hxH)).Equiv
        ((F.raw.evalRaw x (F.defined_on x hxF)) +
          (G.raw.evalRaw x (G.defined_on x hxG)))

/-- Pointwise rational-scalar relation for interval-certified functions. -/
def PointwiseScaleRat (r : Rat) (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (G.raw.evalRaw x (G.defined_on x hxG)).Equiv
        (RealRaw.scaleRat r
          (F.raw.evalRaw x (F.defined_on x hxF)))

/-- Pointwise order relation for interval-certified functions on the same
rational interval.  This is the order analogue of `PointwiseAdd`: it records
the theorem-facing fact that `F(x) <= G(x)` for every rational point in the
common interval. -/
def PointwiseLe (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (F.raw.evalRaw x (F.defined_on x hxF)).Le
        (G.raw.evalRaw x (G.defined_on x hxG))

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

theorem integralFor_compute_eq (F : FunctionOnInterval)
    (c : ConstructionFor F) (n : Nat) :
    (integralFor F c).compute n = c.compute n := rfl

theorem integralFor_valid (F : FunctionOnInterval)
    (c : ConstructionFor F) :
    (integralFor F c).Valid :=
  c.certificate

end Integral

def Integral.ExistsConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (Integral.ConstructionFor F)

theorem integral_construction_proves_well_defined_for
    {F : FunctionOnInterval}
    (c : Integral.ConstructionFor F) :
    Integral.ExistsConstructionFor F :=
  ⟨c⟩

/-- Epsilon-delta continuity stated entirely over rational inputs.

For a requested positive rational output tolerance `eps`, the certificate
chooses a positive rational input tolerance and one evaluation precision. Any
two rational points of the stated interval within that tolerance then have
output boxes within `eps` of one another, each of width at most `eps`.  This
is quantitative proximity, not literal overlap: a nonconstant function can
send nearby rational inputs to distinct exact rational values.  No topology,
completed real-valued function space, or implicit exact-value evaluation
occurs here.
`EffectiveModulusFor` below is the stronger computable-modulus presentation
used by the current calculus constructors. -/
def EpsilonDeltaContinuousOn (F : FunctionOnInterval) : Prop :=
  forall eps : QPos, Exists fun delta : QPos => Exists fun evalPrecision : Nat =>
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= delta.val ->
        QInterval.NearAt
          (F.compute x hx evalPrecision)
          (F.compute y hy evalPrecision) eps

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
        intervalNearAtPrecision
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

The field `increasing` means nondecreasing; its negation selects the
nonincreasing case.  This is order data, not yet enough to build an inverse
algorithm by itself. -/
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

/-- Nondecreasing means increasing in the weak order sense used by the
project: rational inputs with `x <= y` have compatible output intervals with
the value at `x` no larger than the value at `y`. -/
def NondecreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute x hx n).lo <= (F.compute y hy n).hi

/-- Nonincreasing is the reversed weak interval order. -/
def NonincreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute y hy n).lo <= (F.compute x hx n).hi

namespace MonotoneOnInterval

def ofNondecreasing {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := True
  monotone_inc := by
    intro _hinc
    exact h
  monotone_dec := by
    intro hfalse
    exact False.elim (hfalse trivial)

def ofNonincreasing {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := False
  monotone_inc := by
    intro hfalse
    cases hfalse
  monotone_dec := by
    intro _hdec
    exact h

theorem nondecreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hinc : h.increasing) :
    NondecreasingOnInterval F :=
  h.monotone_inc hinc

theorem nonincreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hdec : ¬ h.increasing) :
    NonincreasingOnInterval F :=
  h.monotone_dec hdec

def restrict {F : FunctionOnInterval}
    (h : MonotoneOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneOnInterval (F.restrict a b hlo hab hhi) where
  increasing := h.increasing
  monotone_inc := by
    intro hinc x y hx hy hxy n
    exact h.monotone_inc hinc x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n
  monotone_dec := by
    intro hdec x y hx hy hxy n
    exact h.monotone_dec hdec x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n

end MonotoneOnInterval

namespace NondecreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NondecreasingOnInterval

namespace NonincreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NonincreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NonincreasingOnInterval

namespace Integral

/-- The first-class integral object for monotone interval functions.

The intended construction is by lower and upper endpoint sums on a static
dyadic mesh, with width controlled by total variation times mesh size.  The
present structure separates that monotonicity certificate from the resulting
valid `ConstructionFor`, so later proofs can build the construction while
downstream calculus can already use the interface. -/
structure MonotoneConstructionFor (F : FunctionOnInterval) where
  monotone : MonotoneOnInterval F
  construction : ConstructionFor F

namespace MonotoneConstructionFor

def restrict {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneConstructionFor (F.restrict a b hlo hab hhi) where
  monotone := c.monotone.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end MonotoneConstructionFor

/-- The preferred first case for integrals: a certified nondecreasing
function together with its valid integral construction. -/
structure NondecreasingConstructionFor (F : FunctionOnInterval) where
  nondecreasing : NondecreasingOnInterval F
  construction : ConstructionFor F

namespace NondecreasingConstructionFor

def toMonotoneConstructionFor {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F) :
    MonotoneConstructionFor F where
  monotone := MonotoneOnInterval.ofNondecreasing c.nondecreasing
  construction := c.construction

def restrict {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingConstructionFor (F.restrict a b hlo hab hhi) where
  nondecreasing := c.nondecreasing.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end NondecreasingConstructionFor

def monotoneIntegralFor (F : FunctionOnInterval)
    (c : MonotoneConstructionFor F) : RealRaw :=
  integralFor F c.construction

theorem monotoneIntegralFor_valid (F : FunctionOnInterval)
    (c : MonotoneConstructionFor F) :
    (monotoneIntegralFor F c).Valid :=
  integralFor_valid F c.construction

def ExistsMonotoneConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (MonotoneConstructionFor F)

def nondecreasingIntegralFor (F : FunctionOnInterval)
    (c : NondecreasingConstructionFor F) : RealRaw :=
  integralFor F c.construction

theorem nondecreasingIntegralFor_valid (F : FunctionOnInterval)
    (c : NondecreasingConstructionFor F) :
    (nondecreasingIntegralFor F c).Valid :=
  integralFor_valid F c.construction

theorem nondecreasingIntegralFor_eq_monotoneIntegralFor
    (F : FunctionOnInterval) (c : NondecreasingConstructionFor F) :
    nondecreasingIntegralFor F c =
      monotoneIntegralFor F c.toMonotoneConstructionFor := rfl

def ExistsNondecreasingConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (NondecreasingConstructionFor F)

/-- A piecewise-monotone integral plan: split an interval into finitely many
rational subintervals and supply a monotone construction on each piece. -/
structure PiecewiseMonotoneConstructionFor (F : FunctionOnInterval) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = F.lower
  right_endpoint : point pieces = F.upper
  point_mem :
    forall i, i <= pieces -> inDomainInterval F.lower F.upper (point i)
  point_mono :
    forall i j, i <= j -> j <= pieces -> point i <= point j
  construction :
    forall k (hk : k < pieces),
      MonotoneConstructionFor
        (F.restrict (point k) (point (k + 1))
          (point_mem k (Nat.le_of_lt hk)).1
          (point_mono k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk))
          (point_mem (k + 1) (Nat.succ_le_of_lt hk)).2)

namespace PiecewiseMonotoneConstructionFor

/-- Promote one monotone integral construction to the general piecewise
interface by using the one-cell partition `[lower, upper]`. -/
noncomputable def ofMonotone {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneConstructionFor F where
  pieces := 1
  positive := by decide
  point
    | 0 => F.lower
    | _ + 1 => F.upper
  left_endpoint := rfl
  right_endpoint := rfl
  point_mem := by
    intro i _hi
    cases i with
    | zero =>
        exact ⟨Rat.le_refl, hinterval⟩
    | succ _ =>
        exact ⟨hinterval, Rat.le_refl⟩
  point_mono := by
    intro i j hij _hj
    cases i with
    | zero =>
        cases j with
        | zero =>
            exact Rat.le_refl
        | succ _ =>
            exact hinterval
    | succ i' =>
        cases j with
        | zero =>
            exact False.elim (Nat.not_succ_le_zero i' hij)
        | succ _ =>
            exact Rat.le_refl
  construction := by
    intro k hk
    have hk_le_zero : k <= 0 := Nat.le_of_lt_succ hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk_le_zero
    subst k
    simpa using
      c.restrict
        Rat.le_refl
        hinterval
        Rat.le_refl

/-- Promote the preferred nondecreasing integral construction to the general
piecewise interface. -/
noncomputable def ofNondecreasing {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneConstructionFor F :=
  ofMonotone c.toMonotoneConstructionFor hinterval

end PiecewiseMonotoneConstructionFor

/-- The integral raw real for a single monotone piece of a piecewise-monotone
construction. -/
def piecewiseMonotoneCellIntegral (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (k : Nat) (hk : k < c.pieces) : RealRaw :=
  monotoneIntegralFor _ (c.construction k hk)

theorem piecewiseMonotoneCellIntegral_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (k : Nat) (hk : k < c.pieces) :
    (piecewiseMonotoneCellIntegral F c k hk).Valid :=
  monotoneIntegralFor_valid _ (c.construction k hk)

/-- Sum the monotone-piece integrals over the finite rational partition. -/
def piecewiseMonotoneIntegralFor (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F) : RealRaw :=
  (List.range c.pieces).foldl
    (fun acc k =>
      if hk : k < c.pieces then
        acc + piecewiseMonotoneCellIntegral F c k hk
      else
        acc)
    (RealRaw.ofRat 0)

theorem piecewiseMonotoneIntegralFor_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F) :
    (piecewiseMonotoneIntegralFor F c).Valid := by
  let step : RealRaw -> Nat -> RealRaw :=
    fun acc k =>
      if hk : k < c.pieces then
        acc + piecewiseMonotoneCellIntegral F c k hk
      else
        acc
  have hstep : forall acc k, acc.Valid -> (step acc k).Valid := by
    intro acc k hacc
    by_cases hk : k < c.pieces
    · simp [step, hk]
      exact RealRaw.add_valid hacc
        (piecewiseMonotoneCellIntegral_valid F c k hk)
    · simp [step, hk, hacc]
  have hfold :
      forall (xs : List Nat) (acc : RealRaw),
        acc.Valid -> (xs.foldl step acc).Valid := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons k ks ih =>
        intro acc hacc
        simpa [List.foldl] using ih (step acc k) (hstep acc k hacc)
  simpa [piecewiseMonotoneIntegralFor, step] using
    hfold (List.range c.pieces) (RealRaw.ofRat 0) (by
    simpa [RealRaw.Valid, RealRaw.ofRat] using RealRaw.ofRat_valid 0)

/-- A one-piece promotion from a monotone construction computes the same raw
integral as the original monotone construction. -/
theorem piecewiseMonotoneIntegralFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneIntegralFor F c) := by
  simpa [piecewiseMonotoneIntegralFor, piecewiseMonotoneCellIntegral,
    PiecewiseMonotoneConstructionFor.ofMonotone,
    MonotoneConstructionFor.restrict, monotoneIntegralFor, integralFor,
    RealRaw.zero] using
    (RealRaw.zero_add_equiv
      (monotoneIntegralFor_valid F c))

/-- The preferred nondecreasing one-piece promotion is compatible with the
general piecewise-monotone integral. -/
theorem piecewiseMonotoneIntegralFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingIntegralFor F c) := by
  simpa [PiecewiseMonotoneConstructionFor.ofNondecreasing,
    NondecreasingConstructionFor.toMonotoneConstructionFor,
    nondecreasingIntegralFor, monotoneIntegralFor] using
    (piecewiseMonotoneIntegralFor_ofMonotone_equiv
      (F := F) c.toMonotoneConstructionFor hinterval)

def ExistsPiecewiseMonotoneConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (PiecewiseMonotoneConstructionFor F)

/-- Project-facing name for the general definite integral interface:
construct the integral on monotone pieces and sum over a finite rational
partition. -/
abbrev GeneralConstructionFor (F : FunctionOnInterval) :=
  PiecewiseMonotoneConstructionFor F

def generalIntegralFor (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) : RealRaw :=
  piecewiseMonotoneIntegralFor F c

theorem generalIntegralFor_valid (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) :
    (generalIntegralFor F c).Valid :=
  piecewiseMonotoneIntegralFor_valid F c

/-- The public general-integral alias agrees with the original monotone
construction on a one-piece partition. -/
theorem generalIntegralFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneIntegralFor F c) := by
  simpa [generalIntegralFor] using
    piecewiseMonotoneIntegralFor_ofMonotone_equiv
      (F := F) c hinterval

/-- The public general-integral alias agrees with the preferred
nondecreasing construction on a one-piece partition. -/
theorem generalIntegralFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingIntegralFor F c) := by
  simpa [generalIntegralFor] using
    piecewiseMonotoneIntegralFor_ofNondecreasing_equiv
      (F := F) c hinterval

abbrev ExistsGeneralConstructionFor (F : FunctionOnInterval) : Prop :=
  ExistsPiecewiseMonotoneConstructionFor F

/-- Domain-aware linearity target for the eventual integral operator. -/
def LinearFor : Prop :=
  forall (F G H : FunctionOnInterval)
    (_hadd : F.PointwiseAdd G H)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G)
    (cH : ConstructionFor H)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integralFor F cF) (integralFor G cG))),
      (integralFor H cH).Equiv
        { compute := RealRaw.addCompute (integralFor F cF) (integralFor G cG) }

/-- Domain-aware rational scalar compatibility target. -/
def CompatibleWithScaleRatFor : Prop :=
  forall (r : Rat) (F G : FunctionOnInterval)
    (_hscaleFun : F.PointwiseScaleRat r G)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (integralFor F cF))),
      (integralFor G cG).Equiv
        { compute := RealRaw.scaleRatCompute r (integralFor F cF) }

/-- Domain-aware adjacent-interval additivity target. -/
def AdditiveOnAdjacentIntervalsFor : Prop :=
  forall (F : FunctionOnInterval) (a b c : Rat)
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c) (hc : c <= F.upper)
    (cab : ConstructionFor
      (F.restrict a b ha hab (Rat.le_trans hbc hc)))
    (cbc : ConstructionFor
      (F.restrict b c (Rat.le_trans ha hab) hbc hc))
    (cac : ConstructionFor
      (F.restrict a c ha (Rat.le_trans hab hbc) hc))
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (integralFor (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
        (integralFor (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc))),
      (integralFor (F.restrict a c ha (Rat.le_trans hab hbc) hc) cac).Equiv
        { compute := RealRaw.addCompute
            (integralFor (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
            (integralFor (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc) }

/-- Domain-aware order-preservation target for the eventual integral operator:
pointwise order of integrands should imply order of their integrals. -/
def OrderPreservingFor : Prop :=
  forall (F G : FunctionOnInterval)
    (_hle : F.PointwiseLe G)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G),
      (integralFor F cF).Le (integralFor G cG)

/-- Bundle of the basic algebra laws expected of the domain-aware integral.

The individual fields stay proposition-shaped because `ConstructionFor` is an
arbitrary valid raw algorithm.  Concrete integral constructors, such as the
monotone and piecewise-monotone constructors, should provide this package once
their finite-sum comparison proofs are available. -/
structure BasicPropertiesFor where
  linear : LinearFor
  scaleRat : CompatibleWithScaleRatFor
  adjacent_additive : AdditiveOnAdjacentIntervalsFor
  order_preserving : OrderPreservingFor

/-- Linearity target for the piecewise-monotone integral operator. -/
def PiecewiseMonotoneLinearFor : Prop :=
  forall (F G H : FunctionOnInterval)
    (_hadd : F.PointwiseAdd G H)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G)
    (cH : PiecewiseMonotoneConstructionFor H)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (piecewiseMonotoneIntegralFor F cF)
        (piecewiseMonotoneIntegralFor G cG))),
      (piecewiseMonotoneIntegralFor H cH).Equiv
        { compute := RealRaw.addCompute
            (piecewiseMonotoneIntegralFor F cF)
            (piecewiseMonotoneIntegralFor G cG) }

/-- Rational scalar compatibility target for the piecewise-monotone integral
operator. -/
def PiecewiseMonotoneCompatibleWithScaleRatFor : Prop :=
  forall (r : Rat) (F G : FunctionOnInterval)
    (_hscaleFun : F.PointwiseScaleRat r G)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (piecewiseMonotoneIntegralFor F cF))),
      (piecewiseMonotoneIntegralFor G cG).Equiv
        { compute := RealRaw.scaleRatCompute r
            (piecewiseMonotoneIntegralFor F cF) }

/-- Adjacent-interval additivity target for the piecewise-monotone integral
operator. -/
def PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor : Prop :=
  forall (F : FunctionOnInterval) (a b c : Rat)
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c) (hc : c <= F.upper)
    (cab : PiecewiseMonotoneConstructionFor
      (F.restrict a b ha hab (Rat.le_trans hbc hc)))
    (cbc : PiecewiseMonotoneConstructionFor
      (F.restrict b c (Rat.le_trans ha hab) hbc hc))
    (cac : PiecewiseMonotoneConstructionFor
      (F.restrict a c ha (Rat.le_trans hab hbc) hc))
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (piecewiseMonotoneIntegralFor
          (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
        (piecewiseMonotoneIntegralFor
          (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc))),
      (piecewiseMonotoneIntegralFor
        (F.restrict a c ha (Rat.le_trans hab hbc) hc) cac).Equiv
        { compute := RealRaw.addCompute
            (piecewiseMonotoneIntegralFor
              (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
            (piecewiseMonotoneIntegralFor
              (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc) }

/-- Order-preservation target for the piecewise-monotone integral operator. -/
def PiecewiseMonotoneOrderPreservingFor : Prop :=
  forall (F G : FunctionOnInterval)
    (_hle : F.PointwiseLe G)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G),
      (piecewiseMonotoneIntegralFor F cF).Le
        (piecewiseMonotoneIntegralFor G cG)

/-- Bundle of the basic algebra laws for the intended general integral:
define on monotone pieces, then sum over a finite rational partition. -/
structure PiecewiseMonotoneBasicPropertiesFor where
  linear : PiecewiseMonotoneLinearFor
  scaleRat : PiecewiseMonotoneCompatibleWithScaleRatFor
  adjacent_additive : PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor
  order_preserving : PiecewiseMonotoneOrderPreservingFor

abbrev GeneralLinearFor : Prop :=
  PiecewiseMonotoneLinearFor

abbrev GeneralCompatibleWithScaleRatFor : Prop :=
  PiecewiseMonotoneCompatibleWithScaleRatFor

abbrev GeneralAdditiveOnAdjacentIntervalsFor : Prop :=
  PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor

abbrev GeneralOrderPreservingFor : Prop :=
  PiecewiseMonotoneOrderPreservingFor

abbrev GeneralBasicPropertiesFor :=
  PiecewiseMonotoneBasicPropertiesFor

/-- Exact rational-cell order preservation for an integrand together with a
closed-form integral over rational cells.

This is the finite algebraic version of the order-preservation theorem for
integrals.  If `c` is a lower bound for `eval` on every rational point of
`[p,r]`, then `(r-p)*c` is a lower bound for the exact cell integral.  The
upper statement is analogous. -/
structure ExactCellOrderPreservation
    (eval : Rat -> Rat) (integralBetween : Rat -> Rat -> Rat)
    (a b : Rat) where
  lower_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> c <= eval x) ->
        (r - p) * c <= integralBetween p r
  upper_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> eval x <= c) ->
        integralBetween p r <= (r - p) * c

/-- Exact rational-cell order preservation for a constant integrand.

This is the base case for finite polynomial integral certificates: the exact
integral of the constant `k` over `[p,r]` is `(r-p) * k`.  It uses only the
order of rational multiplication, with no limiting or completeness argument.
-/
theorem exactCellOrderPreservation_constant (a b k : Rat) :
    ExactCellOrderPreservation (fun _ => k) (fun p r => (r - p) * k) a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hck : c <= k :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hck hlen
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hkc : k <= c :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hkc hlen

/-- Sum of the weights in a finite rational quadrature rule.  A pair stores a
relative node followed by its weight. -/
def quadratureWeightSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (_, weight) :: rest => weight + quadratureWeightSum rest

/-- Weighted evaluation sum for a finite rational quadrature rule on `[p,r]`.
The first component of each pair is its relative node in `[0,1]`. -/
def quadratureEvalSum (eval : Rat -> Rat) (p r : Rat) :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (node, weight) :: rest =>
      weight * eval (p + node * (r - p)) +
        quadratureEvalSum eval p r rest

private theorem quadratureWeightSum_mul_le_quadratureEvalSum
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> c <= eval x) :
    quadratureWeightSum nodes * c <= quadratureEvalSum eval p r nodes := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : c <= eval (p + node * (r - p)) :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * c <= weight * eval (p + node * (r - p)) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        (weight + quadratureWeightSum rest) * c =
            weight * c + quadratureWeightSum rest * c := by
          grind [Rat.add_mul]
        _ <= weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest := by
          calc
            weight * c + quadratureWeightSum rest * c <=
                weight * eval (p + node * (r - p)) +
                  quadratureWeightSum rest * c :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_left).2 htail

private theorem quadratureEvalSum_le_quadratureWeightSum_mul
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> eval x <= c) :
    quadratureEvalSum eval p r nodes <= quadratureWeightSum nodes * c := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : eval (p + node * (r - p)) <= c :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * eval (p + node * (r - p)) <= weight * c :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest <=
            weight * c + quadratureWeightSum rest * c := by
          calc
            weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest <=
                weight * c + quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * c + quadratureWeightSum rest * c :=
              (Rat.add_le_add_left).2 htail
        _ = (weight + quadratureWeightSum rest) * c := by
          grind [Rat.add_mul]

/-- A finite positive rational quadrature identity gives exact cell-order
preservation.  It applies to any finite rule whose nodes lie in `[0,1]`, whose
weights are nonnegative and sum to one, and whose formula is exact for the
specified integrand. -/
theorem exactCellOrderPreservation_of_positive_quadrature
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat) (nodes : List (Rat × Rat))
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hsum : quadratureWeightSum nodes = 1)
    (hformula : forall p r : Rat,
      integralBetween p r = (r - p) * quadratureEvalSum eval p r nodes) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureWeightSum_mul_le_quadratureEvalSum
      nodes hpr hnodes hweights hbound
    have haverage : c <= quadratureEvalSum eval p r nodes := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureEvalSum_le_quadratureWeightSum_mul
      nodes hpr hnodes hweights hbound
    have haverage : quadratureEvalSum eval p r nodes <= c := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength

/-- A positive Boole quadrature identity gives exact cell-order preservation.

The five rational nodes are the endpoints and the quarter points of a cell.
For a polynomial for which the displayed identity is exact, a pointwise bound
at all rational points bounds its exact integral.  The proof is finite rational
arithmetic; it invokes neither a limit nor real-number completeness. -/
theorem exactCellOrderPreservation_of_boole
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat)
    (hboole : forall p r : Rat,
      integralBetween p r =
        ((r - p) / 90) *
          (7 * eval p +
            32 * eval (p + (r - p) / 4) +
            12 * eval (p + (r - p) / 2) +
            32 * eval (p + 3 * (r - p) / 4) +
            7 * eval r)) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by native_decide) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by native_decide)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : c <= eval p := hbound (Rat.le_refl : p <= p) hpr
    have h1 : c <= eval q₁ := hbound hq₁.1 hq₁.2
    have h2 : c <= eval q₂ := hbound hq₂.1 hq₂.2
    have h3 : c <= eval q₃ := hbound hq₃.1 hq₃.2
    have hr : c <= eval r := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        90 * c <= 7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by native_decide : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by native_decide : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by native_decide : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by native_decide : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by native_decide : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by native_decide)
    rw [hboole]
    change L * c <=
      (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r)
    calc
      L * c = (L / 90) * (90 * c) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by native_decide) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by native_decide)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : eval p <= c := hbound (Rat.le_refl : p <= p) hpr
    have h1 : eval q₁ <= c := hbound hq₁.1 hq₁.2
    have h2 : eval q₂ <= c := hbound hq₂.1 hq₂.2
    have h3 : eval q₃ <= c := hbound hq₃.1 hq₃.2
    have hr : eval r <= c := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r <= 90 * c := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by native_decide : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by native_decide : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by native_decide : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by native_decide : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by native_decide : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by native_decide)
    rw [hboole]
    change (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r) <= L * c
    calc
      (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) <=
          (L / 90) * (90 * c) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
      _ = L * c := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end Integral

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
