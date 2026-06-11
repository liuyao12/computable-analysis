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

def precisionAtStage (n : Nat) : QPos :=
  if hn : n = 0 then
      { val := 1, property := by grind }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

def intervalCloseAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.CloseAt I J (precisionAtStage n)

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

/-- Legacy convexity-facing FTC data.

This is the older certificate-shaped route: convexity is only a method for
obtaining the derivative bounds consumed by `DerivativeBoundFTC`.  The main
convex FTC should no longer be stated this way; it should start from exact
convexity and construct the one-sided derivative and its integral. -/
structure LegacyConvexFTC (F dF : RealFunRaw) (a b : Rat) where
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

namespace LegacyConvexFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk => (h.convexBound eps k hk).toDerivativeBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end LegacyConvexFTC

/-- Legacy convexity-facing FTC.

Once a convexity certificate has produced derivative bounds on the chosen
rational partition cells, the old effective FTC conclusion is exactly the
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
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  legacyConvexFTC h

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
