import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.SinPiSquareCheckpoints
import ComputableAnalysis.EffectiveCalculusFoundation
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.SeriesFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteSineIntegral
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.Series
import ComputableAnalysis.FirstYearCalculus
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.FiniteFourierOrthogonality
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.ExponentialLogarithmFoundation
import ComputableAnalysis.ScalarODEUniqueness
import ComputableAnalysis.DifferentialEquationsFoundation
import ComputableAnalysis.PeanoBaker
import ComputableAnalysis.FiniteQuarticQuinticIntegrationByParts
import ComputableAnalysis.GeometricRotationODE
import ComputableAnalysis.RotationPeanoBakerBridge
import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteGaussianIntegral
import ComputableAnalysis.ComplexCircleBridge
import ComputableAnalysis.ComplexPathIntegral
import ComputableAnalysis.FiniteComplexPathCertificate
import ComputableAnalysis.IrrationalSqrt
import ComputableAnalysis.SqrtTwoDescent

/-!
# Computable calculus foundation

This is the focused public entry point for the project's calculus route.  It
collects the rational-circle, finite-integral, effective-FTC, power-series,
exponential/logarithm, Fourier, and scalar/linear-ODE interfaces without
requiring users to import the full benchmark catalogue in `ComputableAnalysis`.

The imports expose certificates and raw algorithms; they do not introduce a
completed real-number or measurable-function foundation.
-/

namespace ComputableAnalysis.ComplexPathIntegral

/-! Public complex FTC entry point for finite polygonal paths.  The path is a
finite list of rational-complex vertices and the primitive is supplied by its
finite polynomial coefficients, so the theorem is entirely algebraic. -/
theorem effectivePolynomialPathFTC
    (coefficients : List QComplex) (start endpoint : QComplex)
    (vertices : List QComplex) :
    (polygonalPolynomialIntegralRaw coefficients start
      (vertices ++ [endpoint])).Equiv
      (ComplexRaw.ofQComplex
        (polynomialPrimitiveIncrement coefficients start endpoint)) := by
  exact polygonalPolynomialIntegralRaw_equiv_endpoint
    coefficients start endpoint vertices

end ComputableAnalysis.ComplexPathIntegral

namespace ComputableAnalysis

/-! Public effective FTC bridge.  The certificate packages a finite
derivative-bound computation, its rational partition, and the width budget;
the result identifies the resulting raw integral with the certificate's
endpoint computation. -/
theorem effectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC h

theorem effectiveFTC_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  exact h.boundedIntegralRaw_equiv_endpointDifference hendpoint

/-! Public finite integration-by-parts laws.  These are the algebraic
rectangle identities behind later Stieltjes and change-of-variables proofs;
the variation term is retained explicitly rather than discarded by a limit. -/
theorem effectiveFiniteIntegrationByParts_onPartition {a b : Rat}
    (P : RationalPartition a b) (f g : Rat -> Rat) :
    leftStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces +
      rightStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces =
      f b * g b - f a * g a := by
  exact RationalPartition.finiteIntegrationByParts_onPartition P f g

theorem effectiveFiniteIntegrationByParts_withVariation_onPartition {a b : Rat}
    (P : RationalPartition a b) (f g : Rat -> Rat) :
    leftStieltjesSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces +
      leftStieltjesSum (fun i => g (P.clampedPath i))
        (fun i => f (P.clampedPath i)) P.pieces +
      quadraticVariationSum (fun i => f (P.clampedPath i))
        (fun i => g (P.clampedPath i)) P.pieces =
      f b * g b - f a * g a := by
  exact RationalPartition.finiteIntegrationByParts_withVariation_onPartition P f g

theorem effectiveCoordinateIntegrationByParts_endpointBracket {a b : Rat}
    (P : RationalPartition a b) (v : Rat -> Rat) (delta : Rat)
    (hstep : P.MaxStepAtMost delta)
    (hv : forall i, 0 <= v (P.clampedPath (i + 1)) -
      v (P.clampedPath i)) :
    b * v b - a * v a - delta * (v b - v a) <=
        leftStieltjesSum P.clampedPath
          (fun i => v (P.clampedPath i)) P.pieces +
      leftStieltjesSum (fun i => v (P.clampedPath i))
          P.clampedPath P.pieces /\
      leftStieltjesSum P.clampedPath
          (fun i => v (P.clampedPath i)) P.pieces +
        leftStieltjesSum (fun i => v (P.clampedPath i))
          P.clampedPath P.pieces <=
        b * v b - a * v a := by
  exact RationalPartition.coordinateIntegrationByParts_onPartition_endpoint_bracket
    P v delta hstep hv

/-! Public finite vector-ODE facade.  These are exact rational recurrence and
Duhamel identities; continuous coefficient and tail providers remain
explicit inputs in the ODE chapter. -/
theorem effectiveLinearODERecurrence_unique
    (system : LinearODE.DiscreteLinearSystem dimension)
    (initial : LinearODE.RatVector dimension)
    (candidate : Nat -> LinearODE.RatVector dimension)
    (hsolution : system.SolvesRecurrence initial candidate) :
    forall n, candidate n = system.trajectory initial n := by
  exact LinearODE.effectiveDiscreteRecurrence_unique
    system initial candidate hsolution

theorem effectiveLinearODEVariationOfConstants
    (system : LinearODE.DiscreteLinearSystem dimension)
    (initial : LinearODE.RatVector dimension) (n : Nat) :
    system.trajectory initial n =
      LinearODE.vectorAdd
        (LinearODE.matrixApply
          (LinearODE.chronologicalStepProduct system.step 0 n) initial)
        (system.trajectory (LinearODE.vectorZero dimension) n) := by
  exact LinearODE.effectiveDiscreteVariationOfConstants system initial n

theorem effectiveLinearODEDuhamel
    (system : LinearODE.DiscreteLinearSystem dimension)
    (initial : LinearODE.RatVector dimension) (n : Nat) :
    system.trajectory initial n =
      LinearODE.vectorAdd
        (LinearODE.matrixApply
          (LinearODE.chronologicalStepProduct system.step 0 n) initial)
        (LinearODE.DiscreteLinearSystem.duhamelSum system n) := by
  exact LinearODE.effectiveDiscreteVariationOfConstants_duhamel
    system initial n

def effectivePeanoBakerFactorialRemainderCertificate
    {M T : Rat} (hM : 0 <= M) (hT : 0 <= T) (eps : QPos) :
    LinearODE.PeanoBakerFactorialRemainderCertificate M T eps := by
  exact LinearODE.peanoBakerFactorialRemainderCertificate hM hT eps

theorem effectivePeanoBakerFactorialTail_le_eps
    {M T : Rat} (hM : 0 <= M) (hT : 0 <= T) (eps : QPos)
    (terms : Nat) :
    LinearODE.peanoBakerFactorialTail M T
      (RationalMajorant.factorialTailStart (M * T) +
        LinearODE.peanoBakerFactorialTailShift M T eps) terms <= eps.val := by
  exact LinearODE.peanoBakerFactorialTail_shifted_le_eps hM hT eps terms

/-! Public same-partition nesting theorem for interval-image Darboux stages.
The evaluator's cross-stage containment is an explicit hypothesis; this does
not silently provide the changing-partition nesting needed for a universal
integral. -/
theorem effectiveIntervalRegularDarbouxStage_contains_of_evalIntervalsNested
    (F : FunctionOnInterval) (hregular : IntervalRegularOn F)
    (hstage : Integral.IntervalRegularOn.EvalIntervalsNested hregular)
    (P : RationalPartition F.lower F.upper) {n m : Nat} (hnm : n <= m) :
    (Integral.intervalRegularDarbouxStage F hregular P n).ContainsInterval
      (Integral.intervalRegularDarbouxStage F hregular P m) := by
  exact Integral.intervalRegularDarbouxStage_contains_of_evalIntervalsNested
    F hregular hstage P hnm

/-! Public representation-chain transport.  A real uses a preferred raw
algorithm and parent-relative implementation edges; any two certified views
are interchangeable by transitivity.  Complex function views additionally
state the common-domain coverage needed to compose partial representations. -/
theorem effectiveRealRepresentation_equiv
    {x : Real} (source target : Real.Representation x) :
    source.raw.Equiv target.raw := by
  exact source.equiv target

theorem effectiveRealRepresentation_overlapsAt
    {x : Real} (source target : Real.Representation x) (stage : Nat) :
    QInterval.Overlaps (source.raw.compute stage) (target.raw.compute stage) := by
  exact source.overlapsAt target stage

theorem effectiveComplexFunctionRepresentation_overlapsAt_on_common_domain
    {f : ComplexFunction} (source target : ComplexFunction.Representation f)
    (hsource : forall z, source.raw.domain z -> f.preferred.domain z)
    {z : QComplex} (hzs : source.raw.domain z) (hzt : target.raw.domain z)
    (stage : Nat) :
    QBox.Overlaps
      (source.raw.compute z hzs stage) (target.raw.compute z hzt stage) := by
  exact ComplexFunction.Representation.overlapsAt_on_common_domain
    source target hsource hzs hzt stage

theorem effectiveComplexFunction_agreeOnCommonDomain_of_common_anchor
    {f g anchor : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) (ha : anchor.Valid)
    (hdom : forall z, f.domain z -> g.domain z -> anchor.domain z)
    (hfa : f.AgreeOnCommonDomain anchor)
    (hga : g.AgreeOnCommonDomain anchor) :
    f.AgreeOnCommonDomain g := by
  exact FunctionRaw.agreeOnCommonDomain_of_common_anchor
    hf hg ha hdom hfa hga

/-! Public conditional equal-dyadic sine transport.  The theorem consumes a
canonical finite half-angle certificate family and an independently certified
integral for the comparison evaluator; the geometric family is intentionally
not synthesized here. -/
theorem effectiveSinPiHalfIntegral_equiv_reciprocalPi_of_canonical_certificate_family
    (S : SinPiIntegral.ArctanSinPiConstruction)
    (pub : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        SinPiIntegral.dyadicNestedRadicalStageSinAt n k)
    (family : SinPiIntegral.DyadicCanonicalCertificateFamily S.inverse)
    (hintegral : (Integral.integral g 0 ((1 : Rat) / 2) cg).Equiv
      SinPiIntegral.reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv SinPiIntegral.reciprocalPiRaw := by
  exact S.halfIntegral_equiv_reciprocalPi_of_canonical_certificate_family
    pub g cg hdyadic hplan hevaluator family hintegral

theorem effectiveSineWitnessSearch_exists_of_overlap_of_positive_width
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1)
    (hover : QInterval.Overlaps
      (SinPiIntegral.rationalCircleSinInterval U) S)
    (hwidth : 0 < S.width) :
    ∃ m u, SinPiIntegral.rationalTangentWitnessBoxSearch U S m = some u := by
  exact SinPiIntegral.exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    hU hS hover hwidth

theorem effectiveIntervalRegularDarbouxSchedule_widths_shrink_of_budget
    {F : FunctionOnInterval} (hregular : IntervalRegularOn F)
    {hinterval : F.lower <= F.upper} (lengthBound : Nat)
    (hLength : F.upper - F.lower <= (lengthBound : Rat))
    (evalPrecision : Nat -> Nat)
    (hbudget : forall eps : QPos, Exists fun N : Nat =>
      forall n : Nat, N <= n ->
        (F.upper - F.lower) *
          (1 / ((evalPrecision n + 1 : Nat) : Rat)) <= eps.val) :
    RealRaw.WidthsShrinkToZero
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular
          lengthBound evalPrecision n)
        evalPrecision
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular
          lengthBound evalPrecision n)) := by
  exact Integral.intervalRegularDarbouxSchedule_widths_shrink_of_budget
    hregular lengthBound hLength evalPrecision hbudget

def effectiveIntervalRegularDarbouxSchedule_ofAutomaticPieces
    {F : FunctionOnInterval} (hregular : IntervalRegularOn F)
    {hinterval : F.lower <= F.upper} (lengthBound : Nat)
    (hLength : F.upper - F.lower <= (lengthBound : Rat))
    (evalPrecision : Nat -> Nat)
    (hbudget : forall eps : QPos, Exists fun N : Nat =>
      forall n : Nat, N <= n ->
        (F.upper - F.lower) *
          (1 / ((evalPrecision n + 1 : Nat) : Rat)) <= eps.val)
    (nested : forall n m, n <= m ->
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular
          lengthBound evalPrecision n)
        evalPrecision
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular
          lengthBound evalPrecision n) n).lo <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular
          lengthBound evalPrecision n)
        evalPrecision
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular
          lengthBound evalPrecision n) m).lo /\
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular
          lengthBound evalPrecision n)
        evalPrecision
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular
          lengthBound evalPrecision n) m).hi <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular
          lengthBound evalPrecision n)
        evalPrecision
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular
          lengthBound evalPrecision n) n).hi) :
    Integral.IntervalRegularDarbouxSchedule F hregular hinterval :=
  Integral.IntervalRegularDarbouxSchedule.ofAutomaticPieces hregular
    lengthBound hLength evalPrecision hbudget nested

theorem effectiveIntervalRegularDarbouxScheduleRaw_valid
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval) :
    (Integral.intervalRegularDarbouxScheduleRaw s).Valid := by
  exact Integral.intervalRegularDarbouxScheduleRaw_valid s

theorem effectiveIntervalRegularDarbouxScheduleRaw_precision_witness
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval)
    (eps : QPos) :
    ∃ n : Nat,
      ((Integral.intervalRegularDarbouxScheduleRaw s).compute n).width <= eps.val := by
  exact Integral.intervalRegularDarbouxScheduleRaw_precision_witness s eps

/-! Public finite multiple-integral bridge.  An outer right sum of inner
left sums is exactly the complementary one-dimensional rectangle sum. -/
theorem effectiveUniformTriangleRightSum_eq_complementUniformLeftEndpointSum
    (f : Rat -> Rat) (mesh : Nat) (hmesh : 0 < mesh) :
    ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformTriangleRightSum f mesh mesh =
      ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x => (1 - x) * f x) mesh := by
  exact ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformTriangleRightSum_eq_complementUniformLeftEndpointSum
    f mesh hmesh

/-! Public arbitrary-dimensional finite product-integral factorization. -/
theorem effectiveFiniteProductIntegralNestedSum_factorized
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat)) :
    finiteProductIntegralNestedSum samples factors =
      finiteProductIntegralSum samples factors := by
  exact finiteProductIntegralNestedSum_factorized samples factors

/-! General finite Fubini symmetry.  Cell values may depend on both sampled
coordinates; the theorem is just commutation of two finite rational folds and
does not assume separability, an integral operator, or a completed space. -/
theorem effectiveFiniteRectangularSum_swap {α β : Type}
    (xs : List α) (ys : List β) (h : α -> β -> Rat) :
    finiteRectangularSum xs ys h =
      finiteRectangularSum ys xs (fun y x => h x y) := by
  exact finiteRectangularSum_swap xs ys h

theorem effectiveFiniteRectangularSum_nonneg {α β : Type}
    (xs : List α) (ys : List β)
    (cellValue : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys -> 0 <= cellValue x y) :
    0 <= finiteRectangularSum xs ys cellValue := by
  exact finiteRectangularSum_nonneg xs ys cellValue h

theorem effectiveFiniteRectangularSum_mono {α β : Type}
    (xs : List α) (ys : List β)
    (lower upper : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      lower x y <= upper x y) :
    finiteRectangularSum xs ys lower <=
      finiteRectangularSum xs ys upper := by
  exact finiteRectangularSum_mono xs ys lower upper h

theorem effectiveFiniteRectangularSum_add {α β : Type}
    (xs : List α) (ys : List β)
    (f g : α -> β -> Rat) :
    finiteRectangularSum xs ys (fun x y => f x y + g x y) =
      finiteRectangularSum xs ys f + finiteRectangularSum xs ys g := by
  exact finiteRectangularSum_add xs ys f g

theorem effectiveFiniteRectangularSum_scale {α β : Type}
    (xs : List α) (ys : List β) (scale : Rat) (f : α -> β -> Rat) :
    finiteRectangularSum xs ys (fun x y => scale * f x y) =
      scale * finiteRectangularSum xs ys f := by
  exact finiteRectangularSum_scale xs ys scale f

theorem effectiveFiniteRectangularSum_congr {α β : Type}
    (xs : List α) (ys : List β)
    (f g : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys -> f x y = g x y) :
    finiteRectangularSum xs ys f = finiteRectangularSum xs ys g := by
  exact finiteRectangularSum_congr xs ys f g h

theorem effectiveFiniteWeightedRectangularSum_swap
    (xs ys : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys cellValue =
      finiteWeightedRectangularSum ys xs (fun y x => cellValue x y) := by
  exact finiteWeightedRectangularSum_swap xs ys cellValue

theorem effectiveFiniteWeightedRectangularSum_nonneg
    (xs ys : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      0 <= cellValue x.1 y.1) :
    0 <= finiteWeightedRectangularSum xs ys cellValue := by
  exact finiteWeightedRectangularSum_nonneg xs ys cellValue
    hwidthX hwidthY hvalue

theorem effectiveFiniteWeightedRectangularSum_mono
    (xs ys : List (Rat × Rat))
    (lower upper : Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      lower x.1 y.1 <= upper x.1 y.1) :
    finiteWeightedRectangularSum xs ys lower <=
      finiteWeightedRectangularSum xs ys upper := by
  exact finiteWeightedRectangularSum_mono xs ys lower upper
    hwidthX hwidthY hvalue

theorem effectiveFiniteWeightedRectangularSum_add
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys (fun x y => f x y + g x y) =
      finiteWeightedRectangularSum xs ys f +
        finiteWeightedRectangularSum xs ys g := by
  exact finiteWeightedRectangularSum_add xs ys f g

theorem effectiveFiniteWeightedRectangularSum_scale
    (xs ys : List (Rat × Rat)) (scale : Rat)
    (f : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys (fun x y => scale * f x y) =
      scale * finiteWeightedRectangularSum xs ys f := by
  exact finiteWeightedRectangularSum_scale xs ys scale f

theorem effectiveFiniteWeightedRectangularSum_congr
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      f x.1 y.1 = g x.1 y.1) :
    finiteWeightedRectangularSum xs ys f =
      finiteWeightedRectangularSum xs ys g := by
  exact finiteWeightedRectangularSum_congr xs ys f g h

theorem effectiveFiniteTripleRectangularSum_swap12 {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (cellValue : α -> β -> γ -> Rat) :
    finiteTripleRectangularSum xs ys zs cellValue =
      finiteTripleRectangularSum ys xs zs (fun y x z => cellValue x y z) := by
  exact finiteTripleRectangularSum_swap12 xs ys zs cellValue

theorem effectiveFiniteTripleRectangularSum_swap23 {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (cellValue : α -> β -> γ -> Rat) :
    finiteTripleRectangularSum xs ys zs cellValue =
      finiteTripleRectangularSum xs zs ys (fun x z y => cellValue x y z) := by
  exact finiteTripleRectangularSum_swap23 xs ys zs cellValue

theorem effectiveFiniteTripleRectangularSum_nonneg {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (cellValue : α -> β -> γ -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> 0 <= cellValue x y z) :
    0 <= finiteTripleRectangularSum xs ys zs cellValue := by
  exact finiteTripleRectangularSum_nonneg xs ys zs cellValue h

theorem effectiveFiniteTripleRectangularSum_mono {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (lower upper : α -> β -> γ -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> lower x y z <= upper x y z) :
    finiteTripleRectangularSum xs ys zs lower <=
      finiteTripleRectangularSum xs ys zs upper := by
  exact finiteTripleRectangularSum_mono xs ys zs lower upper h

theorem effectiveFiniteWeightedTripleRectangularSum_nonneg
    (xs ys zs : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hwidthZ : forall cell, cell ∈ zs -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> 0 <= cellValue x.1 y.1 z.1) :
    0 <= finiteWeightedTripleRectangularSum xs ys zs cellValue := by
  exact finiteWeightedTripleRectangularSum_nonneg xs ys zs cellValue
    hwidthX hwidthY hwidthZ hvalue

theorem effectiveFiniteWeightedTripleRectangularSum_mono
    (xs ys zs : List (Rat × Rat))
    (lower upper : Rat -> Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hwidthZ : forall cell, cell ∈ zs -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> lower x.1 y.1 z.1 <= upper x.1 y.1 z.1) :
    finiteWeightedTripleRectangularSum xs ys zs lower <=
      finiteWeightedTripleRectangularSum xs ys zs upper := by
  exact finiteWeightedTripleRectangularSum_mono xs ys zs lower upper
    hwidthX hwidthY hwidthZ hvalue

theorem effectiveFiniteWeightedTripleRectangularSum_add
    (xs ys zs : List (Rat × Rat))
    (f g : Rat -> Rat -> Rat -> Rat) :
    finiteWeightedTripleRectangularSum xs ys zs
        (fun x y z => f x y z + g x y z) =
      finiteWeightedTripleRectangularSum xs ys zs f +
        finiteWeightedTripleRectangularSum xs ys zs g := by
  exact finiteWeightedTripleRectangularSum_add xs ys zs f g

theorem effectiveFiniteWeightedTripleRectangularSum_scale
    (xs ys zs : List (Rat × Rat)) (scale : Rat)
    (f : Rat -> Rat -> Rat -> Rat) :
    finiteWeightedTripleRectangularSum xs ys zs
        (fun x y z => scale * f x y z) =
      scale * finiteWeightedTripleRectangularSum xs ys zs f := by
  exact finiteWeightedTripleRectangularSum_scale xs ys zs scale f

theorem effectiveFiniteWeightedTripleRectangularSum_congr
    (xs ys zs : List (Rat × Rat))
    (f g : Rat -> Rat -> Rat -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> f x.1 y.1 z.1 = g x.1 y.1 z.1) :
    finiteWeightedTripleRectangularSum xs ys zs f =
      finiteWeightedTripleRectangularSum xs ys zs g := by
  exact finiteWeightedTripleRectangularSum_congr xs ys zs f g h

theorem effectiveFiniteTripleRectangularSum_add {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (f g : α -> β -> γ -> Rat) :
    finiteTripleRectangularSum xs ys zs (fun x y z => f x y z + g x y z) =
      finiteTripleRectangularSum xs ys zs f +
        finiteTripleRectangularSum xs ys zs g := by
  exact finiteTripleRectangularSum_add xs ys zs f g

theorem effectiveFiniteTripleRectangularSum_scale {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ) (scale : Rat)
    (f : α -> β -> γ -> Rat) :
    finiteTripleRectangularSum xs ys zs (fun x y z => scale * f x y z) =
      scale * finiteTripleRectangularSum xs ys zs f := by
  exact finiteTripleRectangularSum_scale xs ys zs scale f

theorem effectiveFiniteTripleRectangularSum_congr {α β γ : Type}
    (xs : List α) (ys : List β) (zs : List γ)
    (f g : α -> β -> γ -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      forall z, z ∈ zs -> f x y z = g x y z) :
    finiteTripleRectangularSum xs ys zs f =
      finiteTripleRectangularSum xs ys zs g := by
  exact finiteTripleRectangularSum_congr xs ys zs f g h

theorem effectiveFiniteProductIntegralSum2D_nonneg
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat)
    (hx : forall cell, cell ∈ xs -> 0 <= cell.2 * f cell.1)
    (hy : forall cell, cell ∈ ys -> 0 <= cell.2 * g cell.1) :
    0 <= finiteProductIntegralSum2D xs ys f g := by
  exact finiteProductIntegralSum2D_nonneg xs ys f g hx hy

/-! Finite Fubini symmetry for a separable weighted rectangle sum. -/
theorem effectiveFiniteProductIntegralSum2D_swap
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat) :
    finiteProductIntegralSum2D xs ys f g =
      finiteProductIntegralSum2D ys xs g f := by
  rw [finiteProductIntegralSum2D_factorized,
    finiteProductIntegralSum2D_factorized]
  exact Rat.mul_comm _ _

theorem effectiveFiniteProductIntegralNestedSum_nonneg
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat))
    (hwidth : forall cells, cells ∈ samples ->
      forall cell, cell ∈ cells -> 0 <= cell.2)
    (hfactor : forall factor, factor ∈ factors ->
      forall x, 0 <= factor x) :
    0 <= finiteProductIntegralNestedSum samples factors := by
  exact finiteProductIntegralNestedSum_nonneg samples factors hwidth hfactor

/-! Public entry-point wrapper for the coefficient-level complex FTC bridge.
Downstream proofs can recover a coefficient stream after formal integration
without importing the series implementation module directly. -/
theorem effectiveComplexCoefficientDerivative_primitiveCoefficients
    (coefficients : Nat -> QComplex) :
    complexCoefficientDerivative (complexPrimitiveCoefficients coefficients) =
      coefficients := by
  exact complexCoefficientDerivative_primitiveCoefficients coefficients

/-! Public generic finite-polynomial FTC bridge.  A finite Taylor primitive is
defined over rational inputs, its derivative is a finite coefficient prefix,
and the endpoint difference is the corresponding finite monomial sum.  The
secant certificate below is the reusable proof object for turning that exact
algebra into the interval derivative contract consumed by effective FTC. -/
theorem effectiveFiniteTaylorFTC_endpointDifference_eq_finiteMonomialIntegralSum
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    FinitePolynomial.integratedTaylorPrefix coeffs terms b -
        FinitePolynomial.integratedTaylorPrefix coeffs terms a =
      FinitePolynomial.finiteMonomialIntegralSum coeffs terms a b := by
  exact FinitePolynomial.integratedTaylorPrefix_endpointDifference_eq_finiteMonomialIntegralSum
    coeffs terms a b

def effectiveFiniteTaylorDerivativeOnInterval
    (coeffs : Nat -> Rat) (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (FinitePolynomial.integratedTaylorPrefix coeffs terms) a b)
      (FunctionOnInterval.exactRat
        (FinitePolynomial.taylorDerivativePrefix coeffs terms) a b) :=
  FinitePolynomial.integratedTaylorPrefix_hasDerivativeOnInterval
    coeffs terms a b C hleft hright hC1

/-! A finite trigonometric-prefix example belongs to the public calculus
surface even though the full equal-dyadic sine transport is a separate
geometric frontier.  Keeping this distinction visible prevents a polynomial
prefix theorem from being mistaken for the completed sine theorem. -/

/-- The first nonzero sine Taylor prefix, squared on `[0,1/2]`, satisfies the
effective FTC and has the explicitly computed endpoint value. -/
theorem effectiveFTC_sine_prefix_square :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280)) := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value

/-! Fourier stages use the same representation discipline: a precision
witness is an actual finite rational-complex transform inside the stabilized
box. -/
theorem effectiveFourierSeries_precision_witness
    (F : EffectiveFourierSeries) (eps : QPos) :
    ∃ N : Nat, ∃ q : QComplex,
      (QBox.point q).NestedIn (F.stabilized.compute N) /\
      (F.stabilized.compute N).width <= eps.val /\
      (F.stabilized.compute N).height <= eps.val := by
  exact F.precision_witness eps

/-! The first matrix ODE base case is likewise exposed at the scoped entry
point.  It is an exact rational linear-algebra theorem, before any passage to
a continuous matrix-valued function. -/
theorem effectiveTwoByTwoSolutionUnique {a b c d : Rat}
    (hdet : LinearODE.HarmonicOscillator.twoByTwoDeterminant a b c d ≠ 0)
    (rhs u v : LinearODE.RatVector 2)
    (hu : LinearODE.matrixApply
      (LinearODE.HarmonicOscillator.twoByTwoMatrix a b c d) u = rhs)
    (hv : LinearODE.matrixApply
      (LinearODE.HarmonicOscillator.twoByTwoMatrix a b c d) v = rhs) :
    u = v := by
  exact LinearODE.HarmonicOscillator.twoByTwo_solution_unique hdet rhs u v hu hv

end ComputableAnalysis

namespace ComputableAnalysis

/-! The finite secant product rule is the algebraic product-rule interface for
the effective calculus.  It is stated over rational endpoint values and a
positive cell, before any derivative or limit representation is introduced. -/
theorem effectiveSecantProductRule
    {x y f0 f1 g0 g1 : Rat} (hxy : x < y) :
    (f1 * g1 - f0 * g0) / (y - x) =
      f0 * ((g1 - g0) / (y - x)) +
        g1 * ((f1 - f0) / (y - x)) := by
  exact secantSlope_product_transport hxy

end ComputableAnalysis

namespace ComputableAnalysis.ExactFunction

/-! Public finite chain-rule factorization and error estimate.  The nonzero
inner increment is explicit, so this is a rational forward-step theorem rather
than an assertion about an attained derivative at a limit point. -/
theorem effectiveDifferenceQuotientCompositionFactorization
    (f g : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0)
    (hgh : g (x + h) - g x ≠ 0) :
    differenceQuotient (fun z => f (g z)) x h =
      differenceQuotient f (g x) (g (x + h) - g x) *
        differenceQuotient g x h := by
  exact differenceQuotient_comp_factorization f g hh hgh

theorem effectiveDifferenceQuotientCompositionErrorLe
    (f df g dg : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0)
    (hgh : g (x + h) - g x ≠ 0) :
    qabs (differenceQuotient (fun z => f (g z)) x h -
      df (g x) * dg x) <=
      qabs (differenceQuotient f (g x) (g (x + h) - g x)) *
          qabs (differenceQuotient g x h - dg x) +
        qabs (dg x) *
          qabs (differenceQuotient f (g x) (g (x + h) - g x) -
            df (g x)) := by
  exact differenceQuotient_comp_error_le f df g dg hh hgh

end ComputableAnalysis.ExactFunction

namespace ComputableAnalysis

/-! Public finite integration-by-parts and square-chain identities.  The
quadratic-variation term is retained explicitly, so the finite statement does
not rely on silently discarding a mesh error. -/
theorem effectiveFiniteIntegrationByParts
    (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f g n + rightStieltjesSum f g n =
      f n * g n - f 0 * g 0 := by
  exact finiteIntegrationByParts f g n

theorem effectiveFiniteSquareChain
    (f : Nat -> Rat) (n : Nat) :
    2 * leftStieltjesSum f f n + quadraticVariationSum f f n =
      f n * f n - f 0 * f 0 := by
  exact finiteSquareStieltjes_chain f n

theorem effectiveFiniteSquareChain_left_bounds
    (f : Nat -> Rat) (n : Nat) (eps : Rat)
    (hvariation : 0 <= quadraticVariationSum f f n)
    (hvariation_le : quadraticVariationSum f f n <= eps) :
    f n * f n - f 0 * f 0 - eps <=
        2 * leftStieltjesSum f f n /\
      2 * leftStieltjesSum f f n <=
        f n * f n - f 0 * f 0 := by
  exact finiteSquareStieltjes_left_bounds f n eps hvariation hvariation_le

end ComputableAnalysis
