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
