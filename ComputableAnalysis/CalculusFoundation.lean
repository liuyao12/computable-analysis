import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteFTCQuintic
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.SinPiSquareCheckpoints
import ComputableAnalysis.EffectiveCalculusFoundation
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.SeriesFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteTaylorCertificate
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
import ComputableAnalysis.RationalCircle
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

/-! Finite geometric control used by the integral and circle chapters.  The
    polygonal-path inequality is derived by induction from a rational
    triangle inequality; it is not imported as a completeness or Euclidean
    existence principle. -/
theorem effectivePolygonalPath_length_ge_endpoint
    (segmentLength : PiCirclePoint -> PiCirclePoint -> Rat)
    (hzero : forall p, segmentLength p p = 0)
    (htriangle : forall p q r,
      segmentLength p r <= segmentLength p q + segmentLength q r)
    (p : PiCirclePoint) (rest : List PiCirclePoint) :
    segmentLength p (RationalCircle.Stage.polygonalPathEndpoint p rest) <=
      RationalCircle.Stage.polygonalPathLengthFrom segmentLength p rest := by
  exact RationalCircle.Stage.polygonalPath_length_ge_endpoint
    segmentLength hzero htriangle p rest

theorem effectiveRationalPolyline_length_ge_direct (steps : List Rat) :
    RationalCircle.Stage.rationalDirectLength steps <=
      RationalCircle.Stage.rationalPolylineLength steps := by
  exact RationalCircle.Stage.rationalPolyline_length_ge_direct steps

theorem effectiveRationalPolyline_length_strict_of_genuine_turn
    {u v : Rat} (huv : u * v < 0) :
    RationalCircle.Stage.rationalDirectLength [u, v] <
      RationalCircle.Stage.rationalPolylineLength [u, v] := by
  exact RationalCircle.Stage.rationalPolyline_length_two_step_strict_of_genuine_turn huv

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

/-! Public curvature-facing FTC entry points.  These are the project's
    certificate form of the classical MVT/FTC route: convexity or concavity
    supplies finite derivative brackets, while endpoint transport remains an
    explicit rational obligation. -/
theorem effectiveConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact Integral.effectiveConvexFTC h

theorem effectiveConcaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact Integral.effectiveConcaveFTC h

theorem effectiveCurvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact Integral.effectiveCurvatureFTC h

theorem effectiveMeanValueBracket
    {F dF : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C)
    (hF : F.Valid) (hwidth : 0 < C.width) (n : Nat) :
    QInterval.Overlaps
      (H.bound n)
      (QInterval.divByRat
        (endpointDifferenceInterval F C.lower C.upper
          (H.endpointPrecision n))
        C.width) := by
  exact Integral.effectiveMeanValueBracket H hF hwidth n

/-! Concrete regression client: the rational square certificate closes the
    curvature-to-FTC pipeline at the normalized value one. -/
theorem effectiveSquareCurvatureFTC :
    Integral.squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      Integral.squareCurvatureFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact Integral.effectiveSquareCurvatureFTC

theorem effectiveSquareCurvatureFTC_value_one :
    Integral.squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1) := by
  exact Integral.effectiveSquareCurvatureFTC_value_one

/-! Rational bridge for the first non-polynomial product example.  The
    combined derivative evaluator is definitionally the tangent-square
    density, and the primitive's endpoint difference is the quarter-turn
    anchor; only the separate sine-representation overlap remains. -/
theorem effectiveTangentSquareCombinedDerivative_compute_eq_density
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    SinPiIntegral.tangentSquareCombinedDerivativeRaw.compute x n =
      SinPiIntegral.tangentSquareDensityRaw.compute x n := by
  exact SinPiIntegral.tangentSquareCombinedDerivativeRaw_compute_eq_density
    hx0 hx1 n

theorem effectiveTangentSquarePrimitive_endpointDifference_equiv_halfQuarterTurn :
    (endpointDifferenceRaw
      SinPiIntegral.tangentSquareEffectivePrimitiveOnUnit 0 1
      SinPiIntegral.tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact SinPiIntegral.tangentSquareEffectivePrimitive_endpointDifference_equiv_halfQuarterTurn

theorem effectiveTangentSquareFTC_integral_equiv_halfQuarterTurn :
    SinPiIntegral.tangentSquareEffectiveFTCData.integralRaw.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact SinPiIntegral.tangentSquareEffectiveFTC_integral_equiv_halfQuarterTurn

theorem effectiveDyadicPublicSquareIntegral_equiv_halfQuarterTurn
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (h : SinPiIntegral.DyadicPublicSquareTangentTransportWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hbridge : SinPiIntegral.tangentSquareIntegral.Equiv
      SinPiIntegral.tangentSquareEffectiveFTCData.integralRaw) :
    (SinPiIntegral.dyadicPublicSquareIntegralRaw_stabilized S
      SinPiIntegral.tangentSquareIntegral).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact h.to_public_equiv_halfQuarterTurn hsine hbridge

theorem effectiveDyadicPublicSquareIntegral_equiv_halfQuarterTurn_shared
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (h : SinPiIntegral.DyadicPublicSquareTangentSharedWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hbridge : SinPiIntegral.tangentSquareIntegral.Equiv
      SinPiIntegral.tangentSquareEffectiveFTCData.integralRaw) :
    (SinPiIntegral.dyadicPublicSquareIntegralRaw_stabilized S
      SinPiIntegral.tangentSquareIntegral).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact h.to_public_equiv_halfQuarterTurn hsine hbridge

theorem effectiveReciprocalPi_quarterTurn_equiv_quarter :
    (SinPiIntegral.reciprocalPiRaw *
      RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact reciprocalPi_quarterTurn_equiv_quarter

theorem effectiveCanonicalDyadicCertificate_square_complement_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    (h : SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt
      B precision depth k hk) :
    QInterval.Overlaps
      (SinPiIntegral.rationalSquareInterval
        (SinPiIntegral.dyadicNestedRadicalTableAt precision depth k).1)
      (SinPiIntegral.rationalOneMinusSquareInterval h.cosineBox) := by
  exact SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt.to_square_complement_overlap h

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

theorem effectiveLinearODEChronologicalProduct_split
    (B : Nat -> LinearODE.RatMatrix dimension)
    (first second : Nat) :
    LinearODE.chronologicalProduct B (first + second) =
      LinearODE.matrixMul
        (LinearODE.chronologicalProduct
          (fun k => B (first + k)) second)
        (LinearODE.chronologicalProduct B first) := by
  exact LinearODE.chronologicalProduct_split B first second

theorem effectiveLinearODESquareZeroUniformStep
    {dimension : Nat} (A : LinearODE.RatMatrix dimension)
    (T : Rat) (steps : Nat) (hsteps : 0 < steps)
    (hAA : LinearODE.matrixMul A A = LinearODE.matrixZero dimension) :
    LinearODE.chronologicalProduct
        (fun _ => LinearODE.matrixScale
          (T / ((steps : Nat) : Rat)) A) steps =
      LinearODE.matrixAdd (LinearODE.matrixIdentity dimension)
        (LinearODE.matrixScale T A) := by
  exact LinearODE.chronologicalProduct_constant_square_zero_uniform_step
    A T steps hsteps hAA

theorem effectiveLinearODESimplexVolume_eq_closed
    (T : Rat) (degree : Nat) :
    LinearODE.orderedSimplexVolume T degree =
      T ^ degree / factorialRat degree := by
  exact LinearODE.orderedSimplexVolume_eq_closed T degree

theorem effectiveLinearODEPeanoBakerTerm_succ
    {dimension : Nat} (A : LinearODE.RatMatrix dimension)
    (T : Rat) (degree : Nat) :
    LinearODE.constantPeanoBakerSimplexTerm A T (degree + 1) =
      LinearODE.matrixScale (T / ((degree + 1 : Nat) : Rat))
        (LinearODE.matrixMul A
          (LinearODE.constantPeanoBakerSimplexTerm A T degree)) := by
  exact LinearODE.constantPeanoBakerSimplexTerm_succ A T degree

theorem effectiveLinearODEPeanoBakerPartial_succ
    {dimension : Nat} (A : LinearODE.RatMatrix dimension)
    (T : Rat) (terms : Nat) :
    LinearODE.constantPeanoBakerSimplexPartial A T (terms + 1) =
      LinearODE.matrixAdd
        (LinearODE.constantPeanoBakerSimplexPartial A T terms)
        (LinearODE.constantPeanoBakerSimplexTerm A T terms) := by
  exact LinearODE.constantPeanoBakerSimplexPartial_succ A T terms

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

/-! The parity adapter makes the geometric workload explicit: even samples
    are inherited from their parent, while the caller supplies only the two
    odd branches. -/
noncomputable def effectiveDyadicTangentWitnessFamily_of_lower_upper_odd_certificates
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (lower : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt B precision (n + 1)
        (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
    (upper : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt B precision (n + 1) k hk) :
    SinPiIntegral.DyadicTangentWitnessFamily B := by
  exact SinPiIntegral.DyadicTangentWitnessFamily.of_lower_upper_odd_canonical_halfAngle_certificate_families
    B ht0 lower upper

theorem effectiveSinPiHalfIntegral_equiv_of_canonical_halfAngle_certificate_family
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
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      0 < k -> SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt
        S.inverse precision depth k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.integral g 0 ((1 : Rat) / 2) cg) := by
  exact S.halfIntegral_equiv_of_canonical_halfAngle_certificate_family
    pub g cg hdyadic hplan hevaluator ht0 hcertificate

theorem effectiveSineWitnessSearch_exists_of_overlap_of_positive_width
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1)
    (hover : QInterval.Overlaps
      (SinPiIntegral.rationalCircleSinInterval U) S)
    (hwidth : 0 < S.width) :
    ∃ m u, SinPiIntegral.rationalTangentWitnessBoxSearch U S m = some u := by
  exact SinPiIntegral.exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    hU hS hover hwidth

/-! Public constructors for the proof-producing canonical dyadic witness
    search.  These expose the finite rational certificate boundary without
    exposing the implementation of the candidate-list traversal. -/
def effectiveCanonicalDyadicCertificate_at_of_rational_witness
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    (u : Rat) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsine : (SinPiIntegral.dyadicNestedRadicalTableAt precision depth k).1.lo <=
        SinPiIntegral.rationalCircleSin u /\
      SinPiIntegral.rationalCircleSin u <=
        (SinPiIntegral.dyadicNestedRadicalTableAt precision depth k).1.hi)
    (houter : (SinPiIntegral.dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (SinPiIntegral.rationalHalfAngleTangentInterval
        ((SinPiIntegral.dyadicNestedRadicalTableAt precision depth k).1)
        { lo := SinPiIntegral.rationalCircleCos u,
          hi := SinPiIntegral.rationalCircleCos u })) :
    SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt B precision depth k hk := by
  exact SinPiIntegral.canonical_dyadic_certificate_at_of_rational_witness
    B hk u hu0 hu1 hsine houter

noncomputable def effectiveCanonicalDyadicCertificateSearchAt_sound
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    {candidates : List Rat} {u : Rat}
    (hsearch : SinPiIntegral.canonicalDyadicCertificateSearchAt
      B precision depth k hk candidates = some u) :
    SinPiIntegral.CanonicalDyadicHalfAngleCertificateAt B precision depth k hk := by
  exact SinPiIntegral.canonicalDyadicCertificateSearchAt_sound B hsearch

theorem effectiveCanonicalDyadicCertificateSearchAt_some_of_mem_of_admissible
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    {candidates : List Rat} {u : Rat}
    (hmem : u ∈ candidates)
    (hadm : SinPiIntegral.canonicalDyadicCertificateAdmissibleBool
      B precision depth k hk u = true) :
    ∃ v, SinPiIntegral.canonicalDyadicCertificateSearchAt
      B precision depth k hk candidates = some v := by
  exact SinPiIntegral.canonicalDyadicCertificateSearchAt_some_of_mem_of_admissible
    B hmem hadm

theorem effectiveDyadicNestedRadicalIntegralRaw_widths_shrink :
    RealRaw.WidthsShrinkToZero
      SinPiIntegral.dyadicNestedRadicalIntegralRaw.compute := by
  exact SinPiIntegral.dyadicNestedRadicalIntegralRaw_widths_shrink

theorem effectiveDyadicNestedRadicalLeftSum_width_nonneg (n : Nat) :
    0 <= (SinPiIntegral.dyadicNestedRadicalLeftSum n).width := by
  exact SinPiIntegral.dyadicNestedRadicalLeftSum_width_nonneg n

theorem effectiveDyadicNestedRadical_sample_coordinate
    {n k : Nat} (hk : k < 2 ^ n) :
    2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k =
      (k : Rat) / ((2 ^ n : Nat) : Rat) := by
  exact SinPiIntegral.dyadicNestedRadical_sample_coordinate hk

theorem effectiveDyadicNestedRadicalIntegralRaw_stabilized_valid_of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (SinPiIntegral.dyadicNestedRadicalLeftSum n)
        (SinPiIntegral.sinPiStieltjesIntegral.compute n)) :
    SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized.Valid := by
  exact SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized_valid_of_overlap
    hoverlap

theorem effectiveDyadicNestedRadicalIntegralRaw_stabilized_width_le
    (n : Nat) :
    (SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized.compute n).width <=
      (SinPiIntegral.dyadicNestedRadicalIntegralRaw.compute n).width +
        2 * (SinPiIntegral.sinPiStieltjesIntegral.compute n).width := by
  exact SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized_width_le n

theorem effectiveDyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (SinPiIntegral.dyadicNestedRadicalLeftSum n)
        (SinPiIntegral.sinPiStieltjesIntegral.compute n)) :
    SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized.Equiv
      SinPiIntegral.reciprocalPiRaw := by
  exact SinPiIntegral.dyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_overlap
    hoverlap

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

theorem effectiveFiniteWeightedTripleRectangularSum_swap12_raw
    (xs ys zs : List (Rat × Rat))
    (cellValue : Rat -> Rat -> Rat -> Rat) :
    finiteWeightedTripleRectangularSum xs ys zs cellValue =
      finiteTripleRectangularSum ys xs zs
        (fun y x z => y.2 * x.2 * z.2 * cellValue x.1 y.1 z.1) := by
  exact finiteWeightedTripleRectangularSum_swap12_raw xs ys zs cellValue

theorem effectiveFiniteWeightedTripleRectangularSum_swap23_raw
    (xs ys zs : List (Rat × Rat))
    (cellValue : Rat -> Rat -> Rat -> Rat) :
    finiteWeightedTripleRectangularSum xs ys zs cellValue =
      finiteTripleRectangularSum xs zs ys
        (fun x z y => x.2 * y.2 * z.2 * cellValue x.1 y.1 z.1) := by
  exact finiteWeightedTripleRectangularSum_swap23_raw xs ys zs cellValue

theorem effectiveFiniteWeightedTripleRectangularSum_unitCube_stage :
    finiteWeightedTripleRectangularSum
      [(0, 1 / 2), (1 / 2, 1 / 2)]
      [(0, 1 / 2), (1 / 2, 1 / 2)]
      [(0, 1 / 2), (1 / 2, 1 / 2)]
      (fun _ _ _ => 1) = 1 := by
  exact finiteWeightedTripleRectangularSum_unitCube_stage

theorem effectiveFiniteWeightedTripleRectangularSum_singleCell
    (x y z dx dy dz value : Rat) :
    finiteWeightedTripleRectangularSum
      [(x, dx)] [(y, dy)] [(z, dz)] (fun _ _ _ => value) =
      dx * dy * dz * value := by
  exact finiteWeightedTripleRectangularSum_singleCell
    x y z dx dy dz value

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

/-! Public power-series tail entry points.  These are rational majorant
theorems: an infinite series is approached through finite prefixes plus an
explicit tail budget, rather than introduced as a completed-real object. -/

theorem effectiveGeometricTailPartial_bound {C r : Rat} {N k : Nat}
    (hC : 0 <= C) (hr0 : 0 <= r) (hrHalf : r <= (1 : Rat) / 2) :
    RationalMajorant.geomTailPartial C r N k <=
      RationalMajorant.geomTailBound C r N := by
  exact RationalMajorant.geometric_tail_partial_bound hC hr0 hrHalf

theorem effectiveFactorialTailPartial_shifted_le_eps {C : Rat}
    (hC : 0 <= C) (eps : QPos) (terms : Nat) :
    RationalMajorant.factorialTailPartial C
      (RationalMajorant.factorialTailStart C +
        RationalMajorant.halfDecayShift
          (2 * RationalMajorant.factorialTailTerm C
            (RationalMajorant.factorialTailStart C)) eps)
      terms <= eps.val := by
  exact RationalMajorant.factorialTailPartial_shifted_le_eps hC eps terms

theorem effectiveSineTaylorIntegralPartial_eq_one_sub_cosineTaylorPartial_succ
    (x : Rat) (n : Nat) :
    FormalPowerSeries.sineTaylorIntegralPartial x n =
      1 - FormalPowerSeries.cosineTaylorPartial x (n + 1) := by
  exact FormalPowerSeries.sineTaylorIntegralPartial_eq_one_sub_cosineTaylorPartial_succ
    x n

theorem effectiveCosineTaylorIntegralPartial_eq_sineTaylorPartial
    (x : Rat) (n : Nat) :
    FormalPowerSeries.cosineTaylorIntegralPartial x n =
      FormalPowerSeries.sineTaylorPartial x n := by
  exact FormalPowerSeries.cosineTaylorIntegralPartial_eq_sineTaylorPartial x n

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

theorem effectiveFinitePolynomialIntegralSum_add
    (coeffs₁ coeffs₂ : Nat -> Rat) (terms : Nat) (a b : Rat) :
    FinitePolynomial.finiteMonomialIntegralSum
        (fun k => coeffs₁ k + coeffs₂ k) terms a b =
      FinitePolynomial.finiteMonomialIntegralSum coeffs₁ terms a b +
        FinitePolynomial.finiteMonomialIntegralSum coeffs₂ terms a b := by
  exact FinitePolynomial.finiteMonomialIntegralSum_add
    coeffs₁ coeffs₂ terms a b

theorem effectiveFinitePolynomialIntegralSum_scale
    (c : Rat) (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    FinitePolynomial.finiteMonomialIntegralSum
        (fun k => c * coeffs k) terms a b =
      c * FinitePolynomial.finiteMonomialIntegralSum coeffs terms a b := by
  exact FinitePolynomial.finiteMonomialIntegralSum_scale c coeffs terms a b

/-- Public entry point for a finite Taylor certificate.  Its fold identity is
    the exact finite FTC calculation consumed by later tail arguments. -/
theorem effectiveFiniteTaylorCertificate_fold_identity
    (certificate : FiniteTaylorCertificate) :
    certificate.prefixIncrement =
      (List.range certificate.terms).foldl
        (fun acc k => acc + certificate.coefficients k *
          (certificate.rightEndpoint ^ (k + 1) /
              ((k + 1 : Nat) : Rat) -
            certificate.leftEndpoint ^ (k + 1) /
              ((k + 1 : Nat) : Rat))) 0 := by
  exact certificate.fold_identity

/-- Public validity and value transport for the finite polynomial endpoint
    computation.  This is the consumer-facing entry point before a later
    proof assembles several polynomial or special-function certificates. -/
theorem effectiveFiniteTaylorCertificate_endpointRaw_valid
    (certificate : FiniteTaylorCertificate) :
    certificate.endpointRaw.Valid := by
  exact certificate.endpointRaw_valid

theorem effectiveFiniteTaylorCertificate_endpointRaw_equiv_prefixIncrement
    (certificate : FiniteTaylorCertificate) :
    certificate.endpointRaw.Equiv
      (RealRaw.ofRat certificate.prefixIncrement) := by
  exact certificate.endpointRaw_equiv_prefixIncrement

noncomputable def effectiveFiniteTaylorEndpointRaw
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) : RealRaw :=
  (finiteTaylorCertificate coeffs terms a b).endpointRaw

theorem effectiveFiniteTaylorEndpointRaw_valid
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a b).Valid := by
  exact (finiteTaylorCertificate coeffs terms a b).endpointRaw_valid

theorem effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a b).Equiv
      (RealRaw.ofRat
        (FinitePolynomial.integratedTaylorPrefix coeffs terms b -
          FinitePolynomial.integratedTaylorPrefix coeffs terms a)) := by
  exact (finiteTaylorCertificate coeffs terms a b).endpointRaw_equiv_prefixIncrement

theorem effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a b).Equiv
      (RealRaw.ofRat
        (FinitePolynomial.finiteMonomialIntegralSum coeffs terms a b)) := by
  have h := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms a b
  have hvalue := effectiveFiniteTaylorFTC_endpointDifference_eq_finiteMonomialIntegralSum
    coeffs terms a b
  rw [hvalue] at h
  exact h

theorem effectiveFiniteTaylorEndpointRaw_split
    (coeffs : Nat -> Rat) (terms : Nat) (a c b : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a b).Equiv
      (effectiveFiniteTaylorEndpointRaw coeffs terms a c +
        effectiveFiniteTaylorEndpointRaw coeffs terms c b) := by
  let P := FinitePolynomial.integratedTaylorPrefix coeffs terms
  let q := P c - P a
  let r := P b - P c
  have hab := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms a b
  have hac := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms a c
  have hcb := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms c b
  have habvalid := effectiveFiniteTaylorEndpointRaw_valid coeffs terms a b
  have hacvalid := effectiveFiniteTaylorEndpointRaw_valid coeffs terms a c
  have hcbvalid := effectiveFiniteTaylorEndpointRaw_valid coeffs terms c b
  have hqvalid : (RealRaw.ofRat q).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hrvalid : (RealRaw.ofRat r).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hsumvalid := RealRaw.add_valid hacvalid hcbvalid
  have htransport :
      (effectiveFiniteTaylorEndpointRaw coeffs terms a c +
        effectiveFiniteTaylorEndpointRaw coeffs terms c b).Equiv
        (RealRaw.ofRat q + RealRaw.ofRat r) := by
    exact RealRaw.add_equiv hacvalid hqvalid hcbvalid hrvalid hac hcb
  have hcollapse :
      (RealRaw.ofRat q + RealRaw.ofRat r).Equiv
        (RealRaw.ofRat (P b - P a)) := by
    have h := ComputableAnalysis.ofRat_add_equiv q r
    have hqr : q + r = P b - P a := by
      dsimp [q, r]
      grind [Rat.sub_def, Rat.add_assoc]
    rw [← hqr]
    exact h
  have htotalvalid : (RealRaw.ofRat (P b - P a)).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hqrvalid : (RealRaw.ofRat q + RealRaw.ofRat r).Valid :=
    RealRaw.add_valid hqvalid hrvalid
  have hright :
      (effectiveFiniteTaylorEndpointRaw coeffs terms a c +
        effectiveFiniteTaylorEndpointRaw coeffs terms c b).Equiv
        (RealRaw.ofRat (P b - P a)) :=
    RealRaw.equiv_trans hsumvalid hqrvalid htotalvalid htransport hcollapse
  exact RealRaw.equiv_trans habvalid htotalvalid hsumvalid hab
    (RealRaw.equiv_symm hright)

theorem effectiveFiniteTaylorEndpointRaw_self_equiv_zero
    (coeffs : Nat -> Rat) (terms : Nat) (a : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a a).Equiv
      RealRaw.zero := by
  have h := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms a a
  rw [Rat.sub_self] at h
  simpa [RealRaw.zero] using h

theorem effectiveFiniteTaylorEndpointRaw_reverse
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw coeffs terms a b).Equiv
      (-(effectiveFiniteTaylorEndpointRaw coeffs terms b a)) := by
  let P := FinitePolynomial.integratedTaylorPrefix coeffs terms
  have hab := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms a b
  have hba := effectiveFiniteTaylorEndpointRaw_equiv_endpointDifference
    coeffs terms b a
  have habvalid := effectiveFiniteTaylorEndpointRaw_valid coeffs terms a b
  have hbavalid := effectiveFiniteTaylorEndpointRaw_valid coeffs terms b a
  have hqvalid : (RealRaw.ofRat (P a - P b)).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hnegvalid : (-(RealRaw.ofRat (P a - P b))).Valid :=
    RealRaw.neg_valid hqvalid
  have htotalvalid : (RealRaw.ofRat (P b - P a)).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hnegRat :
      (-(RealRaw.ofRat (P a - P b))).Equiv
        (RealRaw.ofRat (P b - P a)) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    change QInterval.Overlaps
      { lo := -(P a - P b), hi := -(P a - P b) }
      { lo := P b - P a, hi := P b - P a }
    unfold QInterval.Overlaps
    constructor <;> grind [Rat.sub_def]
  have hright :
      (-(effectiveFiniteTaylorEndpointRaw coeffs terms b a)).Equiv
        (RealRaw.ofRat (P b - P a)) := by
    exact RealRaw.equiv_trans (RealRaw.neg_valid hbavalid)
      hnegvalid htotalvalid (RealRaw.neg_equiv hba) hnegRat
  exact RealRaw.equiv_trans habvalid htotalvalid
    (RealRaw.neg_valid hbavalid) hab (RealRaw.equiv_symm hright)

/-! Generic prefix-plus-tail bookkeeping.  A tail certificate is kept as a
separate raw computation; the only assembly fact needed here is finite
interval arithmetic on the two widths. -/

theorem effectivePrefixTail_width_eq_add
    (head tail : RealRaw) (stage : Nat) :
    ((head + tail).compute stage).width =
      (head.compute stage).width + (tail.compute stage).width := by
  exact RealRaw.add_width head tail stage

theorem effectivePrefixTail_width_le_of_bounds
    (head tail : RealRaw) (stage : Nat)
    (prefixBound tailBound : Rat)
    (hprefix : (head.compute stage).width <= prefixBound)
    (htail : (tail.compute stage).width <= tailBound) :
    ((head + tail).compute stage).width <= prefixBound + tailBound := by
  rw [effectivePrefixTail_width_eq_add]
  exact _root_.ComputableAnalysis.rat_add_le_add hprefix htail

theorem effectivePrefixTail_equiv_of_components
    {head head' tail tail' : RealRaw}
    (hhead : head.Valid) (hhead' : head'.Valid)
    (htail : tail.Valid) (htail' : tail'.Valid)
    (hheadEq : head.Equiv head') (htailEq : tail.Equiv tail') :
    (head + tail).Equiv (head' + tail') := by
  exact RealRaw.add_equiv hhead hhead' htail htail' hheadEq htailEq

/-- Focused-entry-point access to the closed monomial FTC family.  The
    implementation remains in `Integral`; this wrapper is the stable import
    surface for downstream formalizations. -/
def effectiveExactRatPowDefiniteIdentity (k : Nat) :
    Integral.DefiniteIdentityFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
      (Integral.powPrimitiveOnUnit k) :=
  Integral.exactRat_pow_definiteIdentity k

theorem effectiveExactRatPowIntegral_equiv_ofRat (k : Nat) :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
      (Integral.exactRat_pow_integral_certificate k)).Equiv
      (RealRaw.ofRat (1 / ((k + 1 : Nat) : Rat))) :=
  Integral.exactRat_pow_integral_raw_equiv_one_div_succ k

/-- Named focused-entry-point aliases for the first higher-degree interval
    bounded FTC regressions.  Their separate modules retain the detailed
    budgets; these names make the closed polynomial ladder discoverable from
    the foundation import. -/
def effectiveExactRatQuarticDefiniteIdentity :
    Integral.DefiniteIdentityFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      Integral.quarticPrimitiveOnUnit :=
  Integral.exactRat_quartic_definiteIdentity

def effectiveExactRatQuinticDefiniteIdentity :
    Integral.DefiniteIdentityFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 5) 0 1)
      Integral.quinticPrimitiveOnUnit :=
  Integral.exactRat_quintic_definiteIdentity

/-! Assemble a finite polynomial integral from the certified monomial raws.
    The separate anchor raw keeps the computation graph explicit; reducing
    that finite sum to one rational is an independent finite arithmetic step. -/

def effectiveFinitePolynomialIntegralRaw
    (coeffs : Nat -> Rat) (terms : Nat) : RealRaw :=
  Integral.finiteRawSum ((List.range terms).map (fun k =>
    RealRaw.scaleRat (coeffs k)
      (Integral.raw
        (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
        (Integral.exactRat_pow_integral_certificate k))))

def effectiveFinitePolynomialIntegralAnchorRaw
    (coeffs : Nat -> Rat) (terms : Nat) : RealRaw :=
  Integral.finiteRawSum ((List.range terms).map (fun k =>
    RealRaw.scaleRat (coeffs k)
      (RealRaw.ofRat (1 / ((k + 1 : Nat) : Rat)))))

def effectiveFinitePolynomialIntegralValue
    (coeffs : Nat -> Rat) (terms : Nat) : Rat :=
  finiteRatSum ((List.range terms).map (fun k =>
    coeffs k * (1 / ((k + 1 : Nat) : Rat))))

private theorem finitePolynomialRatSum_append (xs ys : List Rat) :
    finiteRatSum (xs ++ ys) = finiteRatSum xs + finiteRatSum ys := by
  induction xs with
  | nil =>
      simp [finiteRatSum]
      grind [Rat.zero_add]
  | cons x xs ih =>
      simp only [List.cons_append, finiteRatSum]
      rw [ih]
      grind [Rat.add_assoc]

theorem effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum
    (coeffs : Nat -> Rat) (terms : Nat) :
    effectiveFinitePolynomialIntegralValue coeffs terms =
      FinitePolynomial.finiteMonomialIntegralSum coeffs terms 0 1 := by
  induction terms with
  | zero => rfl
  | succ n ih =>
      simp only [effectiveFinitePolynomialIntegralValue, List.range_succ,
        List.map_append, FinitePolynomial.finiteMonomialIntegralSum]
      rw [finitePolynomialRatSum_append]
      simp only [List.map_singleton, finiteRatSum]
      rw [Rat.add_zero]
      change effectiveFinitePolynomialIntegralValue coeffs n +
        coeffs n * (1 / ((n + 1 : Nat) : Rat)) =
        FinitePolynomial.finiteMonomialIntegralSum coeffs n 0 1 +
          coeffs n * (1 ^ (n + 1) / ((n + 1 : Nat) : Rat) -
            0 ^ (n + 1) / ((n + 1 : Nat) : Rat))
      rw [ih]
      have hzero : (0 : Rat) ^ (n + 1) = 0 := by
        exact Series.rat_zero_pow_of_pos (by omega)
      simp [Series.rat_one_pow, hzero]
      have hzeroDiv : (0 : Rat) / ((n : Rat) + 1) = 0 := by
        rw [Rat.div_def, Rat.zero_mul]
      rw [hzeroDiv]
      grind [Rat.sub_def]

theorem effectiveFinitePolynomialIntegralValue_add
    (coeffs₁ coeffs₂ : Nat -> Rat) (terms : Nat) :
    effectiveFinitePolynomialIntegralValue
        (fun k => coeffs₁ k + coeffs₂ k) terms =
      effectiveFinitePolynomialIntegralValue coeffs₁ terms +
        effectiveFinitePolynomialIntegralValue coeffs₂ terms := by
  rw [effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum,
    effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum,
    effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum]
  exact effectiveFinitePolynomialIntegralSum_add coeffs₁ coeffs₂ terms 0 1

theorem effectiveFinitePolynomialIntegralValue_scale
    (c : Rat) (coeffs : Nat -> Rat) (terms : Nat) :
    effectiveFinitePolynomialIntegralValue (fun k => c * coeffs k) terms =
      c * effectiveFinitePolynomialIntegralValue coeffs terms := by
  rw [effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum,
    effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum]
  exact effectiveFinitePolynomialIntegralSum_scale c coeffs terms 0 1

private theorem scaleRat_ofRat_equiv (c q : Rat) :
    (RealRaw.scaleRat c (RealRaw.ofRat q)).Equiv
      (RealRaw.ofRat (c * q)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  by_cases hc : 0 <= c
  · simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, RealRaw.ofRat,
      RealRaw.ofRat_compute, hc, QInterval.Overlaps]
  · have hc' : c < 0 := by grind
    simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, RealRaw.ofRat,
      RealRaw.ofRat_compute, hc, hc', QInterval.Overlaps]

private theorem scaleRat_width_eq_qabs_mul (c : Rat) (x : RealRaw)
    (n : Nat) :
    ((RealRaw.scaleRat c x).compute n).width =
      qabs c * (x.compute n).width := by
  by_cases hc : 0 <= c
  · unfold RealRaw.scaleRat RealRaw.scaleRatCompute QInterval.width
    simp only [if_pos hc]
    simp only [qabs_eq_self_of_nonneg hc]
    grind
  · have hc' : c < 0 := by grind
    unfold RealRaw.scaleRat RealRaw.scaleRatCompute QInterval.width
    simp only [if_neg hc]
    unfold qabs
    rw [if_pos hc']
    grind

set_option maxHeartbeats 100000000 in
private theorem finiteRawSum_ofRat_equiv_sum (xs : List Rat) :
    (Integral.finiteRawSum (xs.map RealRaw.ofRat)).Equiv
      (RealRaw.ofRat (finiteRatSum xs)) := by
  induction xs with
  | nil =>
      have hzero : (RealRaw.ofRat (0 : Rat)).Valid := by
        unfold RealRaw.ofRat RealRaw.Valid
        exact RealRaw.ofRat_valid 0
      exact RealRaw.equiv_refl _ hzero
  | cons x xs ih =>
      have hxvalid : (RealRaw.ofRat x).Valid := by
        unfold RealRaw.ofRat RealRaw.Valid
        exact RealRaw.ofRat_valid x
      have htail : (Integral.finiteRawSum (xs.map RealRaw.ofRat)).Valid := by
        apply Integral.finiteRawSum_valid
        intro y hy
        simp only [List.mem_map] at hy
        rcases hy with ⟨z, hz, rfl⟩
        exact RealRaw.ofRat_valid _
      have htail' : (RealRaw.ofRat (finiteRatSum xs)).Valid := by
        unfold RealRaw.ofRat RealRaw.Valid
        exact RealRaw.ofRat_valid _
      have hvalue : (RealRaw.ofRat (x + finiteRatSum xs)).Valid := by
        unfold RealRaw.ofRat RealRaw.Valid
        exact RealRaw.ofRat_valid _
      have hsum :
          (RealRaw.ofRat x + Integral.finiteRawSum (xs.map RealRaw.ofRat)).Equiv
            (RealRaw.ofRat x + RealRaw.ofRat (finiteRatSum xs)) :=
        RealRaw.add_equiv hxvalid hxvalid htail htail'
          (RealRaw.equiv_refl _ hxvalid) ih
      exact RealRaw.equiv_trans
        (RealRaw.add_valid hxvalid htail)
        (RealRaw.add_valid hxvalid htail')
        hvalue
        hsum
        (ComputableAnalysis.ofRat_add_equiv x (finiteRatSum xs))

theorem effectiveFinitePolynomialIntegralRaw_valid
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralRaw coeffs terms).Valid := by
  apply Integral.finiteRawSum_valid
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨k, hk, rfl⟩
  exact RealRaw.scaleRat_valid
    (Integral.raw_valid _ (Integral.exactRat_pow_integral_certificate k))

theorem effectiveFinitePolynomialIntegralAnchorRaw_valid
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralAnchorRaw coeffs terms).Valid := by
  apply Integral.finiteRawSum_valid
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨k, hk, rfl⟩
  exact RealRaw.scaleRat_valid (RealRaw.ofRat_valid _)

theorem effectiveFinitePolynomialIntegralRaw_widths_shrink :
    RealRaw.WidthsShrinkToZero
      (effectiveFinitePolynomialIntegralRaw coeffs terms).compute := by
  exact (effectiveFinitePolynomialIntegralRaw_valid coeffs terms).2.2

theorem effectiveFinitePolynomialIntegralAnchorRaw_widths_shrink :
    RealRaw.WidthsShrinkToZero
      (effectiveFinitePolynomialIntegralAnchorRaw coeffs terms).compute := by
  exact (effectiveFinitePolynomialIntegralAnchorRaw_valid coeffs terms).2.2

theorem effectiveFinitePolynomialIntegralRaw_precision_witness
    (coeffs : Nat -> Rat) (terms : Nat) (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      ((effectiveFinitePolynomialIntegralRaw coeffs terms).compute n).width <=
        eps.val := by
  exact effectiveFinitePolynomialIntegralRaw_widths_shrink
    (coeffs := coeffs) (terms := terms) eps

theorem effectiveFinitePolynomialIntegralAnchorRaw_precision_witness
    (coeffs : Nat -> Rat) (terms : Nat) (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      ((effectiveFinitePolynomialIntegralAnchorRaw coeffs terms).compute n).width <=
        eps.val := by
  exact effectiveFinitePolynomialIntegralAnchorRaw_widths_shrink
    (coeffs := coeffs) (terms := terms) eps

theorem effectiveFinitePolynomialIntegralRaw_equiv_anchor
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralRaw coeffs terms).Equiv
      (effectiveFinitePolynomialIntegralAnchorRaw coeffs terms) := by
  unfold effectiveFinitePolynomialIntegralRaw
    effectiveFinitePolynomialIntegralAnchorRaw
  apply Integral.finiteRawSum_equiv_of_forall
  · apply Integral.finiteRawListEquiv_map_of_forall
    intro k hk
    exact RealRaw.scaleRat_equiv
      (Integral.exactRat_pow_integral_raw_equiv_one_div_succ k)
  · intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact RealRaw.scaleRat_valid
      (Integral.raw_valid _ (Integral.exactRat_pow_integral_certificate k))
  · intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact RealRaw.scaleRat_valid (RealRaw.ofRat_valid _)

theorem effectiveFinitePolynomialIntegralRaw_compute_width_le
    (coeffs : Nat -> Rat) (terms stage : Nat) (bound : Rat)
    (hbound : forall k, k < terms ->
      qabs (coeffs k) *
          ((2 * (k : Rat)) * (1 / (((2 ^ stage : Nat) : Rat)))) <= bound) :
    ((effectiveFinitePolynomialIntegralRaw coeffs terms).compute stage).width <=
      (terms : Rat) * bound := by
  unfold effectiveFinitePolynomialIntegralRaw
  have hpoint : forall x, x ∈ (List.range terms).map (fun k =>
      RealRaw.scaleRat (coeffs k)
        (Integral.raw (FunctionOnInterval.exactRat (fun x => x ^ k) 0 1)
          (Integral.exactRat_pow_integral_certificate k))) ->
      (x.compute stage).width <= bound := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    rw [scaleRat_width_eq_qabs_mul]
    rw [Integral.exactRat_pow_integral_raw_compute_width]
    exact hbound k (List.mem_range.mp hk)
  simpa only [List.length_map, List.length_range] using
    (Integral.finiteRawSum_compute_width_le_of_forall
      ((List.range terms).map (fun k =>
        RealRaw.scaleRat (coeffs k)
          (Integral.raw (FunctionOnInterval.exactRat (fun x => x ^ k) 0 1)
      (Integral.exactRat_pow_integral_certificate k)))) stage bound hpoint)

theorem effectiveFinitePolynomialIntegralRaw_compute_width_le_of_bounds
    (coeffs : Nat -> Rat) (terms stage : Nat) (bound : Nat -> Rat)
    (hbound : forall k, k < terms ->
      qabs (coeffs k) *
          ((2 * (k : Rat)) * (1 / (((2 ^ stage : Nat) : Rat)))) <= bound k) :
    ((effectiveFinitePolynomialIntegralRaw coeffs terms).compute stage).width <=
      (List.range terms).foldl (fun total k => total + bound k) 0 := by
  unfold effectiveFinitePolynomialIntegralRaw
  rw [Integral.finiteRawSum_compute_width_eq_foldl]
  have hsum := RationalPartition.rat_add_fold_le_of_forall
    (xs := List.range terms)
    (term := fun k =>
      ((RealRaw.scaleRat (coeffs k)
        (Integral.raw (FunctionOnInterval.exactRat (fun x => x ^ k) 0 1)
          (Integral.exactRat_pow_integral_certificate k))).compute stage).width)
    (bound := bound) (by
      intro k hk
      rw [scaleRat_width_eq_qabs_mul]
      rw [Integral.exactRat_pow_integral_raw_compute_width]
      exact hbound k (List.mem_range.mp hk))
  simpa only [List.foldl_map] using hsum

set_option maxHeartbeats 100000000 in
theorem effectiveFinitePolynomialIntegralAnchorRaw_equiv_value
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralAnchorRaw coeffs terms).Equiv
      (RealRaw.ofRat (effectiveFinitePolynomialIntegralValue coeffs terms)) := by
  unfold effectiveFinitePolynomialIntegralAnchorRaw
    effectiveFinitePolynomialIntegralValue
  let xs : List RealRaw := (List.range terms).map (fun k =>
    RealRaw.scaleRat (coeffs k)
      (RealRaw.ofRat (1 / ((k + 1 : Nat) : Rat))))
  let ys : List RealRaw := (List.range terms).map (fun k =>
    RealRaw.ofRat (coeffs k * (1 / ((k + 1 : Nat) : Rat))))
  have hxse : forall x, x ∈ xs -> x.Valid := by
    intro x hx
    simp only [xs, List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact RealRaw.scaleRat_valid (RealRaw.ofRat_valid _)
  have hyse : forall x, x ∈ ys -> x.Valid := by
    intro x hx
    simp only [ys, List.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact RealRaw.ofRat_valid _
  have hxs : (Integral.finiteRawSum xs).Valid :=
    Integral.finiteRawSum_valid xs hxse
  have hys : (Integral.finiteRawSum ys).Valid :=
    Integral.finiteRawSum_valid ys hyse
  have hlist : (Integral.finiteRawSum xs).Equiv
      (Integral.finiteRawSum ys) := by
    apply Integral.finiteRawSum_equiv_of_forall
    · apply Integral.finiteRawListEquiv_map_of_forall
      intro k hk
      exact scaleRat_ofRat_equiv (coeffs k)
        (1 / ((k + 1 : Nat) : Rat))
    · exact hxse
    · exact hyse
  have hvalue := finiteRawSum_ofRat_equiv_sum
    ((List.range terms).map (fun k =>
      coeffs k * (1 / ((k + 1 : Nat) : Rat))))
  exact RealRaw.equiv_trans hxs hys
    (by
      unfold RealRaw.ofRat RealRaw.Valid
      exact RealRaw.ofRat_valid _)
    (by simpa [xs, ys] using hlist)
    (by simpa [ys, Function.comp_def] using hvalue)

/-- The complete finite polynomial integral bridge: the assembled computation
    is equivalent to its closed rational value.  This is the theorem a user
    should invoke when a finite polynomial integral needs to enter an
    application proof. -/
theorem effectiveFinitePolynomialIntegralRaw_equiv_value
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralRaw coeffs terms).Equiv
      (RealRaw.ofRat (effectiveFinitePolynomialIntegralValue coeffs terms)) := by
  have hvalue :
      (RealRaw.ofRat (effectiveFinitePolynomialIntegralValue coeffs terms)).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  apply RealRaw.equiv_trans
    (effectiveFinitePolynomialIntegralRaw_valid coeffs terms)
    (effectiveFinitePolynomialIntegralAnchorRaw_valid coeffs terms)
    hvalue
  · exact effectiveFinitePolynomialIntegralRaw_equiv_anchor coeffs terms
  · exact effectiveFinitePolynomialIntegralAnchorRaw_equiv_value coeffs terms

/-! A small end-to-end regression keeps the abstract polynomial bridge tied to
an ordinary calculus calculation.  The coefficient stream is finite and
rational; no completed-real integral is hidden in the statement. -/

def effectiveUnitSquareIntegralRaw : RealRaw :=
  effectiveFinitePolynomialIntegralRaw
    (fun k => if k = 2 then 1 else 0) 3

theorem effectiveUnitSquareIntegralRaw_equiv_one_third :
    effectiveUnitSquareIntegralRaw.Equiv (RealRaw.ofRat (1 / 3)) := by
  have h := effectiveFinitePolynomialIntegralRaw_equiv_value
    (fun k => if k = 2 then 1 else 0) 3
  have hvalue : finiteRatSum
      ((List.range 3).map (fun k =>
        (if k = 2 then 1 else 0) * (1 / ((k + 1 : Nat) : Rat)))) =
      (1 / 3 : Rat) := by
    native_decide
  unfold effectiveFinitePolynomialIntegralValue at h
  rw [hvalue] at h
  simpa [effectiveUnitSquareIntegralRaw] using h

def effectiveUnitCubeIntegralRaw : RealRaw :=
  effectiveFinitePolynomialIntegralRaw
    (fun k => if k = 3 then 1 else 0) 4

theorem effectiveUnitCubeIntegralRaw_equiv_one_fourth :
    effectiveUnitCubeIntegralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  have h := effectiveFinitePolynomialIntegralRaw_equiv_value
    (fun k => if k = 3 then 1 else 0) 4
  have hvalue : finiteRatSum
      ((List.range 4).map (fun k =>
        (if k = 3 then 1 else 0) * (1 / ((k + 1 : Nat) : Rat)))) =
      (1 / 4 : Rat) := by
    native_decide
  unfold effectiveFinitePolynomialIntegralValue at h
  rw [hvalue] at h
  simpa [effectiveUnitCubeIntegralRaw] using h

theorem effectiveFinitePolynomialIntegralValue_eq_endpointDifference
    (coeffs : Nat -> Rat) (terms : Nat) :
    effectiveFinitePolynomialIntegralValue coeffs terms =
      FinitePolynomial.integratedTaylorPrefix coeffs terms 1 -
        FinitePolynomial.integratedTaylorPrefix coeffs terms 0 := by
  calc
    effectiveFinitePolynomialIntegralValue coeffs terms =
        FinitePolynomial.finiteMonomialIntegralSum coeffs terms 0 1 :=
      effectiveFinitePolynomialIntegralValue_eq_finiteMonomialIntegralSum
        coeffs terms
    _ = FinitePolynomial.integratedTaylorPrefix coeffs terms 1 -
          FinitePolynomial.integratedTaylorPrefix coeffs terms 0 :=
      (effectiveFiniteTaylorFTC_endpointDifference_eq_finiteMonomialIntegralSum
        coeffs terms 0 1).symm

theorem effectiveFinitePolynomialIntegralRaw_equiv_endpointDifferenceValue
    (coeffs : Nat -> Rat) (terms : Nat) :
    (effectiveFinitePolynomialIntegralRaw coeffs terms).Equiv
      (RealRaw.ofRat
        (FinitePolynomial.integratedTaylorPrefix coeffs terms 1 -
          FinitePolynomial.integratedTaylorPrefix coeffs terms 0)) := by
  have h := effectiveFinitePolynomialIntegralRaw_equiv_value coeffs terms
  rw [effectiveFinitePolynomialIntegralValue_eq_endpointDifference] at h
  exact h

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

/-! Stable entry points for the general effective FTC interface.  The
certificate is the theorem: finite derivative bounds, local endpoint
containment, and a shrinking width schedule are enough to identify the
integral raw with the endpoint-difference raw. -/

theorem effectiveDerivativeBoundFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact h.toDerivativeBoundFTC.equiv_endpoint

theorem effectiveDerivativeBoundFTC_boundedIntegralRaw_equiv_endpointDifference
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (endpointDifferenceRaw F a b hendpoint) := by
  exact h.boundedIntegralRaw_equiv_endpointDifference hendpoint

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

theorem effectiveSinPiHalfIntegral_equiv_endpoint
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : SinPiIntegral.HalfIntegralFTCCertificate C hdefined) :
    (SinPiIntegral.halfIntegral C hdefined h.integral).Equiv
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid) := by
  exact SinPiIntegral.halfIntegral_equiv_endpoint h

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

theorem effectiveFourierSeries_stabilized_valid
    (F : EffectiveFourierSeries) :
    F.stabilized.Valid := by
  exact F.stabilized_valid

theorem effectiveFourierSeries_stage_contained
    (F : EffectiveFourierSeries) (n : Nat) :
    (QBox.point (finiteFourierSum F.root F.mode (F.stage n))).NestedIn
      (F.stabilized.compute n) := by
  exact F.stage_contained n

theorem effectiveFourierSeries_stabilized_width_le
    (F : EffectiveFourierSeries) (n : Nat) :
    (F.stabilized.compute n).width <=
      (F.candidate.compute n).width + 2 * F.radius n := by
  exact F.stabilized_width_le_of_candidate n

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
