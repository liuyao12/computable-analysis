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
