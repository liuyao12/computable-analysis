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
import ComputableAnalysis.SeriesFoundation
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

/-! Public finite algebra for accumulating identical point contributions. -/
theorem effectiveFoldlPointAddScaled {α : Type} (v : QComplex)
    (xs : List α) (acc : QBox) :
    xs.foldl (fun total _ => QBox.add total (QBox.point v)) acc =
      QBox.add acc (QBox.point (QComplex.scaleRat (xs.length : Rat) v)) := by
  exact foldl_point_add_scaled v xs acc

theorem effectiveSegmentLeftSumConstant
    (c a b : QComplex) (n : Nat) (hn : 0 < n) (evalPrecision : Nat) :
    segmentLeftSumEntire (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial) a b n evalPrecision =
      QBox.point (QComplex.mul c (QComplex.sub b a)) := by
  exact segmentLeftSum_constant c a b n hn evalPrecision

theorem effectivePolygonalLeftSumConstant
    (c start : QComplex) (vertices : List QComplex) (n : Nat) (hn : 0 < n)
    (evalPrecision : Nat) :
    polygonalLeftSumEntire (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial) (start :: vertices) n evalPrecision =
      QBox.point (polygonalConstantDifferentialDisplacement c start vertices) := by
  exact polygonalLeftSum_constant c start vertices n hn evalPrecision

theorem effectivePolygonalLeftSumConstantClosed
    (c start : QComplex) (vertices : List QComplex) (n : Nat) (hn : 0 < n)
    (evalPrecision : Nat) :
    polygonalLeftSumEntire (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial)
      (start :: (vertices ++ [start])) n evalPrecision =
      QBox.point QComplex.zero := by
  exact polygonalLeftSum_constant_closed c start vertices n hn evalPrecision

theorem effectivePolygonalLeftSumCertificateOfStageEqPoint
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {vertices : List QComplex} {evalPrecision : Nat -> Nat}
    (anchor : QComplex)
    (hcompute : forall n,
      (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n =
        QBox.point anchor) :
    PolygonalLeftSumCertificate f hEntire vertices evalPrecision := by
  exact PolygonalLeftSumCertificate.of_stage_eq_point anchor hcompute

theorem effectiveConstantClosedPolygonalLeftSumCertificate
    (c start : QComplex) (vertices : List QComplex)
    (evalPrecision : Nat -> Nat) :
    PolygonalLeftSumCertificate (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial)
      (start :: (vertices ++ [start])) evalPrecision := by
  exact constantClosedPolygonalLeftSumCertificate c start vertices evalPrecision

theorem effectivePolygonalIntegralCertificateOfStageEqPoint
    {f : EntireBoxFunctionRaw} {vertices : List QComplex}
    (anchor : QComplex)
    (hcompute : forall n, polygonalIntegralBoxEntire f vertices n =
      QBox.point anchor) :
    PolygonalIntegralCertificate f vertices := by
  exact PolygonalIntegralCertificate.of_stage_eq_point anchor hcompute

theorem effectivePolygonalLeftSumIntegralOverlapOfStageEqPoint
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat} (anchor : QComplex)
    (hleft : forall n,
      (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).compute n =
        QBox.point anchor)
    (hinterval : forall n,
      (polygonalIntegralRawEntire boxFunction vertices).compute n =
        QBox.point anchor) :
    PolygonalLeftSumIntegralOverlapCertificate f hEntire boxFunction vertices
      evalPrecision := by
  exact PolygonalLeftSumIntegralOverlapCertificate.of_stage_eq_point anchor
    hleft hinterval

theorem effectiveConstantClosedPolygonalLeftSumIntegralOverlapCertificate
    (c start : QComplex) (vertices : List QComplex)
    (evalPrecision : Nat -> Nat) :
    PolygonalLeftSumIntegralOverlapCertificate
      (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial) (constantBoxFunction c)
      (start :: (vertices ++ [start])) evalPrecision := by
  exact constantClosedPolygonalLeftSumIntegralOverlapCertificate c start vertices
    evalPrecision

def effectiveConstantPolygonalLeftSumIntegralPositiveStageAgreement
    (c start : QComplex) (vertices : List QComplex)
    (evalPrecision : Nat -> Nat) :
    PolygonalLeftSumIntegralPositiveStageAgreement
      (FunctionRaw.exact (fun _ => c))
      (by intro z; change True; trivial) (constantBoxFunction c)
      (start :: vertices) evalPrecision := by
  exact constantPolygonalLeftSumIntegralPositiveStageAgreement c start vertices
    evalPrecision

/-! Public certificate entry point for the left-endpoint polygonal integral.
The evaluator is executable at every finite stage; validity still comes from
the supplied orderedness, nesting, and shrinking certificates. -/
theorem effectivePolygonalLeftSumRawEntire_valid
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {vertices : List QComplex} {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumCertificate f hEntire vertices evalPrecision) :
    (polygonalLeftSumRawEntire f hEntire vertices evalPrecision).Valid := by
  exact polygonalLeftSumRawEntire_valid certificate

/-! Public path-integral convergence bridge.  A stagewise overlap certificate
identifies the executable left-sum and interval-box representations without
introducing a classical path limit. -/
theorem effectivePolygonalLeftSumIntegral_equiv
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat}
    (certificate : PolygonalLeftSumIntegralOverlapCertificate f hEntire
      boxFunction vertices evalPrecision) :
    certificate.leftRaw.Equiv certificate.intervalRaw := by
  exact certificate.equiv

theorem effectivePolygonalLeftSumIntegral_equiv_of_interval_anchor
    {f : FunctionRaw} {hEntire : forall z, f.domain z}
    {boxFunction : EntireBoxFunctionRaw} {vertices : List QComplex}
    {evalPrecision : Nat -> Nat} (certificate :
      PolygonalLeftSumIntegralOverlapCertificate f hEntire boxFunction
        vertices evalPrecision) {anchor : ComplexRaw}
    (hanchor : anchor.Valid)
    (hinterval_anchor : certificate.intervalRaw.Equiv anchor) :
    certificate.leftRaw.Equiv anchor := by
  exact certificate.equiv_of_interval_anchor hanchor hinterval_anchor

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

/-! Once the canonical certificate records nesting for its scheduled sum, the
    endpoint-difference theorem can safely be presented as ordinary
    subtraction of the primitive's two certified evaluations. -/
theorem effectiveCanonicalFTC_endpointDifference_apply
    {F dF : RealFunRaw} {a b : Rat}
    (hF : F.Valid)
    (h : CanonicalCandidateDerivativeFTC F dF a b) :
    h.integralRaw.Equiv
      ((F.apply hF b h.candidate.toDerivativeBoundFTC.primitive_domain_upper) -
        (F.apply hF a h.candidate.toDerivativeBoundFTC.primitive_domain_lower)) := by
  let A := F.apply hF a h.candidate.toDerivativeBoundFTC.primitive_domain_lower
  let B := F.apply hF b h.candidate.toDerivativeBoundFTC.primitive_domain_upper
  have hA : A.Valid := by
    simpa [A, RealFunRaw.apply, RealFunRaw.applyCompute, RealRaw.Valid] using
      hF a h.candidate.toDerivativeBoundFTC.primitive_domain_lower
  have hB : B.Valid := by
    simpa [B, RealFunRaw.apply, RealFunRaw.applyCompute, RealRaw.Valid] using
      hF b h.candidate.toDerivativeBoundFTC.primitive_domain_upper
  have hsub : (B - A).Valid := RealRaw.sub_valid hB hA
  have hendpoint := endpointDifferenceRaw_equiv_sub_apply hF
    h.candidate.toDerivativeBoundFTC.primitive_domain_lower
    h.candidate.toDerivativeBoundFTC.primitive_domain_upper h.endpoint_valid
  have hendpointRawValid : h.endpointRaw.Valid := by
    simpa [CanonicalCandidateDerivativeFTC.endpointRaw, endpointDifferenceRaw,
      RealRaw.Valid] using h.endpoint_valid
  exact RealRaw.equiv_trans h.integral_valid hendpointRawValid hsub
    h.integral_equiv_canonical_endpoint hendpoint

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

/-! Public acceptance interface for the normalized squared-sine example.  The
primitive and its finite derivative certificate remain explicit inputs; once
provided, the generic effective FTC and endpoint transport are available at
the focused calculus boundary. -/
theorem effectiveSinPiSquareFTC_equiv_endpoint
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (D : SinPiIntegral.SinPiSquareEffectiveFTCData S) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact D.integral_equiv_endpoint

theorem effectiveSinPiSquareFTC_equiv_value
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (D : SinPiIntegral.SinPiSquareEffectiveFTCData S)
    (hvalue : D.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))) :
    D.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact D.endpoint_equiv_of_value hvalue

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

/-! Public transport for the independent tangent-square computation.  A
stagewise rational overlap certificate is the only application-specific
input; the theorem then exposes the effective-FTC quarter-turn value through
the focused calculus entry point. -/
theorem effectiveTangentSquareIntegral_equiv_halfQuarterTurn_of_overlap
    (h : SinPiIntegral.TangentSquareIntegralEffectiveFTCOverlap) :
    SinPiIntegral.tangentSquareIntegral.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact h.to_halfQuarterTurn

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

/- Stable focused-entry-point name for the representation edge before the
   quarter-turn transport.  The shared witness proves the public stabilized
   evaluator agrees with the tangent-square anchor itself. -/
theorem effectiveDyadicPublicSquareIntegral_stabilized_equiv_tangentSquare_shared
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (h : SinPiIntegral.DyadicPublicSquareTangentSharedWitness S) :
    (SinPiIntegral.dyadicPublicSquareIntegralRaw_stabilized S
      SinPiIntegral.tangentSquareIntegral).Equiv
      SinPiIntegral.tangentSquareIntegral := by
  exact h.stabilized_equiv_tangentSquare

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

theorem effectiveLinearODEChronologicalProduct_constant
    {dimension : Nat} (B : LinearODE.RatMatrix dimension) (steps : Nat) :
    LinearODE.chronologicalProduct (fun _ => B) steps =
      LinearODE.matrixPow
        (LinearODE.matrixAdd (LinearODE.matrixIdentity dimension) B) steps := by
  exact LinearODE.chronologicalProduct_constant B steps

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

theorem effectivePeanoBakerFactorialRemainderInterval_contains_tail
    {M T : Rat} (certificate :
      LinearODE.PeanoBakerFactorialRemainderCertificate M T eps)
    (hM : 0 <= M) (hT : 0 <= T) (terms : Nat) :
    (LinearODE.PeanoBakerFactorialRemainderCertificate.interval
      certificate terms).lo <=
        LinearODE.peanoBakerFactorialTail M T certificate.start terms /\
      LinearODE.peanoBakerFactorialTail M T certificate.start terms <=
        (LinearODE.PeanoBakerFactorialRemainderCertificate.interval
          certificate terms).hi := by
  exact certificate.tail_mem_interval hM hT terms

theorem effectivePeanoBakerFactorialRemainderInterval_width_le
    {M T : Rat} (certificate :
      LinearODE.PeanoBakerFactorialRemainderCertificate M T eps)
    (terms : Nat) :
    (LinearODE.PeanoBakerFactorialRemainderCertificate.interval
      certificate terms).width <= eps.val := by
  unfold LinearODE.PeanoBakerFactorialRemainderCertificate.interval
    QInterval.width
  have htail := certificate.tail_le_eps terms
  grind [Rat.sub_eq_add_neg]

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

/-! The direct candidate-facing variant keeps the finite rational witness
    lists and admissibility proofs visible to callers. -/
theorem effectiveSinPiHalfIntegral_equiv_reciprocalPi_of_candidate_family
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
    (family : SinPiIntegral.DyadicCanonicalCertificateCandidateFamily S.inverse)
    (hintegral : (Integral.integral g 0 ((1 : Rat) / 2) cg).Equiv
      SinPiIntegral.reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv SinPiIntegral.reciprocalPiRaw := by
  exact S.halfIntegral_equiv_reciprocalPi_of_candidate_family
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

/-! Consumer-facing integral object for an interval-regular schedule.  The
schedule already carries the construction certificate; this alias keeps
downstream proofs at the focused calculus boundary instead of reaching into
the implementation namespace. -/
def effectiveIntervalRegularDarbouxScheduleIntegralFor
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval) : RealRaw :=
  Integral.intervalRegularDarbouxScheduleIntegralFor s

def effectiveIntervalRegularDarbouxSchedule_ofAutomaticLinearPrecision
    {F : FunctionOnInterval} (hregular : IntervalRegularOn F)
    {hinterval : F.lower <= F.upper} (lengthBound : Nat)
    (hLength : F.upper - F.lower <= (lengthBound : Rat))
    (nested : forall n m, n <= m ->
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) n).lo <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) m).lo /\
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) m).hi <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) n).hi) :
    Integral.IntervalRegularDarbouxSchedule F hregular hinterval :=
  Integral.IntervalRegularDarbouxSchedule.ofAutomaticLinearPrecision
    hregular lengthBound hLength nested

theorem effectiveIntervalRegularDarbouxScheduleRaw_linear_width_le
    {F : FunctionOnInterval} (hregular : IntervalRegularOn F)
    {hinterval : F.lower <= F.upper} (lengthBound : Nat)
    (hLength : F.upper - F.lower <= (lengthBound : Rat))
    (nested : forall n m, n <= m ->
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) n).lo <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) m).lo /\
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) m).hi <=
      (Integral.intervalRegularDarbouxScheduleCompute F hinterval hregular
        (fun n => Integral.intervalRegularAutomaticPieces hregular lengthBound
          (fun k => k) n)
        (fun n => n)
        (fun n => Integral.intervalRegularAutomaticPieces_pos hregular lengthBound
          (fun k => k) n) n).hi) :
    ∀ n : Nat,
      ((Integral.intervalRegularDarbouxScheduleRaw
        (effectiveIntervalRegularDarbouxSchedule_ofAutomaticLinearPrecision
          hregular lengthBound hLength nested)).compute n).width <=
        (F.upper - F.lower) * (1 / ((n + 1 : Nat) : Rat)) := by
  exact Integral.intervalRegularDarbouxScheduleRaw_linear_width_le
    hregular lengthBound hLength nested

theorem effectiveIntervalRegularDarbouxScheduleIntegralFor_valid
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval) :
    (effectiveIntervalRegularDarbouxScheduleIntegralFor s).Valid := by
  exact Integral.intervalRegularDarbouxScheduleIntegralFor_valid s

theorem effectiveIntervalRegularDarbouxScheduleIntegralFor_precision_witness
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval)
    (eps : QPos) :
    ∃ n : Nat,
      ((effectiveIntervalRegularDarbouxScheduleIntegralFor s).compute n).width <=
        eps.val := by
  exact Integral.intervalRegularDarbouxScheduleIntegralFor_precision_witness s eps

theorem effectiveIntervalRegularDarbouxScheduleIntegralFor_width_le_of_tolerance
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hinterval : F.lower <= F.upper}
    (s : Integral.IntervalRegularDarbouxSchedule F hregular hinterval)
    (n : Nat) (eps : Rat)
    (hbudget : (F.upper - F.lower) *
        (1 / ((s.evalPrecision n + 1 : Nat) : Rat)) <= eps) :
    ((effectiveIntervalRegularDarbouxScheduleIntegralFor s).compute n).width <=
      eps := by
  exact Integral.intervalRegularDarbouxScheduleIntegralFor_width_le_of_tolerance
    s n eps hbudget

/-! The arbitrary-power monomial FTC family is exposed as one public theorem:
the dyadic integral of `x^k` on the unit interval agrees with the rational
endpoint value `1 / (k + 1)`. -/
theorem effectiveExactRatPowIntegral_equiv_one_div_succ (k : Nat) :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
      (Integral.exactRat_pow_integral_certificate k)).Equiv
      (RealRaw.ofRat (1 / ((k + 1 : Nat) : Rat))) := by
  exact Integral.exactRat_pow_integral_raw_equiv_one_div_succ k

theorem effectiveExactRatPowIntegral_equiv_pow_endpoint (k : Nat) :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
      (Integral.exactRat_pow_integral_certificate k)).Equiv
      (endpointDifferenceRaw
        (Integral.powPrimitiveOnUnit k).toRealFunRaw 0 1
        (Integral.powPrimitiveOnUnit_endpoint_valid k)) := by
  exact Integral.exactRat_pow_integral_raw_equiv_pow_endpoint k

def effectiveExactRatPow_definiteIdentity (k : Nat) :
    Integral.DefiniteIdentityFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ k) 0 1)
      (Integral.powPrimitiveOnUnit k) := by
  exact Integral.exactRat_pow_definiteIdentity k

theorem effectiveFiniteFourierSampleInnerProduct_add
    (root : QComplex) (length mode : Nat)
    (sample₁ sample₂ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.add (sample₁ k) (sample₂ k)) :
    finiteFourierSampleInnerProduct root length mode sample =
      QComplex.add
        (finiteFourierSampleInnerProduct root length mode sample₁)
        (finiteFourierSampleInnerProduct root length mode sample₂) := by
  exact finiteFourierSampleInnerProduct_add root length mode sample₁ sample₂
    sample hsample

theorem effectiveFiniteFourierSampleInnerProduct_scale
    (root : QComplex) (length mode : Nat)
    (r : Rat) (sample₀ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.scaleRat r (sample₀ k)) :
    finiteFourierSampleInnerProduct root length mode sample =
      QComplex.scaleRat r
        (finiteFourierSampleInnerProduct root length mode sample₀) := by
  exact finiteFourierSampleInnerProduct_scale root length mode r sample₀ sample
    hsample

theorem effectiveFiniteFourierSampleInnerProduct_conj
    (root : QComplex) (length mode : Nat)
    (sample₀ sample : Nat → QComplex)
    (hsample : ∀ k, sample k = QComplex.conj (sample₀ k)) :
    finiteFourierSampleInnerProduct (QComplex.conj root) length mode sample =
      QComplex.conj
        (finiteFourierSampleInnerProduct root length mode sample₀) := by
  exact finiteFourierSampleInnerProduct_conj root length mode sample₀ sample
    hsample

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

theorem effectiveFiniteTaylorEndpointRaw_add
    (coeffs₁ coeffs₂ : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw (fun k => coeffs₁ k + coeffs₂ k) terms a b).Equiv
      (effectiveFiniteTaylorEndpointRaw coeffs₁ terms a b +
        effectiveFiniteTaylorEndpointRaw coeffs₂ terms a b) := by
  have hsum := effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    (fun k => coeffs₁ k + coeffs₂ k) terms a b
  have h₁ := effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    coeffs₁ terms a b
  have h₂ := effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    coeffs₂ terms a b
  let q₁ := FinitePolynomial.finiteMonomialIntegralSum coeffs₁ terms a b
  let q₂ := FinitePolynomial.finiteMonomialIntegralSum coeffs₂ terms a b
  have hq₁valid : (RealRaw.ofRat q₁).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hq₂valid : (RealRaw.ofRat q₂).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have htransport :
      (effectiveFiniteTaylorEndpointRaw coeffs₁ terms a b +
        effectiveFiniteTaylorEndpointRaw coeffs₂ terms a b).Equiv
        (RealRaw.ofRat q₁ + RealRaw.ofRat q₂) := by
    exact RealRaw.add_equiv
      (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
      hq₁valid
      (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
      hq₂valid
      (by simpa [q₁] using h₁)
      (by simpa [q₂] using h₂)
  have hcollapse :
      (RealRaw.ofRat q₁ + RealRaw.ofRat q₂).Equiv
        (RealRaw.ofRat
          (FinitePolynomial.finiteMonomialIntegralSum
            (fun k => coeffs₁ k + coeffs₂ k) terms a b)) := by
    have h := ComputableAnalysis.ofRat_add_equiv q₁ q₂
    have hq : q₁ + q₂ =
        FinitePolynomial.finiteMonomialIntegralSum
          (fun k => coeffs₁ k + coeffs₂ k) terms a b := by
      dsimp [q₁, q₂]
      exact (effectiveFinitePolynomialIntegralSum_add coeffs₁ coeffs₂ terms a b).symm
    rw [← hq]
    exact h
  have hright :
      (effectiveFiniteTaylorEndpointRaw coeffs₁ terms a b +
        effectiveFiniteTaylorEndpointRaw coeffs₂ terms a b).Equiv
        (RealRaw.ofRat
          (FinitePolynomial.finiteMonomialIntegralSum
            (fun k => coeffs₁ k + coeffs₂ k) terms a b)) := by
    exact RealRaw.equiv_trans
      (RealRaw.add_valid
        (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
        (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _))
      (RealRaw.add_valid hq₁valid hq₂valid)
      (by
        unfold RealRaw.ofRat RealRaw.Valid
        exact RealRaw.ofRat_valid _)
      htransport hcollapse
  exact RealRaw.equiv_trans
    (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
    (by
      unfold RealRaw.ofRat RealRaw.Valid
      exact RealRaw.ofRat_valid _)
    (RealRaw.add_valid
      (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
      (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _))
    hsum (RealRaw.equiv_symm hright)

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

theorem effectivePrefixTail_valid_of_components
    (head tail : RealRaw) (hhead : head.Valid) (htail : tail.Valid) :
    (head + tail).Valid := by
  exact RealRaw.add_valid hhead htail

theorem effectivePrefixTail_widths_shrink_of_components
    (head tail : RealRaw) (hhead : head.Valid) (htail : tail.Valid) :
    RealRaw.WidthsShrinkToZero (head + tail).compute := by
  exact (RealRaw.add_valid hhead htail).2.2

theorem effectivePrefixTail_precision_witness_of_components
    (head tail : RealRaw) (hhead : head.Valid) (htail : tail.Valid)
    (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      ((head + tail).compute n).width <= eps.val := by
  let half : QPos :=
    { val := eps.val / 2
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)) }
  obtain ⟨Nhead, hhead'⟩ := hhead.2.2 half
  obtain ⟨Ntail, htail'⟩ := htail.2.2 half
  refine ⟨max Nhead Ntail, ?_⟩
  intro n hn
  rw [effectivePrefixTail_width_eq_add]
  have hh := hhead' n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have ht := htail' n (Nat.le_trans (Nat.le_max_right _ _) hn)
  calc
    (head.compute n).width + (tail.compute n).width <= half.val + half.val :=
      _root_.ComputableAnalysis.rat_add_le_add hh ht
    _ = eps.val := by
      dsimp [half]
      rw [Rat.div_def]
      grind

theorem effectiveFiniteRawSum_valid_of_components
    (xs : List RealRaw) (hxs : forall x, x ∈ xs -> x.Valid) :
    (Integral.finiteRawSum xs).Valid := by
  exact Integral.finiteRawSum_valid xs hxs

theorem effectiveFiniteRawSum_widths_shrink_of_components
    (xs : List RealRaw) (hxs : forall x, x ∈ xs -> x.Valid) :
    RealRaw.WidthsShrinkToZero (Integral.finiteRawSum xs).compute := by
  exact (effectiveFiniteRawSum_valid_of_components xs hxs).2.2

theorem effectiveFiniteRawSum_precision_witness_of_components
    (xs : List RealRaw) (hxs : forall x, x ∈ xs -> x.Valid)
    (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      ((Integral.finiteRawSum xs).compute n).width <= eps.val := by
  exact effectiveFiniteRawSum_widths_shrink_of_components xs hxs eps

theorem effectiveFiniteRawSum_equiv_of_components
    {xs ys : List RealRaw}
    (hxy : Integral.FiniteRawListEquiv xs ys)
    (hxs : forall x, x ∈ xs -> x.Valid)
    (hys : forall y, y ∈ ys -> y.Valid) :
    (Integral.finiteRawSum xs).Equiv (Integral.finiteRawSum ys) := by
  exact Integral.finiteRawSum_equiv_of_forall hxy hxs hys

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

theorem effectiveFiniteTaylorEndpointRaw_scale
    (c : Rat) (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    (effectiveFiniteTaylorEndpointRaw (fun k => c * coeffs k) terms a b).Equiv
      (RealRaw.scaleRat c (effectiveFiniteTaylorEndpointRaw coeffs terms a b)) := by
  have hscaled := effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    (fun k => c * coeffs k) terms a b
  have hbase := effectiveFiniteTaylorEndpointRaw_equiv_finiteMonomialSum
    coeffs terms a b
  let q := FinitePolynomial.finiteMonomialIntegralSum coeffs terms a b
  let cq := FinitePolynomial.finiteMonomialIntegralSum
    (fun k => c * coeffs k) terms a b
  have hqvalid : (RealRaw.ofRat q).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hcqvalid : (RealRaw.ofRat cq).Valid := by
    unfold RealRaw.ofRat RealRaw.Valid
    exact RealRaw.ofRat_valid _
  have hscale :
      (RealRaw.ofRat cq).Equiv (RealRaw.scaleRat c (RealRaw.ofRat q)) := by
    have hq : cq = c * q := by
      dsimp [cq, q]
      exact effectiveFinitePolynomialIntegralSum_scale c coeffs terms a b
    rw [hq]
    exact RealRaw.equiv_symm (scaleRat_ofRat_equiv c q)
  have htransport :
      (RealRaw.scaleRat c (RealRaw.ofRat q)).Equiv
        (RealRaw.scaleRat c (effectiveFiniteTaylorEndpointRaw coeffs terms a b)) := by
    exact RealRaw.equiv_symm (RealRaw.scaleRat_equiv hbase)
  have hscaleTransport :
      (RealRaw.ofRat cq).Equiv
        (RealRaw.scaleRat c (effectiveFiniteTaylorEndpointRaw coeffs terms a b)) := by
    exact RealRaw.equiv_trans hcqvalid
      (RealRaw.scaleRat_valid hqvalid)
      (RealRaw.scaleRat_valid (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _))
      hscale htransport
  exact RealRaw.equiv_trans
    (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _)
    hcqvalid
    (RealRaw.scaleRat_valid (effectiveFiniteTaylorEndpointRaw_valid _ _ _ _))
    hscaled hscaleTransport

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

theorem effectiveSinPiHalfIntegral_equiv_reciprocalPi_of_FTC
    {C : RationalCircle.GeometricTrig.FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : SinPiIntegral.HalfIntegralFTCCertificate C hdefined)
    (hendpoint :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid).Equiv SinPiIntegral.reciprocalPiRaw) :
    (SinPiIntegral.halfIntegral C hdefined h.integral).Equiv
      SinPiIntegral.reciprocalPiRaw := by
  exact SinPiIntegral.halfIntegral_equiv_reciprocalPi_of_FTC h hendpoint

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

/-! Finite Fourier synthesis is linear in its coefficient table.  These
public wrappers keep the algebraic stage interface next to the stabilized
Fourier object, before any termwise-limit theorem is attempted. -/
theorem effectiveFiniteFourierSynthesisAt_add
    (root : QComplex) (k : Nat) (modes : List Nat)
    (coefficient₁ coefficient₂ coefficient : Nat → QComplex)
    (hcoefficient : ∀ mode, mode ∈ modes →
      coefficient mode = QComplex.add (coefficient₁ mode) (coefficient₂ mode)) :
    finiteFourierSynthesisAt root k modes coefficient =
      QComplex.add
        (finiteFourierSynthesisAt root k modes coefficient₁)
        (finiteFourierSynthesisAt root k modes coefficient₂) := by
  exact finiteFourierSynthesisAt_add root k modes coefficient₁ coefficient₂
    coefficient hcoefficient

theorem effectiveFiniteFourierSynthesisAt_scale
    (root : QComplex) (k : Nat) (modes : List Nat)
    (r : Rat) (coefficient₀ coefficient : Nat → QComplex)
    (hcoefficient : ∀ mode, mode ∈ modes →
      coefficient mode = QComplex.scaleRat r (coefficient₀ mode)) :
    finiteFourierSynthesisAt root k modes coefficient =
      QComplex.scaleRat r
        (finiteFourierSynthesisAt root k modes coefficient₀) := by
  exact finiteFourierSynthesisAt_scale root k modes r coefficient₀ coefficient
    hcoefficient

theorem effectiveFiniteFourierSynthesisAt_conj
    (root : QComplex) (k : Nat) (modes : List Nat)
    (coefficient₀ coefficient : Nat → QComplex)
    (hcoefficient : ∀ mode, mode ∈ modes →
      coefficient mode = QComplex.conj (coefficient₀ mode)) :
    finiteFourierSynthesisAt (QComplex.conj root) k modes coefficient =
      QComplex.conj
        (finiteFourierSynthesisAt root k modes coefficient₀) := by
  exact finiteFourierSynthesisAt_conj root k modes coefficient₀ coefficient
    hcoefficient

theorem effectiveFiniteFourierReconstruction_coefficient_formula
    (certificate : FiniteFourierReconstructionCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.orthogonality.modes) :
    certificate.coefficient mode =
      QComplex.scaleRat
        (1 / (certificate.orthogonality.length : Rat))
        (finiteFourierSampleInnerProduct
          certificate.orthogonality.root certificate.orthogonality.length
          mode certificate.sample) := by
  exact certificate.coefficient_formula_at hmode

theorem effectiveFiniteFourierReconstruction_reconstructs
    (certificate : FiniteFourierReconstructionCertificate)
    {k : Nat} (hk : k < certificate.orthogonality.length) :
    finiteFourierSynthesisAt certificate.orthogonality.root k
        certificate.orthogonality.modes certificate.coefficient =
      certificate.sample k := by
  exact certificate.reconstructs hk

theorem effectiveFiniteFourierReconstruction_reconstructs_of_coefficient_congr
    (certificate : FiniteFourierReconstructionCertificate)
    (coefficient' : Nat → QComplex)
    (hcoeff : ∀ mode, mode ∈ certificate.orthogonality.modes →
      coefficient' mode = certificate.coefficient mode)
    {k : Nat} (hk : k < certificate.orthogonality.length) :
    finiteFourierSynthesisAt certificate.orthogonality.root k
        certificate.orthogonality.modes coefficient' =
      certificate.sample k := by
  exact certificate.reconstructs_of_coefficient_congr coefficient' hcoeff hk

theorem effectiveFourPointComplexFourierTransform_parseval
    (x₀ x₁ x₂ x₃ : QComplex) :
    QComplex.normSq
          (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 0) +
        QComplex.normSq
          (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 1) +
        QComplex.normSq
          (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 2) +
        QComplex.normSq
          (fourPointComplexFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (QComplex.normSq x₀ + QComplex.normSq x₁ +
        QComplex.normSq x₂ + QComplex.normSq x₃) := by
  exact fourPointComplexFourierTransform_parseval x₀ x₁ x₂ x₃

/-! The finite-energy boundary is public at the same scoped entry point.  It
packages an omitted Fourier tail as a rational interval, without introducing
measurable functions or a completed Hilbert space. -/
theorem effectiveFourierEnergyInterval_ordered
    (certificate : FiniteFourierEnergyTailCertificate) :
    (certificate.energyInterval).lo <= (certificate.energyInterval).hi := by
  exact certificate.energyInterval_ordered

theorem effectiveFourierEnergyInterval_contains_total
    (certificate : FiniteFourierEnergyTailCertificate) :
    (certificate.energyInterval).ContainsInterval
      { lo := certificate.totalEnergy, hi := certificate.totalEnergy } := by
  exact certificate.energyInterval_contains_total

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

/-! Signed products close the gap left by the nonnegative product adapter in
`Calculus.lean`.  The four-corner rational interval product is valid for any
two valid raw real values; boundedness is obtained from their stage-zero
intervals, not from a completed real-number model. -/
theorem effectiveRealFunRaw_mul_valid
    {f g : RealFunRaw} (hf : f.Valid) (hg : g.Valid) :
    (RealFunRaw.mul f g).Valid := by
  intro x hx
  let X : RealRaw := { compute := f.compute x }
  let Y : RealRaw := { compute := g.compute x }
  have hX : X.Valid := by
    simpa [X, RealRaw.Valid, RealFunRaw.applyCompute] using hf x hx.1
  have hY : Y.Valid := by
    simpa [Y, RealRaw.Valid, RealFunRaw.applyCompute] using hg x hx.2
  have hproduct : (X * Y).Valid := RealRaw.mul_valid hX hY
  change RealRaw.ValidCompute (RealRaw.mulCompute X Y) at hproduct
  change RealRaw.ValidCompute (RealRaw.mulCompute X Y)
  exact hproduct

/-! Addition has the same representation-transport property as multiplication.
The proof is pointwise rational box arithmetic: overlapping input boxes give
overlapping sums. -/
theorem effectiveComplexRaw_add_equiv
    {z z' w w' : ComplexRaw}
    (hz : z.Valid) (hz' : z'.Valid)
    (hw : w.Valid) (hw' : w'.Valid)
    (hzz' : z.Equiv z') (hww' : w.Equiv w') :
    (ComplexRaw.add z w).Equiv (ComplexRaw.add z' w') := by
  intro n
  have hzz := (ComplexRaw.compareAt_overlap_iff z z' n n).1 (hzz' n)
  have hww := (ComplexRaw.compareAt_overlap_iff w w' n n).1 (hww' n)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z w) (ComplexRaw.add z' w') n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add at *
  simp only [QComplex.le_def] at hzz hww
  constructor
  · constructor <;> grind [Rat.add_assoc]
  · constructor <;> grind [Rat.add_assoc]

/-! The additive identity is also representation transport: adding the
canonical rational zero changes neither coordinate interval.  As with all
function-level identities below, the statement is an equivalence of raw
computations rather than definitional equality. -/
theorem effectiveComplexRaw_zero_add_equiv
    {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.add ComplexRaw.zero z).Equiv z := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add ComplexRaw.zero z) z n n).2
  change QBox.Overlaps
    (QBox.add (ComplexRaw.zero.compute n) (z.compute n)) (z.compute n)
  unfold ComplexRaw.zero ComplexRaw.ofQComplex
    QBox.add QBox.Overlaps QComplex.add
  simp [QComplex.zero, QComplex.le_def]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_add_zero_equiv
    {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.add z ComplexRaw.zero).Equiv z := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z ComplexRaw.zero) z n n).2
  change QBox.Overlaps
    (QBox.add (z.compute n) (ComplexRaw.zero.compute n)) (z.compute n)
  unfold ComplexRaw.zero ComplexRaw.ofQComplex
    QBox.add QBox.Overlaps QComplex.add
  simp [QComplex.zero, QComplex.le_def]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_add_comm_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.add z w).Equiv (ComplexRaw.add w z) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z w) (ComplexRaw.add w z) n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.add_comm]

theorem effectiveComplexRaw_add_assoc_equiv
    {z w u : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hu : u.Valid) :
    (ComplexRaw.add (ComplexRaw.add z w) u).Equiv
      (ComplexRaw.add z (ComplexRaw.add w u)) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have huorder_re : (u.compute n).lo.re ≤ (u.compute n).hi.re := by
    have h := (hu.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have huorder_im : (u.compute n).lo.im ≤ (u.compute n).hi.im := by
    have h := (hu.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add (ComplexRaw.add z w) u)
    (ComplexRaw.add z (ComplexRaw.add w u)) n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.add_assoc]

theorem effectiveComplexRaw_scaleRat_add_equiv_of_nonneg
    (r : Rat) (hr : 0 <= r) {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.scaleRat r (ComplexRaw.add z w)).Equiv
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.scaleRat r (ComplexRaw.add z w))
    (ComplexRaw.add (ComplexRaw.scaleRat r z)
      (ComplexRaw.scaleRat r w)) n n).2
  simp only [ComplexRaw.scaleRat, ComplexRaw.add, QBox.scaleRat,
    QBox.add, if_pos hr]
  change QBox.Overlaps
    { lo := { re := r * ((z.compute n).lo.re + (w.compute n).lo.re),
              im := r * ((z.compute n).lo.im + (w.compute n).lo.im) },
      hi := { re := r * ((z.compute n).hi.re + (w.compute n).hi.re),
              im := r * ((z.compute n).hi.im + (w.compute n).hi.im) } }
    { lo := { re := r * (z.compute n).lo.re + r * (w.compute n).lo.re,
              im := r * (z.compute n).lo.im + r * (w.compute n).lo.im },
      hi := { re := r * (z.compute n).hi.re + r * (w.compute n).hi.re,
              im := r * (z.compute n).hi.im + r * (w.compute n).hi.im } }
  unfold QBox.Overlaps
  have hsum_re : (z.compute n).lo.re + (w.compute n).lo.re ≤
      (z.compute n).hi.re + (w.compute n).hi.re := by
    grind
  have hsum_im : (z.compute n).lo.im + (w.compute n).lo.im ≤
      (z.compute n).hi.im + (w.compute n).hi.im := by
    grind
  have hscaled_re := Rat.mul_le_mul_of_nonneg_left hsum_re hr
  have hscaled_im := Rat.mul_le_mul_of_nonneg_left hsum_im hr
  constructor <;> constructor <;> grind [Rat.mul_add]

theorem effectiveComplexRaw_scaleRat_add_equiv
    (r : Rat) {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.scaleRat r (ComplexRaw.add z w)).Equiv
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) := by
  by_cases hr : 0 <= r
  · exact effectiveComplexRaw_scaleRat_add_equiv_of_nonneg r hr hz hw
  · have hrneg : r < 0 := by grind
    intro n
    have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
      have h := (hz.1 n).1
      unfold QBox.width at h
      grind [Rat.sub_eq_add_neg]
    have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
      have h := (hz.1 n).2
      unfold QBox.height at h
      grind [Rat.sub_eq_add_neg]
    have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
      have h := (hw.1 n).1
      unfold QBox.width at h
      grind [Rat.sub_eq_add_neg]
    have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
      have h := (hw.1 n).2
      unfold QBox.height at h
      grind [Rat.sub_eq_add_neg]
    apply (ComplexRaw.compareAt_overlap_iff
      (ComplexRaw.scaleRat r (ComplexRaw.add z w))
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) n n).2
    simp only [ComplexRaw.scaleRat, ComplexRaw.add, QBox.scaleRat,
      QBox.add, if_neg hr]
    change QBox.Overlaps
      { lo := { re := r * ((z.compute n).hi.re + (w.compute n).hi.re),
                im := r * ((z.compute n).hi.im + (w.compute n).hi.im) },
        hi := { re := r * ((z.compute n).lo.re + (w.compute n).lo.re),
                im := r * ((z.compute n).lo.im + (w.compute n).lo.im) } }
      { lo := { re := r * (z.compute n).hi.re + r * (w.compute n).hi.re,
                im := r * (z.compute n).hi.im + r * (w.compute n).hi.im },
        hi := { re := r * (z.compute n).lo.re + r * (w.compute n).lo.re,
                im := r * (z.compute n).lo.im + r * (w.compute n).lo.im } }
    unfold QBox.Overlaps
    have hsum_re : (z.compute n).lo.re + (w.compute n).lo.re ≤
        (z.compute n).hi.re + (w.compute n).hi.re := by
      grind
    have hsum_im : (z.compute n).lo.im + (w.compute n).lo.im ≤
        (z.compute n).hi.im + (w.compute n).hi.im := by
      grind
    have hscaled_re' := Rat.mul_le_mul_of_nonneg_left hsum_re
      (by grind : 0 ≤ -r)
    have hscaled_im' := Rat.mul_le_mul_of_nonneg_left hsum_im
      (by grind : 0 ≤ -r)
    have hscaled_re : r * ((z.compute n).hi.re + (w.compute n).hi.re) ≤
        r * ((z.compute n).lo.re + (w.compute n).lo.re) := by
      grind [Rat.neg_mul]
    have hscaled_im : r * ((z.compute n).hi.im + (w.compute n).hi.im) ≤
        r * ((z.compute n).lo.im + (w.compute n).lo.im) := by
      grind [Rat.neg_mul]
    constructor <;> constructor <;> grind [Rat.mul_add]

def FunctionRaw.zero : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.zero

def FunctionRaw.one : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.point QComplex.one

def FunctionRaw.constant (c : QComplex) : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.point c

theorem FunctionRaw.zero_valid : FunctionRaw.zero.Valid := by
  intro z hz
  change ComplexRaw.zero.Valid
  exact ComplexRaw.ofQComplex_valid QComplex.zero

theorem FunctionRaw.one_valid : FunctionRaw.one.Valid := by
  intro z hz
  change ComplexRaw.ofQComplex QComplex.one |>.Valid
  exact ComplexRaw.ofQComplex_valid QComplex.one

theorem FunctionRaw.constant_valid (c : QComplex) :
    (FunctionRaw.constant c).Valid := by
  intro z hz
  change (ComplexRaw.ofQComplex c).Valid
  exact ComplexRaw.ofQComplex_valid c

theorem FunctionRaw.constant_agreeOnCommonDomain (c : QComplex) :
    (FunctionRaw.constant c).AgreeOnCommonDomain
      (FunctionRaw.constant c) := by
  intro z hleft hright
  exact ComplexRaw.equiv_refl
    ((FunctionRaw.constant c).evalRaw z hleft)
    (FunctionRaw.constant_valid c z hleft)

theorem effectiveMulRealInterval_one_overlap {a b : Rat} (hab : a <= b) :
    QInterval.Overlaps
      (QBox.mulRealInterval a b 1 1)
      ({ lo := a, hi := b } : QInterval) := by
  by_cases ha : 0 <= a
  · have heq := QBox.mulRealInterval_of_nonneg ha hab
      (by native_decide : (0 : Rat) <= 1)
      (by native_decide : (1 : Rat) <= 1)
    rw [heq]
    simp [QInterval.Overlaps]
    exact hab
  · have hault : a < 0 := by grind
    by_cases hb : b <= 0
    · unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind
    · have hbpos : 0 < b := by grind
      unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind

theorem effectiveMulRealInterval_zero {a b : Rat} :
    QBox.mulRealInterval a b 0 0 = ({ lo := 0, hi := 0 } : QInterval) := by
  unfold QBox.mulRealInterval min4 max4 minRat maxRat2
  simp

theorem effectiveMulRealInterval_zero_left {a b : Rat} :
    QBox.mulRealInterval 0 0 a b = ({ lo := 0, hi := 0 } : QInterval) := by
  unfold QBox.mulRealInterval min4 max4 minRat maxRat2
  simp

theorem effectiveMulRealInterval_one_left_overlap {a b : Rat} (hab : a <= b) :
    QInterval.Overlaps
      (QBox.mulRealInterval 1 1 a b)
      ({ lo := a, hi := b } : QInterval) := by
  by_cases ha : 0 <= a
  · have heq := QBox.mulRealInterval_of_nonneg
      (by native_decide : (0 : Rat) <= 1)
      (by native_decide : (1 : Rat) <= 1) ha hab
    rw [heq]
    simp [QInterval.Overlaps]
    exact hab
  · have hault : a < 0 := by grind
    by_cases hb : b <= 0
    · unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind
    · have hbpos : 0 < b := by grind
      unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind

theorem effectiveComplexRaw_mul_one_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul z ComplexRaw.one).Equiv z := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hreal := effectiveMulRealInterval_one_overlap hzre
  have himag := effectiveMulRealInterval_one_overlap hzim
  have hreal' :
      (QBox.mulRealInterval (z.compute n).lo.re (z.compute n).hi.re 1 1).lo ≤
        (z.compute n).hi.re /\
      (z.compute n).lo.re ≤
        (QBox.mulRealInterval (z.compute n).lo.re (z.compute n).hi.re 1 1).hi := by
    simpa [QInterval.Overlaps] using hreal
  have himag' :
      (QBox.mulRealInterval (z.compute n).lo.im (z.compute n).hi.im 1 1).lo ≤
        (z.compute n).hi.im /\
      (z.compute n).lo.im ≤
        (QBox.mulRealInterval (z.compute n).lo.im (z.compute n).hi.im 1 1).hi := by
    simpa [QInterval.Overlaps] using himag
  have hzeroRe := effectiveMulRealInterval_zero
      (a := (z.compute n).lo.im) (b := (z.compute n).hi.im)
  have hzeroIm := effectiveMulRealInterval_zero
      (a := (z.compute n).lo.re) (b := (z.compute n).hi.re)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z ComplexRaw.one) z n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (QBox.point QComplex.one)) (z.compute n)
  simp [QBox.mul, QBox.point, QComplex.one, hzeroRe, hzeroIm]
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hreal_lo := hreal'.1
  have hreal_hi := hreal'.2
  have himag_lo := himag'.1
  have himag_hi := himag'.2
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_one_mul_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul ComplexRaw.one z).Equiv z := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hreal0 := effectiveMulRealInterval_one_left_overlap hzre
  have himag0 := effectiveMulRealInterval_one_left_overlap hzim
  have hreal :
      (QBox.mulRealInterval 1 1 (z.compute n).lo.re
        (z.compute n).hi.re).lo ≤ (z.compute n).hi.re /\
      (z.compute n).lo.re ≤
        (QBox.mulRealInterval 1 1 (z.compute n).lo.re
          (z.compute n).hi.re).hi := by
    simpa [QInterval.Overlaps] using hreal0
  have himag :
      (QBox.mulRealInterval 1 1 (z.compute n).lo.im
        (z.compute n).hi.im).lo ≤ (z.compute n).hi.im /\
      (z.compute n).lo.im ≤
        (QBox.mulRealInterval 1 1 (z.compute n).lo.im
          (z.compute n).hi.im).hi := by
    simpa [QInterval.Overlaps] using himag0
  have hzeroRe := effectiveMulRealInterval_zero_left
      (a := (z.compute n).lo.im) (b := (z.compute n).hi.im)
  have hzeroIm := effectiveMulRealInterval_zero_left
      (a := (z.compute n).lo.re) (b := (z.compute n).hi.re)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul ComplexRaw.one z) z n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.point QComplex.one) (z.compute n)) (z.compute n)
  simp [QBox.mul, QBox.point, QComplex.one, hzeroRe, hzeroIm]
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hreal_lo := hreal.1
  have hreal_hi := hreal.2
  have himag_lo := himag.1
  have himag_hi := himag.2
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_mul_zero_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul z ComplexRaw.zero).Equiv ComplexRaw.zero := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z ComplexRaw.zero) ComplexRaw.zero n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (QBox.point QComplex.zero))
    (QBox.point QComplex.zero)
  simp [QBox.mul, QBox.point, QComplex.zero,
    effectiveMulRealInterval_zero, QInterval.Overlaps]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_zero_mul_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul ComplexRaw.zero z).Equiv ComplexRaw.zero := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul ComplexRaw.zero z) ComplexRaw.zero n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.point QComplex.zero) (z.compute n))
    (QBox.point QComplex.zero)
  simp [QBox.mul, QBox.point, QComplex.zero,
    effectiveMulRealInterval_zero_left, QInterval.Overlaps]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_mul_comm_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul z w).Equiv (ComplexRaw.mul w z) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z w) (ComplexRaw.mul w z) n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (w.compute n))
    (QBox.mul (w.compute n) (z.compute n))
  unfold QBox.mul QBox.Overlaps QBox.mulRealInterval
    min4 max4 minRat maxRat2
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.mul_comm]

theorem effectiveComplexRaw_mul_assoc_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul (ComplexRaw.mul z w) v).Equiv
      (ComplexRaw.mul z (ComplexRaw.mul w v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hwv := QBox.mul_contains hy.1 hy.2 hu.1 hu.2
  have hleft := QBox.mul_contains hzw.1 hzw.2 hu.1 hu.2
  have hright := QBox.mul_contains hx.1 hx.2 hwv.1 hwv.2
  have hassoc : QComplex.mul (QComplex.mul x y) u =
      QComplex.mul x (QComplex.mul y u) := by
    exact QComplex.mul_assoc_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.mul z w) v)
    (ComplexRaw.mul z (ComplexRaw.mul w v)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.mul A B) C)
    (QBox.mul A (QBox.mul B C))
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hre := congrArg QComplex.re hassoc
  have him := congrArg QComplex.im hassoc
  have hrightReLo : (QBox.mul A (QBox.mul B C)).lo.re <=
      (QComplex.mul (QComplex.mul x y) u).re := by
    rw [hre]
    exact hright.1.1
  have hrightReHi : (QComplex.mul (QComplex.mul x y) u).re <=
      (QBox.mul A (QBox.mul B C)).hi.re := by
    rw [hre]
    exact hright.2.1
  have hleftReHi : (QComplex.mul (QComplex.mul x y) u).re <=
      (QBox.mul (QBox.mul A B) C).hi.re := by
    exact hleft.2.1
  have hrightImLo : (QBox.mul A (QBox.mul B C)).lo.im <=
      (QComplex.mul (QComplex.mul x y) u).im := by
    rw [him]
    exact hright.1.2
  have hrightImHi : (QComplex.mul (QComplex.mul x y) u).im <=
      (QBox.mul A (QBox.mul B C)).hi.im := by
    rw [him]
    exact hright.2.2
  have hleftImHi : (QComplex.mul (QComplex.mul x y) u).im <=
      (QBox.mul (QBox.mul A B) C).hi.im := by
    exact hleft.2.2
  exact ⟨⟨Rat.le_trans hleft.1.1 hrightReHi,
    Rat.le_trans hleft.1.2 hrightImHi⟩,
    ⟨Rat.le_trans hrightReLo hleftReHi,
      Rat.le_trans hrightImLo hleftImHi⟩⟩

theorem QBox.overlaps_of_common_point {A B : QBox} {z : QComplex}
    (hA : A.lo <= z /\ z <= A.hi)
    (hB : B.lo <= z /\ z <= B.hi) :
    A.Overlaps B := by
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  exact ⟨⟨Rat.le_trans hA.1.1 hB.2.1,
    Rat.le_trans hA.1.2 hB.2.2⟩,
    ⟨Rat.le_trans hB.1.1 hA.2.1,
      Rat.le_trans hB.1.2 hA.2.2⟩⟩

theorem QBox.neg_contains {A : QBox} {z : QComplex}
    (hA : A.lo <= z /\ z <= A.hi) :
    (QBox.neg A).lo <= QComplex.neg z /\
      QComplex.neg z <= (QBox.neg A).hi := by
  unfold QBox.neg QComplex.neg
  simp only [QComplex.le_def]
  exact ⟨⟨Rat.neg_le_neg hA.2.1, Rat.neg_le_neg hA.2.2⟩,
    ⟨Rat.neg_le_neg hA.1.1, Rat.neg_le_neg hA.1.2⟩⟩

theorem effectiveComplexRaw_mul_neg_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul z (ComplexRaw.neg w)).Equiv
      (ComplexRaw.neg (ComplexRaw.mul z w)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let x := A.center
  let y := B.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hny := QBox.neg_contains hy
  have hleft := QBox.mul_contains hx.1 hx.2 hny.1 hny.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hright := QBox.neg_contains hzw
  have hidentity : QComplex.mul x (QComplex.neg y) =
      QComplex.neg (QComplex.mul x y) := by
    exact QComplex.mul_neg_cert x y
  have hright' : (QBox.neg (QBox.mul A B)).lo <=
      QComplex.mul x (QComplex.neg y) /\
      QComplex.mul x (QComplex.neg y) <=
        (QBox.neg (QBox.mul A B)).hi := by
    rw [hidentity]
    exact hright
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z (ComplexRaw.neg w))
    (ComplexRaw.neg (ComplexRaw.mul z w)) n n).2
  change QBox.Overlaps
    (QBox.mul A (QBox.neg B))
    (QBox.neg (QBox.mul A B))
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_neg_mul_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul (ComplexRaw.neg z) w).Equiv
      (ComplexRaw.neg (ComplexRaw.mul z w)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let x := A.center
  let y := B.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hnx := QBox.neg_contains hx
  have hleft := QBox.mul_contains hnx.1 hnx.2 hy.1 hy.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hright := QBox.neg_contains hzw
  have hidentity : QComplex.mul (QComplex.neg x) y =
      QComplex.neg (QComplex.mul x y) := by
    exact QComplex.neg_mul_cert x y
  have hright' : (QBox.neg (QBox.mul A B)).lo <=
      QComplex.mul (QComplex.neg x) y /\
      QComplex.mul (QComplex.neg x) y <=
        (QBox.neg (QBox.mul A B)).hi := by
    rw [hidentity]
    exact hright
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.neg z) w)
    (ComplexRaw.neg (ComplexRaw.mul z w)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.neg A) B)
    (QBox.neg (QBox.mul A B))
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_mul_add_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul z (ComplexRaw.add w v)).Equiv
      (ComplexRaw.add (ComplexRaw.mul z w) (ComplexRaw.mul z v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hyu := QBox.add_contains hy.1 hy.2 hu.1 hu.2
  have hleft := QBox.mul_contains hx.1 hx.2 hyu.1 hyu.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hzv := QBox.mul_contains hx.1 hx.2 hu.1 hu.2
  have hright := QBox.add_contains hzw.1 hzw.2 hzv.1 hzv.2
  have hidentity : QComplex.mul x (QComplex.add y u) =
      QComplex.add (QComplex.mul x y) (QComplex.mul x u) := by
    exact QComplex.mul_add_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z (ComplexRaw.add w v))
    (ComplexRaw.add (ComplexRaw.mul z w) (ComplexRaw.mul z v)) n n).2
  change QBox.Overlaps
    (QBox.mul A (QBox.add B C))
    (QBox.add (QBox.mul A B) (QBox.mul A C))
  have hright' : (QBox.add (QBox.mul A B) (QBox.mul A C)).lo <=
      QComplex.mul x (QComplex.add y u) /\
      QComplex.mul x (QComplex.add y u) <=
        (QBox.add (QBox.mul A B) (QBox.mul A C)).hi := by
    rw [hidentity]
    exact hright
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_add_mul_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul (ComplexRaw.add z w) v).Equiv
      (ComplexRaw.add (ComplexRaw.mul z v) (ComplexRaw.mul w v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hxy := QBox.add_contains hx.1 hx.2 hy.1 hy.2
  have hleft := QBox.mul_contains hxy.1 hxy.2 hu.1 hu.2
  have hzv := QBox.mul_contains hx.1 hx.2 hu.1 hu.2
  have hwv := QBox.mul_contains hy.1 hy.2 hu.1 hu.2
  have hright := QBox.add_contains hzv.1 hzv.2 hwv.1 hwv.2
  have hidentity : QComplex.mul (QComplex.add x y) u =
      QComplex.add (QComplex.mul x u) (QComplex.mul y u) := by
    exact QComplex.add_mul_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.add z w) v)
    (ComplexRaw.add (ComplexRaw.mul z v) (ComplexRaw.mul w v)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.add A B) C)
    (QBox.add (QBox.mul A C) (QBox.mul B C))
  have hright' : (QBox.add (QBox.mul A C) (QBox.mul B C)).lo <=
      QComplex.mul (QComplex.add x y) u /\
      QComplex.mul (QComplex.add x y) u <=
        (QBox.add (QBox.mul A C) (QBox.mul B C)).hi := by
    rw [hidentity]
    exact hright
  exact QBox.overlaps_of_common_point hleft hright'

/-! Negation is the interval-reversing operation needed to assemble signed
linear combinations from the order-preserving nonnegative scaling primitive. -/
theorem effectiveComplexRaw_neg_equiv
    {z w : ComplexRaw}
    (hzw : z.Equiv w) :
    (ComplexRaw.neg z).Equiv (ComplexRaw.neg w) := by
  intro n
  have hover := (ComplexRaw.compareAt_overlap_iff z w n n).1 (hzw n)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.neg z) (ComplexRaw.neg w) n n).2
  change QBox.Overlaps
    { lo := { re := -(z.compute n).hi.re, im := -(z.compute n).hi.im },
      hi := { re := -(z.compute n).lo.re, im := -(z.compute n).lo.im } }
    { lo := { re := -(w.compute n).hi.re, im := -(w.compute n).hi.im },
      hi := { re := -(w.compute n).lo.re, im := -(w.compute n).lo.im } }
  unfold QBox.Overlaps at hover ⊢
  simp only [QComplex.le_def] at hover ⊢
  constructor <;> constructor <;> grind [Rat.neg_le_neg]

def FunctionRaw.add (f g : FunctionRaw) : FunctionRaw where
  domain := fun z => f.domain z /\ g.domain z
  compute := fun z hz n =>
    QBox.add (f.compute z hz.1 n) (g.compute z hz.2 n)

theorem FunctionRaw.add_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.add f g).Valid := by
  intro z hz
  have hadd : (ComplexRaw.add (f.evalRaw z hz.1)
      (g.evalRaw z hz.2)).Valid :=
    ComplexRaw.add_valid (hf z hz.1) (hg z hz.2)
  change (ComplexRaw.add (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid at hadd
  change (ComplexRaw.add (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid
  exact hadd

theorem FunctionRaw.add_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.add f g).AgreeOnCommonDomain
      (FunctionRaw.add f' g') := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (f'.evalRaw z hright.1)
      (g'.evalRaw z hright.2))
  exact effectiveComplexRaw_add_equiv
    (hf z hleft.1) (hf' z hright.1)
    (hg z hleft.2) (hg' z hright.2)
    (hff z hleft.1 hright.1)
    (hgg z hleft.2 hright.2)

theorem FunctionRaw.zero_add_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.add FunctionRaw.zero f).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.add
    (FunctionRaw.zero.evalRaw z hleft.1)
    (f.evalRaw z hleft.2)).Equiv (f.evalRaw z hright)
  exact effectiveComplexRaw_zero_add_equiv (hf z hright)

theorem FunctionRaw.add_zero_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.add f FunctionRaw.zero).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.add
    (f.evalRaw z hleft.1)
    (FunctionRaw.zero.evalRaw z hleft.2)).Equiv (f.evalRaw z hright)
  exact effectiveComplexRaw_add_zero_equiv (hf z hright)

theorem FunctionRaw.add_comm_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.add f g).AgreeOnCommonDomain
      (FunctionRaw.add g f) := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (g.evalRaw z hright.1)
      (f.evalRaw z hright.2))
  exact effectiveComplexRaw_add_comm_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.add_assoc_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.add (FunctionRaw.add f g) h).AgreeOnCommonDomain
      (FunctionRaw.add f (FunctionRaw.add g h)) := by
  intro z hleft hright
  change (ComplexRaw.add
      (ComplexRaw.add (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (f.evalRaw z hright.1)
      (ComplexRaw.add (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_add_assoc_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

def FunctionRaw.sum : List FunctionRaw → FunctionRaw
  | [] => FunctionRaw.zero
  | f :: fs => FunctionRaw.add f (FunctionRaw.sum fs)

theorem FunctionRaw.sum_valid
    (fs : List FunctionRaw)
    (hfs : ∀ f, f ∈ fs → f.Valid) :
    (FunctionRaw.sum fs).Valid := by
  induction fs with
  | nil => exact FunctionRaw.zero_valid
  | cons f fs ih =>
    exact FunctionRaw.add_valid (hfs f (by simp))
      (ih (fun g hg => hfs g (by simp [hg])))

theorem FunctionRaw.zero_agreeOnCommonDomain :
    FunctionRaw.zero.AgreeOnCommonDomain FunctionRaw.zero := by
  intro z _ _
  exact ComplexRaw.equiv_refl ComplexRaw.zero
    (ComplexRaw.ofQComplex_valid QComplex.zero)

def FunctionRaw.AgreeList : List FunctionRaw → List FunctionRaw → Prop
  | [], [] => True
  | f :: fs, g :: gs =>
      f.AgreeOnCommonDomain g ∧ FunctionRaw.AgreeList fs gs
  | _, _ => False

theorem FunctionRaw.sum_agreeOnCommonDomain
    {fs gs : List FunctionRaw}
    (hfs : ∀ f, f ∈ fs → f.Valid)
    (hgs : ∀ g, g ∈ gs → g.Valid)
    (hpair : FunctionRaw.AgreeList fs gs) :
    (FunctionRaw.sum fs).AgreeOnCommonDomain
      (FunctionRaw.sum gs) := by
  induction fs generalizing gs with
  | nil =>
    cases gs with
    | nil => exact FunctionRaw.zero_agreeOnCommonDomain
    | cons g gs => simp [FunctionRaw.AgreeList] at hpair
  | cons f fs ih =>
    cases gs with
    | nil => simp [FunctionRaw.AgreeList] at hpair
    | cons g gs =>
      rcases hpair with ⟨hfg, htail⟩
      exact FunctionRaw.add_agreeOnCommonDomain
        (hfs f (by simp))
        (hgs g (by simp))
        (FunctionRaw.sum_valid fs (fun x hx => hfs x (by simp [hx])))
        (FunctionRaw.sum_valid gs (fun x hx => hgs x (by simp [hx])))
        hfg
        (ih
          (fun x hx => hfs x (by simp [hx]))
            (fun x hx => hgs x (by simp [hx]))
            htail)

def FunctionRaw.neg (f : FunctionRaw) : FunctionRaw where
  domain := f.domain
  compute := fun z hz n => QBox.neg (f.compute z hz n)

theorem FunctionRaw.neg_valid
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.neg f).Valid := by
  intro z hz
  have hneg : (ComplexRaw.neg (f.evalRaw z hz)).Valid :=
    ComplexRaw.neg_valid (hf z hz)
  change (ComplexRaw.neg (f.evalRaw z hz)).Valid at hneg
  change (ComplexRaw.neg (f.evalRaw z hz)).Valid
  exact hneg

theorem FunctionRaw.neg_agreeOnCommonDomain
    {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.neg f).AgreeOnCommonDomain (FunctionRaw.neg g) := by
  intro z hfz hgz
  change (ComplexRaw.neg (f.evalRaw z hfz)).Equiv
    (ComplexRaw.neg (g.evalRaw z hgz))
  exact effectiveComplexRaw_neg_equiv (hfg z hfz hgz)

/-! Nonnegative rational scaling is the order-preserving scalar operation on
complex raw functions.  Negative scaling is intentionally assembled from
negation plus this primitive, so interval reversal stays explicit. -/
def FunctionRaw.scaleRat (r : Rat) (f : FunctionRaw) : FunctionRaw where
  domain := f.domain
  compute := fun z hz n => QBox.scaleRat r (f.compute z hz n)

theorem FunctionRaw.scaleRat_add_agreeOnCommonDomain_of_nonneg
    {r : Rat} (hr : 0 <= r) {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.scaleRat r (FunctionRaw.add f g)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.scaleRat r f)
        (FunctionRaw.scaleRat r g)) := by
  intro z hleft hright
  change (ComplexRaw.scaleRat r
      (ComplexRaw.add (f.evalRaw z hleft.1)
        (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.scaleRat r (f.evalRaw z hright.1))
      (ComplexRaw.scaleRat r (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_scaleRat_add_equiv_of_nonneg r hr
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.scaleRat_add_agreeOnCommonDomain
    {r : Rat} {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.scaleRat r (FunctionRaw.add f g)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.scaleRat r f)
        (FunctionRaw.scaleRat r g)) := by
  intro z hleft hright
  change (ComplexRaw.scaleRat r
      (ComplexRaw.add (f.evalRaw z hleft.1)
        (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.scaleRat r (f.evalRaw z hright.1))
      (ComplexRaw.scaleRat r (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_scaleRat_add_equiv r
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.scaleRat_valid_of_nonneg
    {r : Rat} (hr : 0 <= r) {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.scaleRat r f).Valid := by
  intro z hz
  have hscaled : (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid :=
    ComplexRaw.scaleRat_valid_of_nonneg hr (hf z hz)
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid at hscaled
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid
  exact hscaled

theorem FunctionRaw.scaleRat_agreeOnCommonDomain_of_nonneg
    {r : Rat} (hr : 0 <= r)
    {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.scaleRat r f).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r g) := by
  intro z hfz hgz
  change (ComplexRaw.scaleRat r (f.evalRaw z hfz)).Equiv
    (ComplexRaw.scaleRat r (g.evalRaw z hgz))
  exact ComplexRaw.scaleRat_equiv_of_nonneg hr
    (hfg z hfz hgz)

private theorem effectiveComplexRaw_scaleRat_neg_eq
    {r : Rat} (hr : r < 0) (z : ComplexRaw) :
    ∀ n, (ComplexRaw.scaleRat r z).compute n =
      (ComplexRaw.neg (ComplexRaw.scaleRat (-r) z)).compute n := by
  cases z with
  | mk compute rate =>
    intro n
    have hrnot : ¬ 0 <= r := by grind
    have hrpos : 0 <= -r := by grind
    simp only [ComplexRaw.scaleRat, ComplexRaw.neg, QBox.scaleRat,
      if_neg hrnot, if_pos hrpos]
    congr 1 <;> simp [Rat.neg_mul]

theorem effectiveComplexRaw_scaleRat_valid
    {r : Rat} {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.scaleRat r z).Valid := by
  by_cases hr : 0 <= r
  · exact ComplexRaw.scaleRat_valid_of_nonneg hr hz
  · have hrlt : r < 0 := by grind
    have hrnonneg : 0 <= -r := by grind
    have hcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt z
    have hneg : (ComplexRaw.neg (ComplexRaw.scaleRat (-r) z)).Valid :=
      ComplexRaw.neg_valid
        (ComplexRaw.scaleRat_valid_of_nonneg hrnonneg hz)
    change ComplexRaw.ValidCompute (ComplexRaw.scaleRat r z).compute
    rw [funext hcompute]
    exact hneg

theorem effectiveComplexRaw_scaleRat_equiv
    {r : Rat} {z w : ComplexRaw} (hzw : z.Equiv w) :
    (ComplexRaw.scaleRat r z).Equiv (ComplexRaw.scaleRat r w) := by
  by_cases hr : 0 <= r
  · exact ComplexRaw.scaleRat_equiv_of_nonneg hr hzw
  · have hrlt : r < 0 := by grind
    have hrnonneg : 0 <= -r := by grind
    have hzcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt z
    have hwcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt w
    intro n
    have hneg := effectiveComplexRaw_neg_equiv
      (ComplexRaw.scaleRat_equiv_of_nonneg hrnonneg hzw) n
    change ComplexRaw.compareBoxes
      ((ComplexRaw.scaleRat r z).compute n)
      ((ComplexRaw.scaleRat r w).compute n) =
      ComplexRaw.CompareAt.overlap
    rw [hzcompute n, hwcompute n]
    exact hneg

theorem FunctionRaw.scaleRat_valid
    {r : Rat} {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.scaleRat r f).Valid := by
  intro z hz
  have hscaled : (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid :=
    effectiveComplexRaw_scaleRat_valid (hf z hz)
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid at hscaled
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid
  exact hscaled

theorem FunctionRaw.scaleRat_agreeOnCommonDomain
    {r : Rat} {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.scaleRat r f).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r g) := by
  intro z hfz hgz
  change (ComplexRaw.scaleRat r (f.evalRaw z hfz)).Equiv
    (ComplexRaw.scaleRat r (g.evalRaw z hgz))
  exact effectiveComplexRaw_scaleRat_equiv (hfg z hfz hgz)

def FunctionRaw.linearCombination : List (Rat × FunctionRaw) → FunctionRaw :=
  fun terms =>
    FunctionRaw.sum
      (terms.map (fun term => FunctionRaw.scaleRat term.1 term.2))

theorem FunctionRaw.linearCombination_valid
    (terms : List (Rat × FunctionRaw))
    (hterms : ∀ term, term ∈ terms → term.2.Valid) :
    (FunctionRaw.linearCombination terms).Valid := by
  apply FunctionRaw.sum_valid
  intro f hf
  obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hf
  exact FunctionRaw.scaleRat_valid (hterms term hterm)

/-! Subtraction is assembled from the already certified addition and
negation operations.  No separate interval-arithmetic theorem is needed. -/
def FunctionRaw.sub (f g : FunctionRaw) : FunctionRaw :=
  FunctionRaw.add f (FunctionRaw.neg g)

theorem FunctionRaw.sub_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.sub f g).Valid := by
  exact FunctionRaw.add_valid hf (FunctionRaw.neg_valid hg)

theorem FunctionRaw.sub_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.sub f g).AgreeOnCommonDomain
      (FunctionRaw.sub f' g') := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (ComplexRaw.neg (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add (f'.evalRaw z hright.1)
      (ComplexRaw.neg (g'.evalRaw z hright.2)))
  exact effectiveComplexRaw_add_equiv
    (hf z hleft.1) (hf' z hright.1)
    (ComplexRaw.neg_valid (hg z hleft.2))
    (ComplexRaw.neg_valid (hg' z hright.2))
    (hff z hleft.1 hright.1)
    (effectiveComplexRaw_neg_equiv (hgg z hleft.2 hright.2))

/-! The abstract function handle exposes the same certified operations as its
preferred raw representative.  Alternative evaluators remain explicit data
which can be attached with `ComplexFunction.withAlternative`. -/
def ComplexFunction.zero : ComplexFunction :=
  ComplexFunction.ofRaw FunctionRaw.zero FunctionRaw.zero_valid

def ComplexFunction.one : ComplexFunction :=
  ComplexFunction.ofRaw FunctionRaw.one FunctionRaw.one_valid

def ComplexFunction.add (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.add f.preferred g.preferred)
    (FunctionRaw.add_valid f.valid g.valid)

theorem ComplexFunction.zero_add_representation_agrees_preferred
    (f : ComplexFunction) :
    (ComplexFunction.add ComplexFunction.zero f).preferred.AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.add FunctionRaw.zero f.preferred).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.zero_add_agreeOnCommonDomain f.valid

theorem ComplexFunction.add_zero_representation_agrees_preferred
    (f : ComplexFunction) :
    (ComplexFunction.add f ComplexFunction.zero).preferred.AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.add f.preferred FunctionRaw.zero).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.add_zero_agreeOnCommonDomain f.valid

theorem ComplexFunction.add_comm_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.add f g).preferred.AgreeOnCommonDomain
      (ComplexFunction.add g f).preferred := by
  change (FunctionRaw.add f.preferred g.preferred).AgreeOnCommonDomain
    (FunctionRaw.add g.preferred f.preferred)
  exact FunctionRaw.add_comm_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.add_assoc_representation_agrees_preferred
    (f g h : ComplexFunction) :
    ((ComplexFunction.add (ComplexFunction.add f g) h).preferred).AgreeOnCommonDomain
      (ComplexFunction.add f (ComplexFunction.add g h)).preferred := by
  change (FunctionRaw.add (FunctionRaw.add f.preferred g.preferred)
      h.preferred).AgreeOnCommonDomain
    (FunctionRaw.add f.preferred (FunctionRaw.add g.preferred h.preferred))
  exact FunctionRaw.add_assoc_agreeOnCommonDomain f.valid g.valid h.valid

def ComplexFunction.neg (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.neg f.preferred)
    (FunctionRaw.neg_valid f.valid)

def ComplexFunction.scaleRat (r : Rat) (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.scaleRat r f.preferred)
    (FunctionRaw.scaleRat_valid f.valid)

theorem ComplexFunction.scaleRat_add_representation_agrees_preferred_of_nonneg
    (r : Rat) (hr : 0 <= r) (f g : ComplexFunction) :
    ((ComplexFunction.scaleRat r (ComplexFunction.add f g)).preferred).AgreeOnCommonDomain
      ((ComplexFunction.add (ComplexFunction.scaleRat r f)
        (ComplexFunction.scaleRat r g)).preferred) := by
  change (FunctionRaw.scaleRat r (FunctionRaw.add f.preferred g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.scaleRat r f.preferred)
      (FunctionRaw.scaleRat r g.preferred))
  exact FunctionRaw.scaleRat_add_agreeOnCommonDomain_of_nonneg hr
    f.valid g.valid

theorem ComplexFunction.scaleRat_add_representation_agrees_preferred
    (r : Rat) (f g : ComplexFunction) :
    ((ComplexFunction.scaleRat r (ComplexFunction.add f g)).preferred).AgreeOnCommonDomain
      ((ComplexFunction.add (ComplexFunction.scaleRat r f)
        (ComplexFunction.scaleRat r g)).preferred) := by
  change (FunctionRaw.scaleRat r (FunctionRaw.add f.preferred g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.scaleRat r f.preferred)
      (FunctionRaw.scaleRat r g.preferred))
  exact FunctionRaw.scaleRat_add_agreeOnCommonDomain f.valid g.valid

def ComplexFunction.sub (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.sub f.preferred g.preferred)
    (FunctionRaw.sub_valid f.valid g.valid)

def ComplexFunction.sum (fs : List ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.sum (fs.map (fun f => f.preferred)))
    (FunctionRaw.sum_valid _ (by
      intro raw hraw
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hraw
      exact f.valid))

theorem ComplexFunction.sum_representation_agrees_preferred
    {fs : List ComplexFunction} {alternatives : List FunctionRaw}
    (halt : ∀ raw, raw ∈ alternatives → raw.Valid)
    (hpair : FunctionRaw.AgreeList alternatives
      (fs.map (fun f => f.preferred))) :
    (FunctionRaw.sum alternatives).AgreeOnCommonDomain
      (FunctionRaw.sum (fs.map (fun f => f.preferred))) := by
  apply FunctionRaw.sum_agreeOnCommonDomain
  · exact halt
  · intro raw hraw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hraw
    exact f.valid
  · exact hpair

def ComplexFunction.linearCombination
    (terms : List (Rat × ComplexFunction)) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.linearCombination
      (terms.map (fun term => (term.1, term.2.preferred))))
    (FunctionRaw.linearCombination_valid _ (by
      intro term hterm
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hterm
      exact original.2.valid))

theorem ComplexFunction.linearCombination_representation_agrees_preferred
    {terms : List (Rat × ComplexFunction)}
    {alternatives : List (Rat × FunctionRaw)}
    (halt : ∀ term, term ∈ alternatives → term.2.Valid)
    (hpair : FunctionRaw.AgreeList
      (alternatives.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2))
      (terms.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2.preferred))) :
    (FunctionRaw.linearCombination alternatives).AgreeOnCommonDomain
      (FunctionRaw.linearCombination
        (terms.map (fun term => (term.1, term.2.preferred)))) := by
  have hsum :
      (FunctionRaw.sum
        (alternatives.map (fun term =>
          FunctionRaw.scaleRat term.1 term.2))).AgreeOnCommonDomain
        (FunctionRaw.sum
          (terms.map (fun term =>
            FunctionRaw.scaleRat term.1 term.2.preferred))) := by
    apply FunctionRaw.sum_agreeOnCommonDomain
    · intro raw hraw
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hraw
      exact FunctionRaw.scaleRat_valid (halt term hterm)
    · intro raw hraw
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hraw
      exact FunctionRaw.scaleRat_valid term.2.valid
    · exact hpair
  have hmap :
      (terms.map (fun term => (term.1, term.2.preferred))).map
          (fun term => FunctionRaw.scaleRat term.1 term.2) =
        terms.map (fun term =>
          FunctionRaw.scaleRat term.1 term.2.preferred) := by
    simp [List.map_map]
  unfold FunctionRaw.linearCombination
  rw [hmap]
  exact hsum

def ComplexFunction.linearCombination_withAlternative
    {terms : List (Rat × ComplexFunction)}
    {alternatives : List (Rat × FunctionRaw)}
    (halt : ∀ term, term ∈ alternatives → term.2.Valid)
    (hpair : FunctionRaw.AgreeList
      (alternatives.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2))
      (terms.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2.preferred))) : ComplexFunction :=
  ComplexFunction.withAlternative
    (ComplexFunction.linearCombination terms)
    (FunctionRaw.linearCombination alternatives)
    (FunctionRaw.linearCombination_valid alternatives halt)
    (FunctionRaw.agreeOnCommonDomain_symm
      (ComplexFunction.linearCombination_representation_agrees_preferred
        halt hpair))

theorem ComplexFunction.add_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.add rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.add f.preferred g.preferred) := by
  exact FunctionRaw.add_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

theorem ComplexFunction.neg_representation_agrees_preferred
    {f : ComplexFunction} (rf : ComplexFunction.Representation f) :
    (FunctionRaw.neg rf.raw).AgreeOnCommonDomain
      (FunctionRaw.neg f.preferred) := by
  exact FunctionRaw.neg_agreeOnCommonDomain rf.agrees

theorem ComplexFunction.scaleRat_representation_agrees_preferred
    {r : Rat} {f : ComplexFunction}
    (rf : ComplexFunction.Representation f) :
    (FunctionRaw.scaleRat r rf.raw).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r f.preferred) := by
  exact FunctionRaw.scaleRat_agreeOnCommonDomain rf.agrees

theorem ComplexFunction.sub_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.sub rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.sub f.preferred g.preferred) := by
  exact FunctionRaw.sub_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

/-! Function-level representation equivalence records the same domain and a
pointwise raw-real equivalence.  This is the lightweight bridge needed when a
later proof switches between two certified implementations of one function. -/
def RealFunRaw.EquivOn (f g : RealFunRaw) : Prop :=
  f.domain = g.domain /\
    ∀ x, f.domain x ->
      ({ compute := f.compute x } : RealRaw).Equiv
        ({ compute := g.compute x } : RealRaw)

theorem RealFunRaw.equivOn_refl (f : RealFunRaw) (hf : f.Valid) :
    f.EquivOn f := by
  constructor
  · rfl
  · intro x hx
    exact RealRaw.equiv_refl { compute := f.compute x } (hf x hx)

theorem RealFunRaw.equivOn_symm {f g : RealFunRaw}
    (hfg : f.EquivOn g) : g.EquivOn f := by
  constructor
  · exact hfg.1.symm
  · intro x hx
    exact RealRaw.equiv_symm (hfg.2 x (hfg.1.symm ▸ hx))

theorem RealFunRaw.equivOn_trans {f g h : RealFunRaw}
    (hf : f.Valid) (hg : g.Valid) (hh : h.Valid)
    (hfg : f.EquivOn g) (hgh : g.EquivOn h) :
    f.EquivOn h := by
  constructor
  · exact hfg.1.trans hgh.1
  · intro x hx
    let F : RealRaw := { compute := f.compute x }
    let G : RealRaw := { compute := g.compute x }
    let H : RealRaw := { compute := h.compute x }
    have hF : F.Valid := by
      simpa [F, RealRaw.Valid, RealFunRaw.applyCompute] using hf x hx
    have hG : G.Valid := by
      simpa [G, RealRaw.Valid, RealFunRaw.applyCompute] using
        hg x (hfg.1 ▸ hx)
    have hH : H.Valid := by
      simpa [H, RealRaw.Valid, RealFunRaw.applyCompute] using
        hh x (hgh.1 ▸ (hfg.1 ▸ hx))
    exact RealRaw.equiv_trans hF hG hH
      (hfg.2 x hx) (hgh.2 x (hfg.1 ▸ hx))

theorem effectiveRealFunRaw_mul_equivOn
    {f f' g g' : RealFunRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.EquivOn f') (hgg : g.EquivOn g') :
    (RealFunRaw.mul f g).EquivOn (RealFunRaw.mul f' g') := by
  constructor
  · funext x
    simp only [RealFunRaw.mul]
    rw [hff.1, hgg.1]
  · intro x hx
    have hfx : f.domain x := hx.1
    have hgx : g.domain x := hx.2
    let X : RealRaw := { compute := f.compute x }
    let X' : RealRaw := { compute := f'.compute x }
    let Y : RealRaw := { compute := g.compute x }
    let Y' : RealRaw := { compute := g'.compute x }
    have hX : X.Valid := by
      simpa [X, RealRaw.Valid, RealFunRaw.applyCompute] using hf x hfx
    have hX' : X'.Valid := by
      simpa [X', RealRaw.Valid, RealFunRaw.applyCompute] using hf' x (hff.1 ▸ hfx)
    have hY : Y.Valid := by
      simpa [Y, RealRaw.Valid, RealFunRaw.applyCompute] using hg x hgx
    have hY' : Y'.Valid := by
      simpa [Y', RealRaw.Valid, RealFunRaw.applyCompute] using hg' x (hgg.1 ▸ hgx)
    change (X * Y).Equiv (X' * Y')
    exact RealRaw.mul_equiv hX hX' hY hY'
      (hff.2 x hfx) (hgg.2 x hgx)

/-! Complex-valued raw functions have the same constructive product closure.
The domain is the intersection of the two input domains, and the output box
is the rational four-corner product of the two certified complex boxes. -/
def FunctionRaw.mul (f g : FunctionRaw) : FunctionRaw where
  domain := fun z => f.domain z /\ g.domain z
  compute := fun z hz n =>
    QBox.mul (f.compute z hz.1 n) (g.compute z hz.2 n)

theorem FunctionRaw.mul_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f g).Valid := by
  intro z hz
  have hproduct : (ComplexRaw.mul (f.evalRaw z hz.1)
      (g.evalRaw z hz.2)).Valid :=
    ComplexRaw.mul_valid (hf z hz.1) (hg z hz.2)
  change (ComplexRaw.mul (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid at hproduct
  change (ComplexRaw.mul (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid
  exact hproduct

theorem FunctionRaw.mul_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.mul f g).AgreeOnCommonDomain
      (FunctionRaw.mul f' g') := by
  intro z hleft hright
  let F := f.evalRaw z hleft.1
  let F' := f'.evalRaw z hright.1
  let G := g.evalRaw z hleft.2
  let G' := g'.evalRaw z hright.2
  change (ComplexRaw.mul F G).Equiv (ComplexRaw.mul F' G')
  exact ComplexRaw.mul_equiv
    (hf z hleft.1) (hf' z hright.1)
    (hg z hleft.2) (hg' z hright.2)
    (hff z hleft.1 hright.1)
    (hgg z hleft.2 hright.2)

theorem FunctionRaw.mul_one_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul f FunctionRaw.one).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (FunctionRaw.one.evalRaw z hleft.2)).Equiv
    (f.evalRaw z hright)
  exact effectiveComplexRaw_mul_one_equiv (hf z hleft.1)

theorem FunctionRaw.one_mul_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul FunctionRaw.one f).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.mul (FunctionRaw.one.evalRaw z hleft.1)
      (f.evalRaw z hleft.2)).Equiv
    (f.evalRaw z hright)
  exact effectiveComplexRaw_one_mul_equiv (hf z hleft.2)

theorem FunctionRaw.mul_zero_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul f FunctionRaw.zero).AgreeOnCommonDomain
      FunctionRaw.zero := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (FunctionRaw.zero.evalRaw z hleft.2)).Equiv
    (FunctionRaw.zero.evalRaw z hright)
  exact effectiveComplexRaw_mul_zero_equiv (hf z hleft.1)

theorem FunctionRaw.zero_mul_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul FunctionRaw.zero f).AgreeOnCommonDomain
      FunctionRaw.zero := by
  intro z hleft hright
  change (ComplexRaw.mul (FunctionRaw.zero.evalRaw z hleft.1)
      (f.evalRaw z hleft.2)).Equiv
    (FunctionRaw.zero.evalRaw z hright)
  exact effectiveComplexRaw_zero_mul_equiv (hf z hleft.2)

theorem FunctionRaw.mul_comm_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f g).AgreeOnCommonDomain
      (FunctionRaw.mul g f) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.mul (g.evalRaw z hright.1)
      (f.evalRaw z hright.2))
  exact effectiveComplexRaw_mul_comm_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.mul_assoc_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul (FunctionRaw.mul f g) h).AgreeOnCommonDomain
      (FunctionRaw.mul f (FunctionRaw.mul g h)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.mul (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.mul (f.evalRaw z hright.1)
      (ComplexRaw.mul (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_mul_assoc_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

def FunctionRaw.pow (f : FunctionRaw) : Nat -> FunctionRaw
  | 0 => FunctionRaw.one
  | n + 1 => FunctionRaw.mul (FunctionRaw.pow f n) f

theorem FunctionRaw.pow_valid {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.pow f n).Valid := by
  induction n with
  | zero => exact FunctionRaw.one_valid
  | succ n ih => exact FunctionRaw.mul_valid ih hf

theorem FunctionRaw.one_agreeOnCommonDomain :
    FunctionRaw.one.AgreeOnCommonDomain FunctionRaw.one := by
  intro z hleft hright
  exact ComplexRaw.equiv_refl
    (FunctionRaw.one.evalRaw z hleft)
    (FunctionRaw.one_valid z hleft)

theorem FunctionRaw.pow_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid)
    (hfg : f.AgreeOnCommonDomain g) (n : Nat) :
    (FunctionRaw.pow f n).AgreeOnCommonDomain
      (FunctionRaw.pow g n) := by
  induction n with
  | zero => exact FunctionRaw.one_agreeOnCommonDomain
  | succ n ih =>
    exact FunctionRaw.mul_agreeOnCommonDomain
      (FunctionRaw.pow_valid hf) (FunctionRaw.pow_valid hg) hf hg ih hfg

theorem FunctionRaw.mul_add_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul f (FunctionRaw.add g h)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.mul f g) (FunctionRaw.mul f h)) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (ComplexRaw.add (g.evalRaw z hleft.2.1)
        (h.evalRaw z hleft.2.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.mul (f.evalRaw z hright.1.1)
        (g.evalRaw z hright.1.2))
      (ComplexRaw.mul (f.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_mul_add_equiv
    (hf z hleft.1) (hg z hleft.2.1) (hh z hleft.2.2)

theorem FunctionRaw.add_mul_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul (FunctionRaw.add f g) h).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.mul f h) (FunctionRaw.mul g h)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.add (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add
      (ComplexRaw.mul (f.evalRaw z hright.1.1)
        (h.evalRaw z hright.1.2))
      (ComplexRaw.mul (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_add_mul_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

theorem FunctionRaw.mul_neg_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f (FunctionRaw.neg g)).AgreeOnCommonDomain
      (FunctionRaw.neg (FunctionRaw.mul f g)) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (ComplexRaw.neg (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.neg (ComplexRaw.mul (f.evalRaw z hright.1)
      (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_mul_neg_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.neg_mul_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul (FunctionRaw.neg f) g).AgreeOnCommonDomain
      (FunctionRaw.neg (FunctionRaw.mul f g)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.neg (f.evalRaw z hleft.1))
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.neg (ComplexRaw.mul (f.evalRaw z hright.1)
      (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_neg_mul_equiv
    (hf z hleft.1) (hg z hleft.2)

def FunctionRaw.polynomial (coeffs : List QComplex) (f : FunctionRaw) : FunctionRaw :=
  coeffs.foldr
    (fun c acc => FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f acc))
    FunctionRaw.zero

theorem FunctionRaw.polynomial_compute
    (coeffs : List QComplex) {f : FunctionRaw} {z : QComplex}
    (hz : f.domain z) (n : Nat)
    (h : (FunctionRaw.polynomial coeffs f).domain z) :
    (FunctionRaw.polynomial coeffs f).compute z h n =
      QBox.evalPoly coeffs (f.compute z hz n) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).compute z h n =
      QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n) (QBox.evalPoly cs (f.compute z hz n)))
    change QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n)
          ((FunctionRaw.polynomial cs f).compute z _ n)) =
      QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n) (QBox.evalPoly cs (f.compute z hz n)))
    rw [ih]

theorem FunctionRaw.polynomial_valid
    (coeffs : List QComplex) {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.polynomial coeffs f).Valid := by
  induction coeffs with
  | nil => exact FunctionRaw.zero_valid
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).Valid
    exact FunctionRaw.add_valid (FunctionRaw.constant_valid c)
      (FunctionRaw.mul_valid hf ih)

theorem FunctionRaw.polynomial_agreeOnCommonDomain
    (coeffs : List QComplex) {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid)
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.polynomial coeffs f).AgreeOnCommonDomain
      (FunctionRaw.polynomial coeffs g) := by
  induction coeffs with
  | nil => exact FunctionRaw.zero_agreeOnCommonDomain
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.constant c)
        (FunctionRaw.mul g (FunctionRaw.polynomial cs g)))
    exact FunctionRaw.add_agreeOnCommonDomain
      (FunctionRaw.constant_valid c) (FunctionRaw.constant_valid c)
      (FunctionRaw.mul_valid hf (FunctionRaw.polynomial_valid cs hf))
      (FunctionRaw.mul_valid hg (FunctionRaw.polynomial_valid cs hg))
      (FunctionRaw.constant_agreeOnCommonDomain c)
      (FunctionRaw.mul_agreeOnCommonDomain (f := f) (f' := g)
        (g := FunctionRaw.polynomial cs f)
        (g' := FunctionRaw.polynomial cs g) hf hg
        (FunctionRaw.polynomial_valid cs hf)
        (FunctionRaw.polynomial_valid cs hg)
        hfg ih)

/-! The abstract complex-function API exposes the certified product only
after the raw product closure has been established.  This keeps the handle
layer honest: multiplication carries the intersection domain and inherits
validity from the four-corner rational box product. -/
def ComplexFunction.mul (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.mul f.preferred g.preferred)
    (FunctionRaw.mul_valid f.valid g.valid)

def ComplexFunction.pow (f : ComplexFunction) (n : Nat) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.pow f.preferred n)
    (FunctionRaw.pow_valid f.valid)

def ComplexFunction.constant (c : QComplex) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.constant c)
    (FunctionRaw.constant_valid c)

def ComplexFunction.polynomial
    (coeffs : List QComplex) (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.polynomial coeffs f.preferred)
    (FunctionRaw.polynomial_valid coeffs f.valid)

theorem ComplexFunction.mul_one_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul f ComplexFunction.one).preferred).AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.mul f.preferred FunctionRaw.one).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.mul_one_agreeOnCommonDomain f.valid

theorem ComplexFunction.one_mul_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul ComplexFunction.one f).preferred).AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.mul FunctionRaw.one f.preferred).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.one_mul_agreeOnCommonDomain f.valid

theorem ComplexFunction.mul_zero_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul f ComplexFunction.zero).preferred).AgreeOnCommonDomain
      ComplexFunction.zero.preferred := by
  change (FunctionRaw.mul f.preferred FunctionRaw.zero).AgreeOnCommonDomain
    FunctionRaw.zero
  exact FunctionRaw.mul_zero_agreeOnCommonDomain f.valid

theorem ComplexFunction.zero_mul_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul ComplexFunction.zero f).preferred).AgreeOnCommonDomain
      ComplexFunction.zero.preferred := by
  change (FunctionRaw.mul FunctionRaw.zero f.preferred).AgreeOnCommonDomain
    FunctionRaw.zero
  exact FunctionRaw.zero_mul_agreeOnCommonDomain f.valid

theorem ComplexFunction.mul_comm_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul f g).preferred.AgreeOnCommonDomain
      (ComplexFunction.mul g f).preferred := by
  change (FunctionRaw.mul f.preferred g.preferred).AgreeOnCommonDomain
    (FunctionRaw.mul g.preferred f.preferred)
  exact FunctionRaw.mul_comm_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.mul_assoc_representation_agrees_preferred
    (f g h : ComplexFunction) :
    ((ComplexFunction.mul (ComplexFunction.mul f g) h).preferred).AgreeOnCommonDomain
      (ComplexFunction.mul f (ComplexFunction.mul g h)).preferred := by
  change (FunctionRaw.mul (FunctionRaw.mul f.preferred g.preferred)
      h.preferred).AgreeOnCommonDomain
    (FunctionRaw.mul f.preferred (FunctionRaw.mul g.preferred h.preferred))
  exact FunctionRaw.mul_assoc_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.mul_add_representation_agrees_preferred
    (f g h : ComplexFunction) :
    (ComplexFunction.mul f (ComplexFunction.add g h)).preferred.AgreeOnCommonDomain
      (ComplexFunction.add (ComplexFunction.mul f g)
        (ComplexFunction.mul f h)).preferred := by
  change (FunctionRaw.mul f.preferred
      (FunctionRaw.add g.preferred h.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.mul f.preferred g.preferred)
      (FunctionRaw.mul f.preferred h.preferred))
  exact FunctionRaw.mul_add_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.add_mul_representation_agrees_preferred
    (f g h : ComplexFunction) :
    (ComplexFunction.mul (ComplexFunction.add f g) h).preferred.AgreeOnCommonDomain
      (ComplexFunction.add (ComplexFunction.mul f h)
        (ComplexFunction.mul g h)).preferred := by
  change (FunctionRaw.mul
      (FunctionRaw.add f.preferred g.preferred) h.preferred).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.mul f.preferred h.preferred)
      (FunctionRaw.mul g.preferred h.preferred))
  exact FunctionRaw.add_mul_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.mul_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.mul rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.mul f.preferred g.preferred) := by
  exact FunctionRaw.mul_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

theorem ComplexFunction.pow_representation_agrees_preferred
    {f : ComplexFunction} (rf : ComplexFunction.Representation f) (n : Nat) :
    (FunctionRaw.pow rf.raw n).AgreeOnCommonDomain
      (FunctionRaw.pow f.preferred n) := by
  exact FunctionRaw.pow_agreeOnCommonDomain
    rf.valid f.valid rf.agrees n

theorem ComplexFunction.polynomial_representation_agrees_preferred
    {f : ComplexFunction} (coeffs : List QComplex)
    (rf : ComplexFunction.Representation f) :
    (FunctionRaw.polynomial coeffs rf.raw).AgreeOnCommonDomain
      (FunctionRaw.polynomial coeffs f.preferred) := by
  exact FunctionRaw.polynomial_agreeOnCommonDomain
    coeffs rf.valid f.valid rf.agrees

theorem ComplexFunction.mul_neg_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul f (ComplexFunction.neg g)).preferred.AgreeOnCommonDomain
      (ComplexFunction.neg (ComplexFunction.mul f g)).preferred := by
  change (FunctionRaw.mul f.preferred (FunctionRaw.neg g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.neg (FunctionRaw.mul f.preferred g.preferred))
  exact FunctionRaw.mul_neg_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.neg_mul_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul (ComplexFunction.neg f) g).preferred.AgreeOnCommonDomain
      (ComplexFunction.neg (ComplexFunction.mul f g)).preferred := by
  change (FunctionRaw.mul (FunctionRaw.neg f.preferred) g.preferred).AgreeOnCommonDomain
    (FunctionRaw.neg (FunctionRaw.mul f.preferred g.preferred))
  exact FunctionRaw.neg_mul_agreeOnCommonDomain f.valid g.valid

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
