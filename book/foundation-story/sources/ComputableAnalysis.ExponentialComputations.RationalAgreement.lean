import ComputableAnalysis.ExponentialComputations.API
import ComputableAnalysis.ComplexExponentialRealBridge
import ComputableAnalysis.ModularForms.GeometricQuarterTurn

/-! Exact bridges from rational elementary samplers to established numerical
computations and derived represented-point evaluations. No modular function
or additional holomorphic construction is defined here. -/
namespace ComputableAnalysis.ExponentialComputations.Rational
open ComplexRaw FunctionTheory RiemannHilbert ModularForms
set_option maxHeartbeats 1000000

theorem rational_exponentialReal_agrees (x : Rat) :
    (ElementaryRational.exponentialReal.evalRaw x trivial).Equiv (expPowerSeries x) := by
  apply ComplexExponentialApproximation.exponentialRawAt_realPart_equiv_expPowerSeries
    x (QComplex.normBound (QComplex.ofRat x)) (QComplex.normBound_nonneg _)
  simp only [QComplex.normBound,QComplex.ofRat]
  rw [show qabs (0:Rat)=0 by decide +kernel,Rat.add_zero]
  exact Rat.le_refl

theorem rational_sinPi_agrees_derived (r : Rat) :
    (ElementaryRational.sinPi.evalRaw r trivial).Equiv
      (entireExponentialValue
        ⟨imaginaryAxis (ElementaryRational.piAngle r),
          imaginaryAxis_valid (ElementaryRational.piAngle_valid r)⟩).val.imagPart := by
  apply imagPart_equiv
  exact equiv_symm (entireExponential_legacy_lift (ElementaryRational.piRotationInput r))

theorem rational_cosPi_agrees_derived (r : Rat) :
    (ElementaryRational.cosPi.evalRaw r trivial).Equiv
      (entireExponentialValue
        ⟨imaginaryAxis (ElementaryRational.piAngle r),
          imaginaryAxis_valid (ElementaryRational.piAngle_valid r)⟩).val.realPart := by
  apply realPart_equiv
  exact equiv_symm (entireExponential_legacy_lift (ElementaryRational.piRotationInput r))

theorem rational_logarithm_agrees_derived (x : Rat) (hx : logarithm.definedAt x) :
    (logarithm.evalRaw x hx).Equiv (log (positiveRationalInput x hx)).val :=
  integralLog_equiv_log _

private theorem imaginaryAxis_rational (x : Rat) :
    (imaginaryAxis (RealRaw.ofRat x)).Equiv (ofQComplex ⟨0,x⟩) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  rw [imaginaryAxis_compute]
  change QBox.Overlaps (QBox.point ⟨0,x⟩) (QBox.point ⟨0,x⟩)
  exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

private theorem piRotation_agrees_rational_rotation (r x : Rat)
    (h : (ElementaryRational.piAngle r).Equiv (RealRaw.ofRat x)) :
    (ElementaryRational.piRotationValue r).Equiv
      (ElementaryRational.exponentialValue ⟨0,x⟩) := by
  let a : Scalar := ⟨imaginaryAxis (ElementaryRational.piAngle r),
    imaginaryAxis_valid (ElementaryRational.piAngle_valid r)⟩
  let b : Scalar := ⟨ofQComplex ⟨0,x⟩,ofQComplex_valid _⟩
  have hab : a.val.Equiv b.val := equiv_trans a.property
    (imaginaryAxis_valid (x := RealRaw.ofRat x) (RealRaw.ofRat_valid x)) b.property
    (imaginaryAxis_equiv (y := RealRaw.ofRat x)
      (ElementaryRational.piAngle_valid r) (RealRaw.ofRat_valid x) h)
    (imaginaryAxis_rational x)
  exact equiv_trans (ElementaryRational.piRotationValue_valid r)
    (entireExponentialValue a).property (ElementaryRational.exponentialValue_valid ⟨0,x⟩)
    (equiv_symm (entireExponential_legacy_lift (ElementaryRational.piRotationInput r)))
    (equiv_trans (entireExponentialValue a).property (entireExponentialValue b).property
      (ElementaryRational.exponentialValue_valid ⟨0,x⟩)
      (entireExponentialValue_congr a b hab) (rational_powerSeries_agrees ⟨0,x⟩))

/-- Different rational coordinate sets are compared at their actual common
points, rather than comparing sine at the same untransformed parameter. -/
theorem sinPi_radian_agrees_on_chart_overlap :
    ElementaryRational.sinPi.AgreeAtCoordinates ElementaryRational.sineRadianRotation
      ElementaryRational.piAngle RealRaw.ofRat :=
  fun r x _ _ h => imagPart_equiv (piRotation_agrees_rational_rotation r x h)

theorem cosPi_radian_agrees_on_chart_overlap :
    ElementaryRational.cosPi.AgreeAtCoordinates ElementaryRational.cosineRadianRotation
      ElementaryRational.piAngle RealRaw.ofRat :=
  fun r x _ _ h => realPart_equiv (piRotation_agrees_rational_rotation r x h)

private theorem piAngle_half :
    (ElementaryRational.piAngle (1/2)).Equiv GeometricPiRotation.halfPi := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
  simp only [ElementaryRational.piAngle,ElementaryRational.pi,
    RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤1/2 by decide +kernel),
    if_pos (show (0:Rat)≤2 by decide +kernel)]
  rw [←Rat.mul_assoc,←Rat.mul_assoc,show (1/2:Rat)*2=1 by decide +kernel,Rat.one_mul,Rat.one_mul]
  exact ⟨ho,ho⟩

theorem rational_piRotation_half :
    (ElementaryRational.piRotationValue (1/2)).Equiv
      (ofQComplex RotationSeries.imaginaryUnit) := by
  let a : Scalar := ⟨imaginaryAxis (ElementaryRational.piAngle (1/2)),
    imaginaryAxis_valid (ElementaryRational.piAngle_valid _)⟩
  let b : Scalar := ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩
  have hab : a.val.Equiv b.val :=
    imaginaryAxis_equiv (ElementaryRational.piAngle_valid _) GeometricPiRotation.halfPi_valid piAngle_half
  exact equiv_trans (ElementaryRational.piRotationValue_valid _) (entireExponentialValue a).property
    (ofQComplex_valid _) (equiv_symm (entireExponential_legacy_lift (ElementaryRational.piRotationInput _)))
    (equiv_trans (entireExponentialValue a).property (entireExponentialValue b).property
      (ofQComplex_valid _) (entireExponentialValue_congr a b hab) entireExponential_geometric_quarterTurn)

theorem rational_sinPi_half :
    (ElementaryRational.sinPi.evalRaw (1/2) trivial).Equiv (RealRaw.ofRat 1) :=
  imagPart_equiv rational_piRotation_half

theorem rational_cosPi_half :
    (ElementaryRational.cosPi.evalRaw (1/2) trivial).Equiv (RealRaw.ofRat 0) :=
  realPart_equiv rational_piRotation_half

end ComputableAnalysis.ExponentialComputations.Rational
