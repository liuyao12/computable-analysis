import ComputableAnalysis.ModularForms.GeometricExponentialPrefixBound
import ComputableAnalysis.ModularForms.GeometricAngularRectangles
import ComputableAnalysis.GeometricPiRotation
import ComputableAnalysis.ModularForms.ExponentialContinuity

/-! Quantitative agreement of mesh angles with the actual geometric half angle. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory ArctanGeometry

theorem geometricHalfPiUnscheduled_compute (n : Nat) :
    GeometricPiRotation.halfPiUnscheduled.compute n =
      {lo := 2*(positiveLoopComputeAtStage 1 n).lo,
       hi := 2*(positiveLoopComputeAtStage 1 n).hi} := by
  change (RealRaw.scaleRat 2 (arctanGeom 1)).compute n = _
  simp [RealRaw.scaleRat,RealRaw.scaleRatCompute,arctanGeom_one_compute_eq,show (0:Rat)≤2 by decide]

theorem geometricMeshAngle_halfPi_error (N : Nat) :
    Small (sub (geometricMeshAngleScalar N (N+1)).val GeometricPiRotation.imaginaryHalf)
      (4*geometricMeshStep N) := by
  have hh := Rat.le_of_lt (geometricMeshStep_positive N)
  have hw := geometricAngularRectangles_endpoint_width N
  have ha := geometricMeshAngle_eq_upper_rectangles N (N+1)
  have hov (n : Nat) := geometricAngularRectangles_sector_overlap N
    (GeometricPiRotation.halfPiStageSchedule.stage n)
  have hbox (n : Nat) : GeometricPiRotation.halfPi.compute n =
      {lo := 2*(positiveLoopComputeAtStage 1 (GeometricPiRotation.halfPiStageSchedule.stage n)).lo,
       hi := 2*(positiveLoopComputeAtStage 1 (GeometricPiRotation.halfPiStageSchedule.stage n)).hi} :=
    geometricHalfPiUnscheduled_compute _
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
    simp only [sub,add,neg,geometricMeshAngleScalar,GeometricPiRotation.imaginaryHalf,
      imaginaryAxis,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
      realPart,imagPart,RealRaw.ofRat,Rat.neg_zero,Rat.add_zero,Rat.zero_add]

  · change -(4*geometricMeshStep N) ≤ 0; grind only
  · change (0:Rat) ≤ 4*geometricMeshStep N
    exact Rat.mul_nonneg (by decide) hh
  · change -(4*geometricMeshStep N) ≤ geometricMeshAngle N (N+1)+ -(GeometricPiRotation.halfPi.compute m).lo
    rw [hbox,ha]
    have ho := (hov m).2
    change (positiveLoopComputeAtStage 1 (GeometricPiRotation.halfPiStageSchedule.stage m)).lo ≤
      integralUpperSum (geometricAngularCells N (N+1)) at ho
    grind only
  · change geometricMeshAngle N (N+1)+ -(GeometricPiRotation.halfPi.compute n).hi ≤ 4*geometricMeshStep N
    rw [hbox,ha]
    have ho := (hov n).1
    change integralLowerSum (geometricAngularCells N (N+1)) ≤
      (positiveLoopComputeAtStage 1 (GeometricPiRotation.halfPiStageSchedule.stage n)).hi at ho
    change integralUpperSum (geometricAngularCells N (N+1))-
      integralLowerSum (geometricAngularCells N (N+1)) ≤ 2*geometricMeshStep N at hw
    grind only

theorem geometricImaginaryHalf_small : Small GeometricPiRotation.imaginaryHalf 2 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; change (-2:Rat) ≤ 0; decide
  · intro n m; change (0:Rat) ≤ 2; decide
  · intro n m; change (-2:Rat) ≤ (GeometricPiRotation.halfPi.compute m).hi
    have hb := GeometricPiRotation.halfPi_bounds m
    have ho := GeometricPiRotation.halfPi_valid.1 m
    unfold QInterval.width at ho
    grind only
  · intro n m; change (GeometricPiRotation.halfPi.compute n).lo ≤ (2:Rat)
    have hb := GeometricPiRotation.halfPi_bounds n
    have ho := GeometricPiRotation.halfPi_valid.1 n
    unfold QInterval.width at ho
    grind only

theorem geometricMeshAngle_exponential_halfPi_error (N : Nat) :
    Small (sub (entireExponentialValue (geometricMeshAngleScalar N (N+1))).val
      (entireExponentialValue ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩).val)
      (4*exponentialQuadraticConstant geometricFactorRadius*geometricMeshStep N) := by
  have hb := entireExponential_lipschitz geometricFactorRadius
    ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩
    (geometricMeshAngleScalar N (N+1))
    ⟨2,by decide,by decide,geometricImaginaryHalf_small⟩
    ⟨2,by decide,by decide,geometricMeshAngleScalar_small N (N+1) (Nat.le_refl _)⟩
    (4*geometricMeshStep N)
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (geometricMeshStep_positive N)))
    (geometricMeshAngle_halfPi_error N)
  have he : 16*exponentialBudget (exponentialRatio geometricFactorRadius)*
      (exponentialRatio geometricFactorRadius)^2*(4*geometricMeshStep N)=
      4*exponentialQuadraticConstant geometricFactorRadius*geometricMeshStep N := by
    unfold exponentialQuadraticConstant
    grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
