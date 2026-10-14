import ComputableAnalysis.ModularForms.GeometricAngularLimit
import ComputableAnalysis.ModularForms.GeometricExponentialMeshError

/-! The exact quarter-turn exponential from the geometric mesh and shrinking errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory SeriesLimitLaws

private theorem eulerEndpoint_small (N : Nat) :
    Small (sub (ofQComplex (geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)))
      (ofQComplex RotationSeries.imaginaryUnit)) (geometricEulerEndpointRate N) := by
  obtain ⟨hr,hi⟩ := geometricEulerEndpoint_error N
  have lr := neg_qabs_le_self (geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).re
  have ur := self_le_qabs (geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).re
  have li := neg_qabs_le_self ((geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).im-1)
  have ui := self_le_qabs ((geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).im-1)
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
    simp only [sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
      RotationSeries.imaginaryUnit,realPart,imagPart,RealRaw.ofRat] <;> grind only

theorem entireExponential_geometric_quarterTurn :
    (entireExponentialValue ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩).val.Equiv
      (ofQComplex RotationSeries.imaginaryUnit) := by
  let f := (entireExponentialValue
    ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩).val
  let c := exponentialQuadraticConstant geometricFactorRadius
  let s := c+geometricExponentialErrorScale+1
  have hc : 0 ≤ c := exponentialQuadraticConstant_nonnegative _
  have hs : 0 ≤ s := Rat.add_nonneg (Rat.add_nonneg hc geometricExponentialErrorScale_nonnegative) (by decide)
  have hrate := shrinks_scale geometricEulerEndpointRate geometricEulerEndpointRate_shrinks s hs
  apply equiv_of_small_sub_zero
  apply small_closed (sub f (ofQComplex RotationSeries.imaginaryUnit)) 0
    (fun N => s*geometricEulerEndpointRate N) hrate
  intro N
  let j := geometricConvergenceMesh N
  let p := geometricExponentialProduct j (j+1)
  let q := ofQComplex (geometricEulerMesh j (j+1))
  have hp := geometricExponentialProduct_valid j (j+1)
  have hq := ofQComplex_valid (geometricEulerMesh j (j+1))
  have hangle := geometricMeshAngle_exponential_halfPi_error j
  have hfp := Small.congr
    (sub_valid (entireExponentialValue (geometricMeshAngleScalar j (j+1))).property (entireExponentialValue _).property)
    (sub_valid hp (entireExponentialValue _).property)
    (FunctionTheory.sub_congr (equiv_symm (geometricExponentialProduct_angle j (j+1)))
      (equiv_refl _ (entireExponentialValue _).property)) hangle
  have hpf := small_neg hfp
  have hsym : (neg (sub p f)).Equiv (sub f p) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid hp (entireExponentialValue _).property))
      (hright := sub_valid (entireExponentialValue _).property hp)
    change -(ComplexRawQuotient.ofRaw p hp + -ComplexRawQuotient.ofRaw f (entireExponentialValue _).property) =
      ComplexRawQuotient.ofRaw f (entireExponentialValue _).property + -ComplexRawQuotient.ofRaw p hp
    grind only
  have hfirst := Small.congr (neg_valid (sub_valid hp (entireExponentialValue _).property))
    (sub_valid (entireExponentialValue _).property hp) hsym hpf
  have hb := LocalODE.small_add (LocalODE.small_add hfirst (geometricExponentialProduct_endpoint_error N))
    (eulerEndpoint_small N)
  have hid := difference_via f (ofQComplex RotationSeries.imaginaryUnit) p q
    (entireExponentialValue _).property (ofQComplex_valid _) hp hq
  have hfinal := Small.congr
    (add_valid (add_valid (sub_valid (entireExponentialValue _).property hp) (sub_valid hp hq))
      (sub_valid hq (ofQComplex_valid _)))
    (sub_valid (entireExponentialValue _).property (ofQComplex_valid _)) (equiv_symm hid) hb
  apply hfinal.mono
  have hh := Rat.le_of_lt (geometricMeshStep_positive j)
  have hm := Rat.mul_nonneg hc hh
  unfold geometricExponentialEndpointRate geometricEulerEndpointRate
  dsimp [s,c,j] at *
  grind only

end ComputableAnalysis.ModularForms
