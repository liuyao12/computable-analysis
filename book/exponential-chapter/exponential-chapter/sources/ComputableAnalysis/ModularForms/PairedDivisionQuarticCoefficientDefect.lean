import ComputableAnalysis.ModularForms.PairedDivisionSquareQuadraticExpansion

/-! Exact extraction of the quartic Riccati coefficient from actual series errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def difference (x y : Scalar) : Scalar := ⟨sub x.val y.val,sub_valid x.property y.property⟩
private def scale (r : Rat) (x : Scalar) : Scalar := ⟨scaleRat r x.val,scaleRat_valid x.property⟩

def pairedDivisionQuarticCoefficientDefect : Scalar :=
  let a : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let d : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  scalarSum (scale 7 d) (scale 2 (scalarProduct a b))

def pairedDivisionQuarticValueResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  let q := pairedRegularDivisionMap.eval z hz
  let a : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let d : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  let z2 := scalarProduct z z
  difference (difference (difference q a) (scalarProduct z2 b)) (scalarProduct (scalarProduct z2 z2) d)

def pairedDivisionCubicDerivativeResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  let q := pairedRegularDivisionDerivative z hz
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let d : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  difference (difference q (scalarProduct (scale 2 z) b))
    (scalarProduct (scale 4 (scalarProduct (scalarProduct z z) z)) d)

def pairedDivisionQuarticError (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  scalarSum (scalarProduct z (pairedDivisionCubicDerivativeResidual z hz))
    (scalarSum (scale 3 (pairedDivisionQuarticValueResidual z hz))
      (scalarProduct (scalarProduct z z) (pairedDivisionSquareQuadraticResidual z hz)))

private theorem quartic_algebra (Z Q P A B D : ScalarAlgebra.Value)
    (hr : Z*P+(Q+(Q+(Q+(Z*Z)*(Q*Q))))=A+(A+A))
    (hb : B+(B+(B+(B+(B+A*A))))=0) :
    ((Z*Z)*(Z*Z))*(ComplexRawQuotient.scaleRat 7 D+ComplexRawQuotient.scaleRat 2 (A*B))=
    -(Z*((P-(ComplexRawQuotient.scaleRat 2 Z)*B)-(ComplexRawQuotient.scaleRat 4 ((Z*Z)*Z))*D)+
      (ComplexRawQuotient.scaleRat 3 (((Q-A)-(Z*Z)*B)-((Z*Z)*(Z*Z))*D)+
        (Z*Z)*((Q*Q-A*A)-ComplexRawQuotient.scaleRat 2 ((A*B)*(Z*Z))))) := by
  have sc2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x := by
    have h := ScalarAlgebra.scale_natural 2 x
    change ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x at h
    exact h
  have sc3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x := by
    have h := ScalarAlgebra.scale_natural 3 x
    change ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x at h
    exact h
  have sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x := by
    have h := ScalarAlgebra.scale_natural 4 x
    change ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x at h
    exact h
  have sc7 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 7 x=(7:ScalarAlgebra.Value)*x := by
    have h := ScalarAlgebra.scale_natural 7 x
    change ComplexRawQuotient.scaleRat 7 x=(7:ScalarAlgebra.Value)*x at h
    exact h
  simp only [sc2,sc3,sc4,sc7]
  grind only

/-- The quartic coefficient defect is exactly the negative of the actual local errors. -/
theorem pairedDivisionQuarticCoefficientDefect_decomposition (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    (mul (mul (mul z.val z.val) (mul z.val z.val)) pairedDivisionQuarticCoefficientDefect.val).Equiv
      (neg (pairedDivisionQuarticError z hz).val) := by
  let q := pairedRegularDivisionMap.eval z hz
  let p := pairedRegularDivisionDerivative z hz
  let a : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let d : Scalar := ⟨pairedCenterQuarticSum,pairedCenterQuarticSum_valid⟩
  have hr := equiv_trans
    (add_valid (mul_valid z.property p.property) (add_valid q.property
      (add_valid q.property (add_valid q.property (mul_valid (mul_valid z.property z.property) (mul_valid q.property q.property))))))
    pairedRiccatiCenterConstant.property (add_valid a.property (add_valid a.property a.property))
    (pairedRegularDivision_riccati_identity z hz) pairedRiccatiCenterConstant_center_coefficient
  have hR := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid (mul_valid z.property p.property) (add_valid q.property
      (add_valid q.property (add_valid q.property (mul_valid (mul_valid z.property z.property) (mul_valid q.property q.property))))))
    (hright := add_valid a.property (add_valid a.property a.property)) hr
  have hB := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := pairedDivisionQuadraticCoefficientDefect.property) (hright := ofQComplex_valid _)
    pairedDivisionQuadraticCoefficientDefect_eq_zero
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))
      pairedDivisionQuarticCoefficientDefect.property)
    (hright := neg_valid (pairedDivisionQuarticError z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change Z*P+(Q+(Q+(Q+(Z*Z)*(Q*Q))))=A+(A+A) at hR
  change B+(B+(B+(B+(B+A*A))))=0 at hB
  change ((Z*Z)*(Z*Z))*(ComplexRawQuotient.scaleRat 7 D+ComplexRawQuotient.scaleRat 2 (A*B))=
    -(Z*((P-(ComplexRawQuotient.scaleRat 2 Z)*B)-(ComplexRawQuotient.scaleRat 4 ((Z*Z)*Z))*D)+
      (ComplexRawQuotient.scaleRat 3 (((Q-A)-(Z*Z)*B)-((Z*Z)*(Z*Z))*D)+
        (Z*Z)*((Q*Q-A*A)-ComplexRawQuotient.scaleRat 2 ((A*B)*(Z*Z)))))
  exact quartic_algebra Z Q P A B D hR hB

/-- Actual sextic errors bound the coefficient after multiplication by the fourth power. -/
theorem pairedDivisionQuarticCoefficientDefect_scaled_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (mul (mul (mul z.val z.val) (mul z.val z.val)) pairedDivisionQuarticCoefficientDefect.val)
      (307200*R*R*R*R*R*R) := by
  have hD : Small (pairedDivisionCubicDerivativeResidual z hz).val (47104*R*R*R*R*R) :=
    pairedRegularDivisionDerivativeValue_cubic_center_bound z hz R hR hs
  have hV : Small (pairedDivisionQuarticValueResidual z hz).val (8192*R*R*R*R*R*R) :=
    pairedRegularDivisionValue_quartic_center_bound z hz R hR hs
  have hS := pairedRegularDivision_square_quadratic_center_bound z hz R hR hs
  have hD0 : 0≤47104*R*R*R*R*R := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR) hR
  have hS0 : 0≤47104*R*R*R*R := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR
  have hZ2 : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR
  have hfirst := Small.mul z.property (pairedDivisionCubicDerivativeResidual z hz).property hR hD0 hs hD
  have hmiddle := LocalODE.small_scale (show (0:Rat)≤3 by decide +kernel) hV
  have hz2 := Small.mul z.property z.property hR hR hs hs
  have hlast := Small.mul (scalarProduct z z).property (pairedDivisionSquareQuadraticResidual z hz).property hZ2 hS0 hz2 hS
  have h := SeriesLimitLaws.small_neg (LocalODE.small_add hfirst (LocalODE.small_add hmiddle hlast))
  have hrate : 2*R*(47104*R*R*R*R*R)+(3*(8192*R*R*R*R*R*R)+2*(2*R*R)*(47104*R*R*R*R))=
    307200*R*R*R*R*R*R := by grind only
  rw [hrate] at h
  exact Small.congr (neg_valid (pairedDivisionQuarticError z hz).property)
    (mul_valid (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))
      pairedDivisionQuarticCoefficientDefect.property)
    (equiv_symm (pairedDivisionQuarticCoefficientDefect_decomposition z hz)) h

end ComputableAnalysis.ModularForms
