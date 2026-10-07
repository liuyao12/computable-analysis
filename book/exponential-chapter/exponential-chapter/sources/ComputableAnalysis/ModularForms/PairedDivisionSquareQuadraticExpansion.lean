import ComputableAnalysis.ModularForms.PairedDivisionCubicDerivativeExpansion

/-! Quadratic center expansion of the actual division square. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def difference (x y : Scalar) : Scalar := ⟨sub x.val y.val,sub_valid x.property y.property⟩

def pairedDivisionSquareQuadraticResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  let q := pairedRegularDivisionMap.eval z hz
  let a : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let p := scalarProduct (scalarProduct a b) (scalarProduct z z)
  difference (difference (scalarProduct q q) (scalarProduct a a))
    ⟨scaleRat 2 p.val,scaleRat_valid p.property⟩

private theorem square_algebra (Q A B Z : ScalarAlgebra.Value) :
    ((Q-A)-(Z*Z)*B)*((Q+A)+B*(Z*Z))+(B*B)*((Z*Z)*(Z*Z))=
      (Q*Q-A*A)-ComplexRawQuotient.scaleRat 2 ((A*B)*(Z*Z)) := by
  have h := ScalarAlgebra.scale_natural 2 ((A*B)*(Z*Z))
  change ComplexRawQuotient.scaleRat 2 ((A*B)*(Z*Z))=(2:ScalarAlgebra.Value)*((A*B)*(Z*Z)) at h
  rw [h]
  grind only

/-- The actual division square has a quadratic polynomial with a quartic coordinate error. -/
theorem pairedRegularDivision_square_quadratic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (pairedDivisionSquareQuadraticResidual z hz).val (47104*R*R*R*R) := by
  let q := pairedRegularDivisionMap.eval z hz
  let a : Scalar := ⟨pairedCenterConstantSum,pairedCenterConstantSum_valid⟩
  let b : Scalar := ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
  let z2 := scalarProduct z z
  let z4 := scalarProduct z2 z2
  let e := difference (difference q a) (scalarProduct z2 b)
  let j := scalarSum (scalarSum q a) (scalarProduct b z2)
  let rem := scalarSum (scalarProduct e j) (scalarProduct (scalarProduct b b) z4)
  have hq : Small q.val 16 := by
    have h := inverseSquareSeriesValue_bound _
      (fun n => (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property) 8
      (pairedRegularDivisionTerm_bound z (LocalODE.interior_bound _ z hz))
    simpa only [q,pairedRegularDivisionMap,pairedRegularDivisionValue,
      show 2*((8:Nat):Rat)=16 by decide +kernel] using h
  have ha : Small a.val 4 := by
    have h := inverseSquareSeriesValue_bound _ pairedCenterConstantTerm_valid 2 pairedCenterConstantTerm_bound
    simpa only [a,pairedCenterConstantSum,show 2*((2:Nat):Rat)=4 by decide +kernel] using h
  have hb : Small b.val 8 := by
    have h := inverseSquareSeriesValue_bound _ pairedCenterQuadraticTerm_valid 4 pairedCenterQuadraticTerm_bound
    simpa only [b,pairedCenterQuadraticSum,show 2*((4:Nat):Rat)=8 by decide +kernel] using h
  have hz2fixed := Small.mul z.property z.property (show (0:Rat)≤1/4 by decide +kernel)
    (show (0:Rat)≤1/4 by decide +kernel) (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ z hz)
  have hjterm := Small.mul b.property z2.property (show (0:Rat)≤8 by decide +kernel)
    (show (0:Rat)≤2*(1/4)*(1/4) by decide +kernel) hb hz2fixed
  have hj := LocalODE.small_add (LocalODE.small_add hq ha) hjterm
  have hj' : Small j.val 22 := by
    rw [show (16:Rat)+4+2*8*(2*(1/4)*(1/4))=22 by decide +kernel] at hj
    exact hj
  have he : Small e.val (1024*R*R*R*R) :=
    pairedRegularDivisionValue_quadratic_center_bound z hz R hR hs
  have hR2 : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR
  have hR4 : 0≤2*(2*R*R)*(2*R*R) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR2) hR2
  have hz2 : Small z2.val (2*R*R) := Small.mul z.property z.property hR hR hs hs
  have hz4 : Small z4.val (2*(2*R*R)*(2*R*R)) := Small.mul z2.property z2.property hR2 hR2 hz2 hz2
  have heNonneg : 0≤1024*R*R*R*R := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR
  have hprod := Small.mul e.property j.property heNonneg (show (0:Rat)≤22 by decide +kernel) he hj'
  have hb2 := Small.mul b.property b.property (show (0:Rat)≤8 by decide +kernel)
    (show (0:Rat)≤8 by decide +kernel) hb hb
  have hlast := Small.mul (scalarProduct b b).property z4.property
    (show (0:Rat)≤2*8*8 by decide +kernel) hR4 hb2 hz4
  have hbound := LocalODE.small_add hprod hlast
  have hrate : 2*(1024*R*R*R*R)*22+2*(2*8*8)*(2*(2*R*R)*(2*R*R))=47104*R*R*R*R := by grind only
  rw [hrate] at hbound
  have heq : rem.val.Equiv (pairedDivisionSquareQuadraticResidual z hz).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := rem.property)
      (hright := (pairedDivisionSquareQuadraticResidual z hz).property)
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let B := ComplexRawQuotient.ofRaw b.val b.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change ((Q-A)-(Z*Z)*B)*((Q+A)+B*(Z*Z))+(B*B)*((Z*Z)*(Z*Z))=
      (Q*Q-A*A)-ComplexRawQuotient.scaleRat 2 ((A*B)*(Z*Z))
    exact square_algebra Q A B Z
  exact Small.congr rem.property (pairedDivisionSquareQuadraticResidual z hz).property heq hbound

end ComputableAnalysis.ModularForms
