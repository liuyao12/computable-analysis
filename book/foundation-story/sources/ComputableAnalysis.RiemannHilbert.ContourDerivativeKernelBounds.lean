import ComputableAnalysis.RiemannHilbert.ContourDerivativeKernel

/-! Quantitative first-moment errors from the actual reciprocal resolvent.
The estimate is independent of any particular interval name. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal
set_option autoImplicit false

theorem tripleProduct_middle_difference (v s r : Scalar) :
    gridScalarSub (scalarProduct (scalarProduct v s) r) (scalarProduct (scalarProduct v r) r)≈
      scalarProduct (scalarProduct v (gridScalarSub s r)) r := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub (scalarProduct (scalarProduct v s) r) (scalarProduct (scalarProduct v r) r)).property)
    (hright := (scalarProduct (scalarProduct v (gridScalarSub s r)) r).property)
  let V := gridScalarValue v
  let S := gridScalarValue s
  let R := gridScalarValue r
  change (V*S)*R-(V*R)*R=(V*(S-R))*R
  grind only

theorem tripleProduct_middle_bound (q v s r : Scalar) (F U E : Rat)
    (hF : 0≤F) (hU : 0≤U) (hE : 0≤E) (hv : Small v.val F) (hr : Small r.val U)
    (hs : Small (sub s.val r.val) E) (hq : q≈scalarProduct (scalarProduct v s) r) :
    Small (sub q.val (scalarProduct (scalarProduct v r) r).val) (4*F*E*U) := by
  have hm := Small.mul (mul_valid v.property (sub_valid s.property r.property)) r.property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hF) hE) hU
    (Small.mul v.property (sub_valid s.property r.property) hF hE hv hs) hr
  rw [show 2*(2*F*E)*U=4*F*E*U by grind only] at hm
  have he : gridScalarSub q (scalarProduct (scalarProduct v r) r)≈
      scalarProduct (scalarProduct v (gridScalarSub s r)) r :=
    Setoid.trans (FunctionTheory.sub_congr hq (equiv_refl _ (scalarProduct (scalarProduct v r) r).property))
      (tripleProduct_middle_difference v s r)
  exact Small.congr (scalarProduct (scalarProduct v (gridScalarSub s r)) r).property
    (sub_valid q.property (scalarProduct (scalarProduct v r) r).property) (equiv_symm he) hm

theorem ribbonCauchyPoleQuotient_error (f : DomainFunctions.Map) (b z : Scalar) (h : QPos)
    (ha : (ribbonCauchyKernel f b).domain z) (hc : (ribbonCauchyKernel f (rationalShift b h)).domain z)
    (F U : Rat) (hF : 0≤F) (hU : 0≤U)
    (hf : Small (f.eval z ha.1).val F) (hu : Small ((ribbonPoleReciprocal b).eval z ha.2).val U)
    (hh : 16*U*h.val≤1) :
    Small (sub (ribbonCauchyPoleQuotient f b z h ha hc).val
      ((ribbonCauchyDerivativeKernel f b).eval z ha).val) (128*F*U*U*U*h.val) := by
  have hs := ribbonPoleReciprocal_shift_bound b z h ha.2 hc.2 U hU hu hh
  have hE : 0≤32*U*U*h.val :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hU) hU) (Rat.le_of_lt h.property)
  have hm := tripleProduct_middle_bound (ribbonCauchyPoleQuotient f b z h ha hc)
    (f.eval z ha.1) ((ribbonPoleReciprocal (rationalShift b h)).eval z hc.2)
    ((ribbonPoleReciprocal b).eval z ha.2) F U (32*U*U*h.val) hF hU hE hf hu hs
    (ribbonCauchyPoleQuotient_resolvent f b z h ha hc)
  rw [show 4*F*(32*U*U*h.val)*U=128*F*U*U*U*h.val by grind only] at hm
  exact hm

end ComputableAnalysis.RiemannHilbert.RectangularContour
