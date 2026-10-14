import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleCauchy
import ComputableAnalysis.RiemannHilbert.ContourBoundaryFinite
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness

/-! Actual first Cauchy moment kernels and rational pole differences. The
resolvent identity and error bound hold for arbitrary represented values. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal
set_option autoImplicit false

def ribbonCauchyDerivativeKernel (f : DomainFunctions.Map) (b : Scalar) : DomainFunctions.Map :=
  productOn (ribbonCauchyKernel f b) (ribbonPoleReciprocal b) (fun _ hz => hz.2)

def ribbonCauchyDerivativeKernel_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) :
    Holomorphic (ribbonCauchyDerivativeKernel f b) :=
  (ribbonCauchyKernel_holomorphic f hf b).productOn (ribbonPoleReciprocal_holomorphic b) (fun _ hz => hz.2)

theorem rectangleDerivativeBoundaryDomains (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) : RectangleBoundaryDomains (ribbonCauchyDerivativeKernel f b) J :=
  let hd := rectangleCauchyBoundaryDomains f J hdom b hb
  ⟨hd.bottom,hd.top,hd.left,hd.right⟩

def fixedRectangleDerivativeContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) : Scalar :=
  continuousRectangleBoundary (ribbonCauchyDerivativeKernel f b) J (rectangleDerivativeBoundaryDomains f J hdom b hb) n

theorem rectanglePoleInterior_rationalShift (J : QInterval × QInterval) (b : Scalar) (D h : QPos)
    (hb : representedRectangleContains (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b)
    (hh : h.val≤D.val/2) : RectanglePoleInterior J (rationalShift b h) := by
  let E : QPos := ⟨D.val/2,by rw [Rat.div_def]; exact Rat.mul_pos D.property (by decide +kernel)⟩
  have hp := Rat.le_of_lt h.property
  refine ⟨E,?_,?_,?_,?_⟩
  · intro n m
    have h0 := hb.1 n m
    change J.1.lo+D.val≤(b.val.compute m).hi.re at h0
    simp only [rationalShift,scalarSum,realStep,ComplexRaw.realPart,ComplexRaw.add,ComplexRaw.scaleRat,ComplexRaw.one,QComplex.one,ComplexRaw.ofQComplex,QBox.add,QBox.scaleRat,QComplex.add,if_pos hp,Rat.mul_one]
    change J.1.lo+E.val≤(b.val.compute m).hi.re+h.val
    have hp := h.property
    dsimp [E]
    grind only
  · intro n m
    have h0 := hb.2.1 n m
    change (b.val.compute n).lo.re≤J.1.hi-D.val at h0
    simp only [rationalShift,scalarSum,realStep,ComplexRaw.realPart,ComplexRaw.add,ComplexRaw.scaleRat,ComplexRaw.one,QComplex.one,ComplexRaw.ofQComplex,QBox.add,QBox.scaleRat,QComplex.add,if_pos hp,Rat.mul_one]
    change (b.val.compute n).lo.re+h.val≤J.1.hi-E.val
    dsimp [E]
    grind only
  · intro n m
    have h0 := hb.2.2.1 n m
    change J.2.lo+D.val≤(b.val.compute m).hi.im at h0
    simp only [rationalShift,scalarSum,realStep,ComplexRaw.imagPart,ComplexRaw.add,ComplexRaw.scaleRat,ComplexRaw.one,QComplex.one,ComplexRaw.ofQComplex,QBox.add,QBox.scaleRat,QComplex.add,if_pos hp,Rat.mul_zero]
    change J.2.lo+E.val≤(b.val.compute m).hi.im+0
    have hp := D.property
    dsimp [E]
    grind only
  · intro n m
    have h0 := hb.2.2.2 n m
    change (b.val.compute n).lo.im≤J.2.hi-D.val at h0
    simp only [rationalShift,scalarSum,realStep,ComplexRaw.imagPart,ComplexRaw.add,ComplexRaw.scaleRat,ComplexRaw.one,QComplex.one,ComplexRaw.ofQComplex,QBox.add,QBox.scaleRat,QComplex.add,if_pos hp,Rat.mul_zero]
    change (b.val.compute n).lo.im+0≤J.2.hi-E.val
    have hp := D.property
    dsimp [E]
    grind only

theorem ribbonPoleOffset_shift_difference (b z : Scalar) (h : QPos) :
    gridScalarSub ((ribbonPoleOffset (rationalShift b h)).eval z trivial)
      ((ribbonPoleOffset b).eval z trivial)≈scalarNeg (realStep h) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub ((ribbonPoleOffset (rationalShift b h)).eval z trivial)
      ((ribbonPoleOffset b).eval z trivial)).property) (hright := (scalarNeg (realStep h)).property)
  let B := gridScalarValue b
  let Z := gridScalarValue z
  let H := gridScalarValue (realStep h)
  change (-(B+H)+1*Z)-(-B+1*Z)= -H
  grind only

theorem ribbonPoleReciprocal_shift_bound (b z : Scalar) (h : QPos)
    (ha : (ribbonPoleReciprocal b).domain z) (hc : (ribbonPoleReciprocal (rationalShift b h)).domain z)
    (U : Rat) (hU : 0≤U) (hu : Small ((ribbonPoleReciprocal b).eval z ha).val U)
    (hh : 16*U*h.val≤1) :
    Small (sub ((ribbonPoleReciprocal (rationalShift b h)).eval z hc).val
      ((ribbonPoleReciprocal b).eval z ha).val) (32*U*U*h.val) := by
  have hs : Small (sub ((ribbonPoleOffset (rationalShift b h)).eval z trivial).val
      ((ribbonPoleOffset b).eval z trivial).val) h.val :=
    Small.congr (scalarNeg (realStep h)).property
      (sub_valid ((ribbonPoleOffset (rationalShift b h)).eval z trivial).property
        ((ribbonPoleOffset b).eval z trivial).property)
      (equiv_symm (ribbonPoleOffset_shift_difference b z h)) (SeriesLimitLaws.small_neg (realStep_small h))
  exact inverse_near_difference_bound ((ribbonPoleOffset b).eval z trivial)
    ((ribbonPoleOffset (rationalShift b h)).eval z trivial) (compose_outer_mem ha) (compose_outer_mem hc)
    U h.val hU (Rat.le_of_lt h.property) hu hs hh

def ribbonCauchyPoleQuotient (f : DomainFunctions.Map) (b z : Scalar) (h : QPos)
    (ha : (ribbonCauchyKernel f b).domain z) (hc : (ribbonCauchyKernel f (rationalShift b h)).domain z) : Scalar :=
  RadialLogarithmChains.scale (1/h.val)
    (gridScalarSub ((ribbonCauchyKernel f (rationalShift b h)).eval z hc) ((ribbonCauchyKernel f b).eval z ha))

theorem ribbonCauchyPoleQuotient_resolvent (f : DomainFunctions.Map) (b z : Scalar) (h : QPos)
    (ha : (ribbonCauchyKernel f b).domain z) (hc : (ribbonCauchyKernel f (rationalShift b h)).domain z) :
    ribbonCauchyPoleQuotient f b z h ha hc≈
      scalarProduct (scalarProduct (f.eval z ha.1) ((ribbonPoleReciprocal (rationalShift b h)).eval z hc.2))
        ((ribbonPoleReciprocal b).eval z ha.2) := by
  let a := (ribbonPoleOffset b).eval z trivial
  let c := (ribbonPoleOffset (rationalShift b h)).eval z trivial
  let R := gridScalarValue ((ribbonPoleReciprocal b).eval z ha.2)
  let S := gridScalarValue ((ribbonPoleReciprocal (rationalShift b h)).eval z hc.2)
  let A := gridScalarValue a
  let C := gridScalarValue c
  let F := gridScalarValue (f.eval z ha.1)
  have hA := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid a.property
    ((ribbonPoleReciprocal b).eval z ha.2).property) (hright := ofQComplex_valid _)
    (mul_inverse a (compose_outer_mem ha.2))
  have hC := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid c.property
    ((ribbonPoleReciprocal (rationalShift b h)).eval z hc.2).property) (hright := ofQComplex_valid _)
    (mul_inverse c (compose_outer_mem hc.2))
  have hdiff := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (gridScalarSub c a).property) (hright := (scalarNeg (realStep h)).property)
    (ribbonPoleOffset_shift_difference b z h)
  change A*R=1 at hA
  change C*S=1 at hC
  change C-A= -ComplexRawQuotient.scaleRat h.val 1 at hdiff
  have hi := Rat.div_mul_cancel (a := (1:Rat)) (Rat.ne_of_gt h.property)
  have hd : S-R=ComplexRawQuotient.scaleRat h.val (S*R) := by
    have ht : ComplexRawQuotient.scaleRat h.val (S*R)=ComplexRawQuotient.scaleRat h.val 1*(S*R) := by
      rw [←ComplexRawQuotient.scaleRat_mul,show (1:ScalarAlgebra.Value)*(S*R)=S*R by grind only]
    rw [ht]
    grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (ribbonCauchyPoleQuotient f b z h ha hc).property)
    (hright := (scalarProduct (scalarProduct (f.eval z ha.1)
      ((ribbonPoleReciprocal (rationalShift b h)).eval z hc.2)) ((ribbonPoleReciprocal b).eval z ha.2)).property)
  change ComplexRawQuotient.scaleRat (1/h.val) (F*S-F*R)=(F*S)*R
  rw [show F*S-F*R=F*(S-R) by grind only,hd,ComplexRawQuotient.mul_scaleRat,
    ComplexRawQuotient.scaleRat_scaleRat,hi,ComplexRawQuotient.scaleRat_one]
  grind only


end ComputableAnalysis.RiemannHilbert.RectangularContour
