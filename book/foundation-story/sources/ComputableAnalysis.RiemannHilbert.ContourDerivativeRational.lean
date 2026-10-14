import ComputableAnalysis.RiemannHilbert.ContourDerivativeExamples

/-! Exact rational first-moment arithmetic is proved equivalent to the
actual represented quadratures when numerator and pole are rational. This
provides tighter executable names without altering the general theorem. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal
set_option autoImplicit false

theorem rationalScalar_nonzero_norm (q : QComplex)
    (hq : NonzeroBoxSearch.Nonzero (rationalRectangleScalar q)) : QComplex.normSq q≠0 := by
  intro h
  have he := QComplex.normSq_eq_zero_iff.mp h
  subst q
  exact hq (equiv_refl _ (ofQComplex_valid _))

theorem ribbonPoleReciprocal_rational_value (b q : QComplex)
    (hz : (ribbonPoleReciprocal (rationalRectangleScalar b)).domain (rationalRectangleScalar q)) :
    (ribbonPoleReciprocal (rationalRectangleScalar b)).eval (rationalRectangleScalar q) hz≈
      rationalRectangleScalar (RationalReciprocal.inverse (QComplex.sub q b)) := by
  let a := (ribbonPoleOffset (rationalRectangleScalar b)).eval (rationalRectangleScalar q) trivial
  let v := rationalRectangleScalar (QComplex.sub q b)
  have he : a≈v := ribbonPoleOffset_agreement _ _
  have hn : NonzeroBoxSearch.Nonzero v := (NonzeroBoxSearch.nonzero_congr a v he).mp (compose_outer_mem hz)
  exact Setoid.trans (b := inverse v hn) (inverse_congr a v (compose_outer_mem hz) hn he)
    (rational_inverse_agreement _ hn (rationalScalar_nonzero_norm _ hn))

def rationalFirstMomentSample (s : QComplex → QComplex) (b q : QComplex) : Scalar :=
  let r := RationalReciprocal.inverse (QComplex.sub q b)
  rationalRectangleScalar (QComplex.mul (QComplex.mul (s q) r) r)

theorem rationalScalar_triple_product (x y z : QComplex) :
    scalarProduct (scalarProduct (rationalRectangleScalar x) (rationalRectangleScalar y)) (rationalRectangleScalar z)≈
      rationalRectangleScalar (QComplex.mul (QComplex.mul x y) z) := by
  exact Setoid.trans (b := scalarProduct (rationalRectangleScalar (QComplex.mul x y)) (rationalRectangleScalar z))
    (mul_equiv (scalarProduct (rationalRectangleScalar x) (rationalRectangleScalar y)).property
      (rationalRectangleScalar (QComplex.mul x y)).property (rationalRectangleScalar z).property
      (rationalRectangleScalar z).property (RationalReciprocal.raw_mul_constants x y)
      (equiv_refl _ (rationalRectangleScalar z).property)) (RationalReciprocal.raw_mul_constants _ _)

theorem rationalFirstMomentSample_agreement (f : DomainFunctions.Map) (s : QComplex → QComplex) (b q : QComplex)
    (hz : (ribbonCauchyDerivativeKernel f (rationalRectangleScalar b)).domain (rationalRectangleScalar q))
    (hs : f.eval (rationalRectangleScalar q) hz.1≈rationalRectangleScalar (s q)) :
    (ribbonCauchyDerivativeKernel f (rationalRectangleScalar b)).eval (rationalRectangleScalar q) hz≈
      rationalFirstMomentSample s b q := by
  let r := (ribbonPoleReciprocal (rationalRectangleScalar b)).eval (rationalRectangleScalar q) hz.2
  let t := rationalRectangleScalar (RationalReciprocal.inverse (QComplex.sub q b))
  have hr : r≈t := ribbonPoleReciprocal_rational_value b q hz.2
  exact Setoid.trans (b := scalarProduct (scalarProduct (rationalRectangleScalar (s q)) t) t)
    (mul_equiv (scalarProduct (f.eval _ hz.1) r).property (scalarProduct (rationalRectangleScalar (s q)) t).property
      r.property t.property (mul_equiv (f.eval _ hz.1).property (rationalRectangleScalar (s q)).property
        r.property t.property hs hr) hr) (rationalScalar_triple_product _ _ _)

theorem fixedRectangleDerivativeContour_rational (f : DomainFunctions.Map) (s : QComplex → QComplex)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : QComplex)
    (hb : RectanglePoleInterior J (rationalRectangleScalar b))
    (hs : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, f.eval (rationalRectangleScalar q) hz≈rationalRectangleScalar (s q))
    (n : Nat) :
    rectangleGridBoundary (rationalFirstMomentSample s b) J (2^n)≈
      fixedRectangleDerivativeContour f J hdom (rationalRectangleScalar b) hb n :=
  rectangleGridBoundary_edges _ J (rectanglePoleInterior_ordered J _ hb).1 (rectanglePoleInterior_ordered J _ hb).2
    (rectangleDerivativeBoundaryDomains f J hdom _ hb) _
    (fun q hq hz => equiv_symm (rationalFirstMomentSample_agreement f s b q hz (hs q hq hz.1))) n

theorem rationalAffine_eval (a d q : QComplex) :
    (DomainFunctions.affine (rationalRectangleScalar a) (rationalRectangleScalar d)).eval (rationalRectangleScalar q) trivial≈
      rationalRectangleScalar (QComplex.add a (QComplex.mul d q)) := by
  have hm : scalarProduct (rationalRectangleScalar d) (rationalRectangleScalar q)≈rationalRectangleScalar (QComplex.mul d q) :=
    RationalReciprocal.raw_mul_constants d q
  exact Setoid.trans (b := scalarSum (rationalRectangleScalar a) (rationalRectangleScalar (QComplex.mul d q)))
    (add_equiv (equiv_refl _ (rationalRectangleScalar a).property) hm)
    (equiv_refl (ofQComplex (QComplex.add a (QComplex.mul d q))) (ofQComplex_valid _))

theorem rationalGeometric_eval (q : QComplex) (hz : CauchyGeometricExample.analyticFunction.domain (rationalRectangleScalar q)) :
    CauchyGeometricExample.analyticFunction.eval (rationalRectangleScalar q) hz≈
      rationalRectangleScalar (RationalReciprocal.inverse (QComplex.sub QComplex.one q)) := by
  let hn := compose_outer_mem hz
  have hv : CauchyGeometricExample.denominator (rationalRectangleScalar q)=rationalRectangleScalar (QComplex.sub QComplex.one q) := rfl
  have hp : NonzeroBoxSearch.Nonzero (rationalRectangleScalar (QComplex.sub QComplex.one q)) := by
    rw [←hv]
    exact hn
  exact rational_inverse_agreement _ hp (rationalScalar_nonzero_norm _ hp)

end ComputableAnalysis.RiemannHilbert.RectangularContour
