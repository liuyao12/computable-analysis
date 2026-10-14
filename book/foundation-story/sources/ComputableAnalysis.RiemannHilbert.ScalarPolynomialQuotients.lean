import ComputableAnalysis.RiemannHilbert.ScalarPolynomialArithmetic
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! Executable polynomial fractions and their finite arithmetic. Denominator
nonvanishing, cancellation, exact evaluation and genuine holomorphy are
proved from the actual coefficient lists and represented reciprocals. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPolynomialQuotients
open ComplexRaw FunctionTheory DomainFunctions RectangularContour ScalarPolynomial NonzeroBoxSearch
set_option autoImplicit false

abbrev Fraction := Polynomial × Polynomial
def numerator (r : Fraction) : Polynomial := r.1
def denominator (r : Fraction) : Polynomial := r.2
def inverseFunction (r : Fraction) : DomainFunctions.Map :=
  compose ReciprocalHolomorphic.function (ScalarPolynomial.function (denominator r))
def function (r : Fraction) : DomainFunctions.Map :=
  productOn (inverseFunction r) (ScalarPolynomial.function (numerator r)) (fun _ _ => trivial)
def holomorphic (r : Fraction) : Holomorphic (function r) :=
  (ReciprocalHolomorphic.holomorphic.compose (ScalarPolynomial.holomorphic (denominator r))).productOn
    (ScalarPolynomial.holomorphic (numerator r)) (fun _ _ => trivial)
theorem domain_iff (r : Fraction) (z : Scalar) :
    (function r).domain z↔Nonzero (value (denominator r) z) :=
  ⟨fun h => h.2,fun h => ⟨trivial,h⟩⟩

def evaluate (r : Fraction) (z : Scalar) (hz : Nonzero (value (denominator r) z)) : Scalar :=
  (function r).eval z ((domain_iff r z).2 hz)

theorem image_equiv {a b : Scalar} (h : a≈b) : gridScalarValue a=gridScalarValue b :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := a.property) (hright := b.property) h

theorem inverse_image (a : Scalar) (ha : Nonzero a) :
    gridScalarValue a*gridScalarValue (RepresentedReciprocal.inverse a ha)=1 :=
  ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid a.property (RepresentedReciprocal.inverse a ha).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse a ha)

theorem clear (r : Fraction) (z : Scalar) (hz : Nonzero (value (denominator r) z)) :
    scalarProduct (value (denominator r) z) (evaluate r z hz)≈value (numerator r) z := by
  have hi := inverse_image (value (denominator r) z) hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (value (denominator r) z) (evaluate r z hz)).property)
    (hright := (value (numerator r) z).property)
  change gridScalarValue (value (denominator r) z)*
    gridScalarValue (RepresentedReciprocal.inverse (value (denominator r) z) hz)=1 at hi
  change gridScalarValue (value (denominator r) z)*
    (gridScalarValue (RepresentedReciprocal.inverse (value (denominator r) z) hz)*
      gridScalarValue (value (numerator r) z))=gridScalarValue (value (numerator r) z)
  grind only

theorem clear_unique (r : Fraction) (z : Scalar) (hz : Nonzero (value (denominator r) z))
    (u : Scalar) (hu : scalarProduct (value (denominator r) z) u≈value (numerator r) z) :
    evaluate r z hz≈u :=
  RepresentedReciprocal.mul_cancel _ hz _ _ (Setoid.trans (clear r z hz) (Setoid.symm hu))

theorem product_nonzero (a b : Scalar) (ha : Nonzero a) (hb : Nonzero b) :
    Nonzero (scalarProduct a b) := by
  apply RepresentedReciprocal.nonzero_of_inverse _
    (scalarProduct (RepresentedReciprocal.inverse a ha) (RepresentedReciprocal.inverse b hb))
  have hia := inverse_image a ha
  have hib := inverse_image b hb
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
  change gridScalarValue a*gridScalarValue (RepresentedReciprocal.inverse a ha)=1 at hia
  change gridScalarValue b*gridScalarValue (RepresentedReciprocal.inverse b hb)=1 at hib
  change (gridScalarValue a*gridScalarValue b)*
    (gridScalarValue (RepresentedReciprocal.inverse a ha)*gridScalarValue (RepresentedReciprocal.inverse b hb))=1
  grind only

theorem product_nonzero_iff (a b : Scalar) : Nonzero (scalarProduct a b)↔Nonzero a ∧ Nonzero b := by
  constructor
  · intro h
    constructor
    · intro ha
      apply h
      exact equiv_trans (scalarProduct a b).property
        (mul_valid (ofQComplex_valid _) b.property) (ofQComplex_valid _)
        (mul_equiv a.property (ofQComplex_valid _) b.property b.property ha (Setoid.refl b))
        (zero_mul_equiv _ b.property)
    · intro hb
      apply h
      exact equiv_trans (scalarProduct a b).property
        (mul_valid a.property (ofQComplex_valid _)) (ofQComplex_valid _)
        (mul_equiv a.property a.property b.property (ofQComplex_valid _) (Setoid.refl a) hb)
        (mul_zero_equiv _ a.property)
  · intro h
    exact product_nonzero a b h.1 h.2

def add (r s : Fraction) : Fraction :=
  (ScalarPolynomialArithmetic.add
    (ScalarPolynomialArithmetic.multiply (numerator r) (denominator s))
    (ScalarPolynomialArithmetic.multiply (numerator s) (denominator r)),
    ScalarPolynomialArithmetic.multiply (denominator r) (denominator s))
def scale (c : Scalar) (r : Fraction) : Fraction :=
  (ScalarPolynomialArithmetic.scale c (numerator r),denominator r)
def subtract (r s : Fraction) : Fraction := add r (scale (rationalRectangleScalar ⟨-1,0⟩) s)
def constant (c : Scalar) : Fraction := ([c],[oneScalar])

theorem add_nonzero (r s : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) (hs : Nonzero (value (denominator s) z)) :
    Nonzero (value (denominator (add r s)) z) :=
  (nonzero_congr _ _ (ScalarPolynomialArithmetic.value_multiply _ _ z)).2 (product_nonzero _ _ hr hs)

theorem evaluate_add (r s : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) (hs : Nonzero (value (denominator s) z)) :
    evaluate (add r s) z (add_nonzero r s z hr hs)≈scalarSum (evaluate r z hr) (evaluate s z hs) := by
  apply clear_unique
  have hcr := image_equiv (clear r z hr)
  have hcs := image_equiv (clear s z hs)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct _ _).property) (hright := (value _ z).property)
  change gridScalarValue (value (denominator (add r s)) z)*
    (gridScalarValue (evaluate r z hr)+gridScalarValue (evaluate s z hs))=
      gridScalarValue (value (numerator (add r s)) z)
  change gridScalarValue (value (denominator r) z)*gridScalarValue (evaluate r z hr)=
    gridScalarValue (value (numerator r) z) at hcr
  change gridScalarValue (value (denominator s) z)*gridScalarValue (evaluate s z hs)=
    gridScalarValue (value (numerator s) z) at hcs
  simp only [add,denominator,numerator,ScalarPolynomialArithmetic.value_add_image,
    ScalarPolynomialArithmetic.value_multiply_image]
  simp only [denominator,numerator] at hcr hcs
  grind only

theorem evaluate_scale (c : Scalar) (r : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) :
    evaluate (scale c r) z hr≈scalarProduct c (evaluate r z hr) := by
  apply clear_unique
  have hc := image_equiv (clear r z hr)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct _ _).property) (hright := (value _ z).property)
  change gridScalarValue (value (denominator r) z)*
    (gridScalarValue c*gridScalarValue (evaluate r z hr))=
      gridScalarValue (value (ScalarPolynomialArithmetic.scale c (numerator r)) z)
  rw [ScalarPolynomialArithmetic.value_scale_image]
  change gridScalarValue (value (denominator r) z)*gridScalarValue (evaluate r z hr)=
    gridScalarValue (value (numerator r) z) at hc
  grind only

theorem scale_agrees (c : Scalar) (r : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) (u : Scalar) (hu : evaluate r z hr≈u) :
    evaluate (scale c r) z hr≈scalarProduct u c := by
  have hc := image_equiv (evaluate_scale c r z hr)
  have he := image_equiv hu
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (evaluate (scale c r) z hr).property) (hright := (scalarProduct u c).property)
  change gridScalarValue (evaluate (scale c r) z hr)=gridScalarValue u*gridScalarValue c
  rw [hc]
  change gridScalarValue c*gridScalarValue (evaluate r z hr)=_
  rw [he]
  grind only

theorem subtract_nonzero (r s : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) (hs : Nonzero (value (denominator s) z)) :
    Nonzero (value (denominator (subtract r s)) z) := add_nonzero r _ z hr hs

theorem evaluate_subtract (r s : Fraction) (z : Scalar)
    (hr : Nonzero (value (denominator r) z)) (hs : Nonzero (value (denominator s) z)) :
    evaluate (subtract r s) z (subtract_nonzero r s z hr hs)≈gridScalarSub (evaluate r z hr) (evaluate s z hs) := by
  let c : Scalar := rationalRectangleScalar ⟨-1,0⟩
  have ha := image_equiv (evaluate_add r (scale c s) z hr hs)
  have hb := image_equiv (evaluate_scale c s z hs)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (evaluate (subtract r s) z (subtract_nonzero r s z hr hs)).property)
    (hright := (gridScalarSub (evaluate r z hr) (evaluate s z hs)).property)
  change gridScalarValue (evaluate (add r (scale c s)) z (add_nonzero r (scale c s) z hr hs))=
    gridScalarValue (gridScalarSub (evaluate r z hr) (evaluate s z hs))
  rw [ha,gridScalarValue_add,hb,gridScalarValue_sub]
  change gridScalarValue (evaluate r z hr)+(-1)*gridScalarValue (evaluate s z hs)=
    gridScalarValue (evaluate r z hr)-gridScalarValue (evaluate s z hs)
  grind only

theorem constant_nonzero (c : Scalar) (z : Scalar) : Nonzero (value (denominator (constant c)) z) :=
  (nonzero_congr _ _ (ScalarPolynomialArithmetic.value_constant oneScalar z)).2
    (RepresentedReciprocal.nonzero_of_inverse oneScalar oneScalar (one_mul_equiv _ oneScalar.property))

theorem evaluate_constant (c : Scalar) (z : Scalar) :
    evaluate (constant c) z (constant_nonzero c z)≈c := by
  apply clear_unique
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct _ _).property) (hright := (value _ z).property)
  change gridScalarValue (value [oneScalar] z)*gridScalarValue c=gridScalarValue (value [c] z)
  rw [ScalarPolynomialArithmetic.value_constant_image,ScalarPolynomialArithmetic.value_constant_image]
  change (1 : ScalarAlgebra.Value)*gridScalarValue c=gridScalarValue c
  grind only

theorem evaluate_names (r : Fraction) (z w : Scalar)
    (hz : Nonzero (value (denominator r) z)) (hw : Nonzero (value (denominator r) w)) (he : z≈w) :
    evaluate r z hz≈evaluate r w hw := (function r).eval_congr z w _ _ he

theorem evaluate_representations (r s : Fraction) (z w : Scalar)
    (hz : Nonzero (value (denominator r) z)) (hw : Nonzero (value (denominator s) w))
    (hlp : (numerator r).length=(numerator s).length)
    (hp : ∀ k, k<(numerator r).length → coefficient (numerator r) k≈coefficient (numerator s) k)
    (hlq : (denominator r).length=(denominator s).length)
    (hq : ∀ k, k<(denominator r).length → coefficient (denominator r) k≈coefficient (denominator s) k)
    (he : z≈w) : evaluate r z hz≈evaluate s w hw :=
  mul_equiv
    (RepresentedReciprocal.inverse (value (denominator r) z) hz).property
    (RepresentedReciprocal.inverse (value (denominator s) w) hw).property
    (value (numerator r) z).property (value (numerator s) w).property
    (RepresentedReciprocal.inverse_congr _ _ hz hw (value_names _ _ hlq hq z w he))
    (value_names _ _ hlp hp z w he)

end ComputableAnalysis.RiemannHilbert.ScalarPolynomialQuotients
