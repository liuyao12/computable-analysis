import ComputableAnalysis.RiemannHilbert.ContourEffectiveLimit

/-! Rational approximations stay in the supplied closed rectangle, including
degenerate edges. Continuous rational bounds extend to every represented point
by a proved closed-bound law, without selecting a uniform continuity modulus. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def intervalClamp (I : QInterval) (t : Rat) : Rat := max I.lo (min I.hi t)

theorem intervalClamp_mem (I : QInterval) (hI : I.lo≤I.hi) (t : Rat) :
    I.lo≤intervalClamp I t ∧ intervalClamp I t≤I.hi := by
  unfold intervalClamp; grind

theorem intervalClamp_error (I : QInterval) (x y t E : Rat) (hE : 0≤E) (hxl : I.lo≤x) (hyu : y≤I.hi)
    (hl : -E≤x + -t) (hu : y + -t≤E) : -E≤x + -intervalClamp I t ∧ y + -intervalClamp I t≤E := by
  unfold intervalClamp; grind

def rectangleRationalApproximation (J : QInterval × QInterval) (z : Scalar) (eps : QPos) : QComplex :=
  let c := (z.val.compute (PrecisionSearch.stage z.val z.property eps)).center
  ⟨intervalClamp J.1 c.re,intervalClamp J.2 c.im⟩

theorem rectangleRationalApproximation_mem (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi)
    (hY : J.2.lo≤J.2.hi) (z : Scalar) (eps : QPos) :
    rationalRectangleContains J (rectangleRationalApproximation J z eps) :=
  let hx := intervalClamp_mem J.1 hX _
  let hy := intervalClamp_mem J.2 hY _
  ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem rectangleRationalApproximation_error (J : QInterval × QInterval) (z : Scalar)
    (hz : representedRectangleContains J z) (eps : QPos) :
    Small (sub z.val (ofQComplex (rectangleRationalApproximation J z eps))) eps.val := by
  let c := (z.val.compute (PrecisionSearch.stage z.val z.property eps)).center
  have hn := PrecisionSearch.stage_spec z.val z.property eps
  have hs := BoxApproximation.center_error z _ eps.val (Rat.le_of_lt eps.property) hn.1 hn.2
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · change -eps.val≤(z.val.compute m).hi.re + -intervalClamp J.1 c.re
    have h := intervalClamp_error J.1 (z.val.compute m).hi.re (z.val.compute m).lo.re c.re eps.val (Rat.le_of_lt eps.property)
      (hz.1 n m) (hz.2.1 m n) (hs.1 n m) (hs.2.1 m n)
    exact h.1
  · change (z.val.compute n).lo.re + -intervalClamp J.1 c.re≤eps.val
    have h := intervalClamp_error J.1 (z.val.compute n).hi.re (z.val.compute n).lo.re c.re eps.val (Rat.le_of_lt eps.property)
      (hz.1 m n) (hz.2.1 n m) (hs.1 m n) (hs.2.1 n m)
    exact h.2
  · change -eps.val≤(z.val.compute m).hi.im + -intervalClamp J.2 c.im
    have h := intervalClamp_error J.2 (z.val.compute m).hi.im (z.val.compute m).lo.im c.im eps.val (Rat.le_of_lt eps.property)
      (hz.2.2.1 n m) (hz.2.2.2 m n) (hs.2.2.1 n m) (hs.2.2.2 m n)
    exact h.1
  · change (z.val.compute n).lo.im + -intervalClamp J.2 c.im≤eps.val
    have h := intervalClamp_error J.2 (z.val.compute n).hi.im (z.val.compute n).lo.im c.im eps.val (Rat.le_of_lt eps.property)
      (hz.2.2.1 m n) (hz.2.2.2 n m) (hs.2.2.1 m n) (hs.2.2.2 n m)
    exact h.2

theorem continuousRectangle_rational_bound_extends (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (B : Rat)
    (hB : ∀ q : QComplex, rationalRectangleContains J q → Small (continuousRectangleSample f J hdom q).val B)
    (z : Scalar) (hz : representedRectangleContains J z) : Small (f.eval z (hdom z hz)).val B := by
  apply SeriesLimitLaws.small_closed _ B (fun n => (RepresentedCauchySum.error n).val)
    RepresentedCauchySum.error_shrinks
  intro n
  let eps := RepresentedCauchySum.error n
  let eta := hc.delta z (hdom z hz) eps
  let q := rectangleRationalApproximation J z eta
  have hq := rectangleRationalApproximation_mem J hX hY z eta
  have hqr := rationalRectangle_represented_mem J q hq
  let v := f.eval (rationalRectangleScalar q) (hdom _ hqr)
  have hv : Small v.val B := Small.congr (continuousRectangleSample f J hdom q).property v.property
    (continuousRectangleSample_agreement f J hdom q hq (hdom _ hqr)) (hB q hq)
  have hd := RepresentedCauchySum.small_sub_symm _ _ _ (rectangleRationalApproximation_error J z hz eta)
  have hs := hc.estimate z (hdom z hz) eps (rationalRectangleScalar q) (hdom _ hqr) hd
  have hb := LocalODE.small_add hv (RepresentedCauchySum.small_sub_symm _ _ _ hs)
  exact Small.congr (add_valid v.property (sub_valid (f.eval z (hdom z hz)).property v.property))
    (f.eval z (hdom z hz)).property (SeriesLimitLaws.add_difference _ _ (f.eval z (hdom z hz)).property v.property) hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
