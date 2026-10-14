import ComputableAnalysis.RiemannHilbert.ContourPowerKernelBounds

/-! A computed rational square around every represented point of a supplied
holomorphic function. Its whole domain and quantitative numerator and
reciprocal bounds are constructed from the supplied local data. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def effectiveLocalRadius (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : QPos :=
  divideRadius (localHolomorphicRadius f hf b hb) ⟨4,by decide +kernel⟩

def effectiveLocalRectangle (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : QInterval × QInterval :=
  let R := effectiveLocalRadius f hf b hb
  rationalCenteredRectangle (rationalPoleCenter b R 0) R.val

theorem rationalCenteredRectangle_offset_bound (c : QComplex) (z : Scalar) (R : Rat)
    (hz : representedRectangleContains (rationalCenteredRectangle c R) z) :
    Small (Centered.offset (rationalRectangleScalar c) z).val R := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hz.1 n m; change c.re-R≤(z.val.compute m).hi.re at h
    change -R≤(z.val.compute m).hi.re + -c.re; grind only
  · have h := hz.2.1 n m; change (z.val.compute n).lo.re≤c.re+R at h
    change (z.val.compute n).lo.re + -c.re≤R; grind only
  · have h := hz.2.2.1 n m; change c.im-R≤(z.val.compute m).hi.im at h
    change -R≤(z.val.compute m).hi.im + -c.im; grind only
  · have h := hz.2.2.2 n m; change (z.val.compute n).lo.im≤c.im+R at h
    change (z.val.compute n).lo.im + -c.im≤R; grind only

theorem effectiveLocalRectangle_near (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : representedRectangleContains (effectiveLocalRectangle f hf b hb) z) :
    Small (Centered.offset b z).val (localHolomorphicRadius f hf b hb).val := by
  let R := effectiveLocalRadius f hf b hb
  let c := representedPoleCenter b R 0
  have hc := (rationalPoleCenter_error b R 0).mono (poleCenterTolerance_relative R 0)
  have hs := LocalODE.small_add (rationalCenteredRectangle_offset_bound (rationalPoleCenter b R 0) z R.val hz)
    (RepresentedCauchySum.small_sub_symm _ _ _ hc)
  have he := divideRadius_identity (localHolomorphicRadius f hf b hb) (⟨4,by decide +kernel⟩ : QPos)
  change 4*R.val=(localHolomorphicRadius f hf b hb).val at he
  have hsize : R.val+R.val/64≤(localHolomorphicRadius f hf b hb).val := by have hp := R.property; grind only
  exact (Small.congr (add_valid (sub_valid z.property c.property) (sub_valid c.property b.property))
    (Centered.offset b z).property (representedDifference_split z c b) hs).mono hsize

theorem effectiveLocalRectangle_domain (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    ∀ z, representedRectangleContains (effectiveLocalRectangle f hf b hb) z → f.domain z :=
  fun z hz => localHolomorphic_domain f hf b hb z (effectiveLocalRectangle_near f hf b hb z hz)

theorem effectiveLocalRectangle_pole_inside (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    RectanglePoleInterior (effectiveLocalRectangle f hf b hb) b := by
  let R := effectiveLocalRadius f hf b hb
  let H : QPos := ⟨R.val/2,by rw [Rat.div_def]; exact Rat.mul_pos R.property (by decide +kernel)⟩
  refine ⟨H,?_⟩
  have hx (x : Rat) : x-R.val+H.val=x-R.val/2 := by dsimp [H]; grind only
  have hy (x : Rat) : x+R.val-H.val=x+R.val/2 := by dsimp [H]; grind only
  change representedRectangleContains
    (⟨(rationalPoleCenter b R 0).re-R.val+H.val,(rationalPoleCenter b R 0).re+R.val-H.val⟩,
      ⟨(rationalPoleCenter b R 0).im-R.val+H.val,(rationalPoleCenter b R 0).im+R.val-H.val⟩) b
  simpa only [rationalCenteredRectangle,hx,hy] using rationalPoleCenter_half_square b R 0

theorem effectiveLocalRectangle_value_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (hd : RectangleBoundaryDomains f (effectiveLocalRectangle f hf b hb)) :
    RectangleBoundaryValueBound f (effectiveLocalRectangle f hf b hb) hd (localHolomorphicValueBound f b hb) := by
  have hord := rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)
  exact rectangleBoundaryValueBound_of_rectangle f _ hord.1 hord.2 (effectiveLocalRectangle_domain f hf b hb)
    hd _ (fun z hz => localHolomorphic_value_bound f hf b hb z _ (effectiveLocalRectangle_near f hf b hb z hz))

theorem effectiveLocalRectangle_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (hd : RectangleBoundaryDomains f (effectiveLocalRectangle f hf b hb)) :
    RectangleBoundaryDerivativeBound f hf (effectiveLocalRectangle f hf b hb) hd (localHolomorphicDerivativeBound f hf b hb) := by
  have hord := rectanglePoleInterior_ordered _ b (effectiveLocalRectangle_pole_inside f hf b hb)
  exact rectangleBoundaryDerivativeBound_of_rectangle f hf _ hord.1 hord.2 (effectiveLocalRectangle_domain f hf b hb)
    hd _ (fun z hz => localHolomorphic_derivative_bound f hf b hb z _ (effectiveLocalRectangle_near f hf b hb z hz))

theorem effectiveLocalRectangle_reciprocal_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (hd : RectangleBoundaryDomains (ribbonPoleReciprocal b) (effectiveLocalRectangle f hf b hb)) :
    RectangleBoundaryValueBound (ribbonPoleReciprocal b) (effectiveLocalRectangle f hf b hb) hd
      (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)) :=
  rationalCenteredBoundary_pole_value_bound _ (effectiveLocalRadius f hf b hb) b
    ((rationalPoleCenter_error b _ 0).mono (poleCenterTolerance_relative _ 0)) hd

end ComputableAnalysis.RiemannHilbert.RectangularContour
