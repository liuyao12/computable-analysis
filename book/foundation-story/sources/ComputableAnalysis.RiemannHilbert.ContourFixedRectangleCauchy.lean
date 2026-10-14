import ComputableAnalysis.RiemannHilbert.ContourFixedRectangleGeometry
import ComputableAnalysis.RiemannHilbert.ContourDisplacedCauchy

/-! On one supplied rational rectangle, every represented interior pole has
the actual Cauchy boundary limit. The small hole is fixed before mesh refinement. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem rationalPoleHole_boundary (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar) (D R : QPos)
    (hb : representedRectangleContains (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b)
    (m : Nat) (hR : 3*R.val≤D.val)
    (hframe : ∀ z, frameDomain R z → f.domain (Centered.translate (representedPoleCenter b R m) z))
    (n : Nat) :
    ribbonInnerBoundary (ribbonCauchyKernel f b) (rationalPoleHoleRibbon J b D R hb m hR)
      (ribbonCauchyKernel_domain f _ (ribbonDomain_of_outer f _ hdom) b
        (rationalPoleHole_inside J b D R hb m hR)) (n+1)≈
      displacedInnerPrefix f b (representedPoleCenter b R m) R hframe
        ((rationalPoleCenter_error b R m).mono (poleCenterTolerance_relative R m)) (2^n) :=
  rationalCenteredRectangle_cauchy_boundary f b (rationalPoleCenter b R m) R _ hframe _ n

theorem fixedRectangleCauchyContour_rectangular (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) :
    Converges (fixedRectangleCauchyContour f J hdom b hb)
      (scalarProduct (f.eval b (hdom b (rectanglePoleInterior_mem J b hb))) rectangularPeriod) := by
  intro eps
  obtain ⟨D,hmargin⟩ := hb
  let ha := hdom b (rectanglePoleInterior_mem J b ⟨D,hmargin⟩)
  let A := f.eval b ha
  let eta := divideRadius eps (⟨4,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨128,by decide +kernel⟩ : QPos)
  let m := max (max (displacedContourErrorStage f hf b ha D)
    (displacedContourErrorStage f hf b ha (hf.continuous.delta b ha theta)))
    (RationalMajorant.natRateStage (64*scalarBound A) eta)
  let R := shrinkingContourRadius f hf b ha m
  have hmD : displacedContourErrorStage f hf b ha D≤m := by dsimp [m]; omega
  have hmC : displacedContourErrorStage f hf b ha (hf.continuous.delta b ha theta)≤m := by dsimp [m]; omega
  have hmH : RationalMajorant.natRateStage (64*scalarBound A) eta≤m := by dsimp [m]; omega
  have hR : 3*R.val≤D.val := displacedContourErrorStage_spec f hf b ha D m hmD
  let G := rationalPoleHoleRibbon J b D R hmargin m hR
  let hd := ribbonCauchyKernel_domain f G (ribbonDomain_of_outer f G hdom) b
    (rationalPoleHole_inside J b D R hmargin m hR)
  obtain ⟨N,hN⟩ := ribbonDifference_eventual_zero (ribbonCauchyKernel f b)
    (ribbonCauchyKernel_holomorphic f hf b) G hd eta
  let B := RationalMajorant.natRateStage (32*scalarBound A) eta
  refine ⟨max N B+1, ?_⟩
  intro k hk
  let n := k-1
  have hnk : n+1=k := by dsimp [n]; omega
  have hnN : N≤n+1 := by dsimp [n]; omega
  have hnB : B≤n := by dsimp [n]; omega
  let X := fixedRectangleCauchyContour f J hdom b ⟨D,hmargin⟩ k
  let Y := ribbonInnerBoundary (ribbonCauchyKernel f b) G hd (n+1)
  let P := reciprocalInnerPrefix R (2^n)
  let Z := scalarProduct A P
  let U := scalarProduct A rectangularPeriod
  have hXY := hN (n+1) hnN
  have houter : ribbonOuterBoundary (ribbonCauchyKernel f b) G hd (n+1)≈X := by
    rw [hnk]
    exact equiv_refl _ X.property
  have hXY' := Small.congr (ribbonDifference (ribbonCauchyKernel f b) G hd (n+1)).property
    (sub_valid X.property Y.property)
    (FunctionTheory.sub_congr houter (equiv_refl _ Y.property)) hXY
  have hnum := displacedInnerPrefix_center_estimate f b (displacedLocalCenter f hf b ha m) ha R
    (displacedLocalFrame_domain f hf b ha m) (poleCenterTolerance R m).val
    (Rat.le_of_lt (poleCenterTolerance R m).property) (poleCenterTolerance_relative R m)
    (rationalPoleCenter_error b R m) theta
    (displacedLocalFrame_numerator_close f hf b ha theta m hmC) (2^n) (Nat.two_pow_pos n)
  have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have htheta : 128*theta.val=eta.val := divideRadius_identity eta (⟨128,by decide +kernel⟩ : QPos)
  have he : 128*theta.val+4096*scalarBound A*(poleCenterTolerance R m).val/R.val=
      eta.val+64*scalarBound A*((1:Rat)/2)^m := by
    simp only [poleCenterTolerance,Rat.div_def]
    grind only
  rw [he] at hnum
  have hcenter := contour_half_rate (64*scalarBound A)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (scalarBound_pos A))) eta m hmH
  have hYZ : Small (sub Y.val Z.val) (eta.val+eta.val) := by
    apply Small.congr (sub_valid (displacedInnerPrefix f b (displacedLocalCenter f hf b ha m) R
      (displacedLocalFrame_domain f hf b ha m) _ (2^n)).property Z.property)
      (sub_valid Y.property Z.property)
    · exact FunctionTheory.sub_congr (Setoid.symm (rationalPoleHole_boundary f J hdom b D R hmargin m hR
        (displacedLocalFrame_domain f hf b ha m) n)) (equiv_refl _ Z.property)
    · exact hnum.mono (by grind only)
  have hperiod := reciprocalInnerPrefix_geometric_error R n
  have hpower : 0≤((1:Rat)/2)^n := Rat.le_of_lt (Rat.pow_pos (by decide +kernel))
  have hmul := Small.mul A.property (sub_valid P.property rectangularPeriod.property)
    (Rat.le_of_lt (scalarBound_pos A)) (Rat.mul_nonneg (by decide +kernel) hpower) (scalar_small A) hperiod
  have hrate := contour_half_rate (32*scalarBound A)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (scalarBound_pos A))) eta n hnB
  have hsize : 2*scalarBound A*(16*((1:Rat)/2)^n)=32*scalarBound A*((1:Rat)/2)^n := by grind only
  rw [hsize] at hmul
  have hZU := Small.congr (mul_valid A.property (sub_valid P.property rectangularPeriod.property))
    (sub_valid Z.property U.property) (equiv_symm (product_difference_left A P rectangularPeriod)) (hmul.mono hrate)
  have hs := LocalODE.small_add (LocalODE.small_add hXY' hYZ) hZU
  have heps : (eta.val+(eta.val+eta.val))+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨4,by decide +kernel⟩ : QPos)
    change 4*eta.val=eps.val at h
    grind only
  rw [heps] at hs
  exact Small.congr
    (add_valid (add_valid (sub_valid X.property Y.property) (sub_valid Y.property Z.property))
      (sub_valid Z.property U.property)) (sub_valid X.property U.property)
    (equiv_symm (SeriesLimitLaws.difference_via X.val U.val Y.val Z.val X.property U.property Y.property Z.property)) hs

theorem fixedRectangleCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) :
    Converges (fixedRectangleCauchyContour f J hdom b hb)
      (localCauchyValue f b (hdom b (rectanglePoleInterior_mem J b hb))) := by
  apply converge_limit_congr _ _ _ (fixedRectangleCauchyContour_rectangular f hf J hdom b hb)
  exact mul_equiv (f.eval b _).property (f.eval b _).property rectangularPeriod.property
    geometricPeriod.property (equiv_refl _ (f.eval b _).property) rectangularPeriod_geometric

theorem fixedRectangleCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (u : Scalar)
    (hu : Converges (fixedRectangleCauchyContour f J hdom b hb) u) :
    u≈localCauchyValue f b (hdom b (rectanglePoleInterior_mem J b hb)) :=
  converge_unique _ _ _ hu (fixedRectangleCauchyContour_converges f hf J hdom b hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour
