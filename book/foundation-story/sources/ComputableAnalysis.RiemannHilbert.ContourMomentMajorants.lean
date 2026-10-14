import ComputableAnalysis.RiemannHilbert.ContourConstructedMomentInvariance
import ComputableAnalysis.RiemannHilbert.ContourBoundaryScaling

/-! Geometric coefficient majorants for the constructed Cauchy moments.
Uniform bounds are first proved for the actual boundary computations, then
passed to their represented limits. No coefficient bound is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

/-- A uniform bound survives convergence, without extracting a modulus. -/
theorem converge_bounded (p : Nat → Scalar) (a : Scalar) (hp : Converges p a)
    (B : Rat) (hb : ∀ n, Small (p n).val B) : Small a.val B := by
  apply SeriesLimitLaws.small_closed a.val B (fun n => (RepresentedCauchySum.error n).val)
    RepresentedCauchySum.error_shrinks
  intro n
  obtain ⟨N,hN⟩ := hp (RepresentedCauchySum.error n)
  have hclose := RepresentedCauchySum.small_sub_symm _ _ _ (hN N (Nat.le_refl _))
  exact Small.congr (add_valid (p N).property (sub_valid a.property (p N).property)) a.property
    (SeriesLimitLaws.add_difference a.val (p N).val a.property (p N).property)
    (LocalODE.small_add (hb N) hclose)

theorem rectangleBoundaryValueBound_rational (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (B : QPos) (hB : RectangleBoundaryValueBound f J hd B)
    (q : QComplex) (hq : rationalRectangleBoundaryContains J q) (hz : f.domain (rationalRectangleScalar q)) :
    Small (f.eval (rationalRectangleScalar q) hz).val B.val := by
  rcases hq with hq|hq|hq|hq
  · exact hB.bottom _ (rationalRectangle_represented_mem _ q hq)
  · exact hB.top _ (rationalRectangle_represented_mem _ q hq)
  · exact hB.left _ (rationalRectangle_represented_mem _ q hq)
  · exact hB.right _ (rationalRectangle_represented_mem _ q hq)

theorem continuousRectangleBoundary_value_bound (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (hd : RectangleBoundaryDomains f J)
    (B : QPos) (hB : RectangleBoundaryValueBound f J hd B) (n : Nat) :
    Small (continuousRectangleBoundary f J hd n).val (4*(J.1.width+J.2.width)*B.val) := by
  have hs := rectangleGridBoundary_bound (rectangleBoundarySample f J hd) J (2^n) hX hY
    (Nat.two_pow_pos n) B.val (Rat.le_of_lt B.property) (by
      intro q hq
      let hz := rectangleBoundaryDomains_rational f J hd q hq
      exact Small.congr (f.eval _ hz).property (rectangleBoundarySample f J hd q).property
        (equiv_symm (rectangleBoundarySample_value f J hd q hq hz))
        (rectangleBoundaryValueBound_rational f J hd B hB q hq hz))
  exact Small.congr (rectangleGridBoundary _ J (2^n)).property (continuousRectangleBoundary f J hd n).property
    (rectangleBoundarySample_edges f J hX hY hd n) hs

theorem powerKernelValueBound_formula (F U : QPos) (m : Nat) :
    (powerKernelValueBound F U m).val=F.val*(2*U.val)^m := by
  induction m with
  | zero => simp only [powerKernelValueBound,Rat.pow_zero,Rat.mul_one]
  | succ m ih =>
    change 2*(powerKernelValueBound F U m).val*U.val=F.val*(2*U.val)^(m+1)
    rw [ih,Rat.pow_succ]; grind only

theorem ribbonCauchyPowerBoundary_value_bound (f : DomainFunctions.Map)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b)
    (hdf : RectangleBoundaryDomains f J) (hdR : RectangleBoundaryDomains (ribbonPoleReciprocal b) J)
    (F U : QPos) (hF : RectangleBoundaryValueBound f J hdf F)
    (hU : RectangleBoundaryValueBound (ribbonPoleReciprocal b) J hdR U) (m : Nat) :
    RectangleBoundaryValueBound (ribbonCauchyPowerKernel f b m) J
      (ribbonCauchyPowerBoundaryDomains f J hdom b hb m) (powerKernelValueBound F U m) where
  bottom := fun z hz => ribbonCauchyPowerKernel_value_bound f b z _ F U (hF.bottom z hz) (hU.bottom z hz) m
  top := fun z hz => ribbonCauchyPowerKernel_value_bound f b z _ F U (hF.top z hz) (hU.top z hz) m
  left := fun z hz => ribbonCauchyPowerKernel_value_bound f b z _ F U (hF.left z hz) (hU.left z hz) m
  right := fun z hz => ribbonCauchyPowerKernel_value_bound f b z _ F U (hF.right z hz) (hU.right z hz) m

def localCauchyCoefficientRate (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : QPos :=
  ⟨2*(centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).val,
    Rat.mul_pos (by decide +kernel) (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).property⟩

def localCauchyCoefficientBound (f : DomainFunctions.Map) (b : Scalar) (hb : f.domain b) : QPos :=
  ⟨512*scalarBound inverseGeometricPeriod*(localHolomorphicValueBound f b hb).val,
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod))
      (localHolomorphicValueBound f b hb).property⟩

theorem effectiveLocalPowerValue_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar)
    (hb : f.domain b) (m : Nat) :
    Small (effectiveLocalPowerValue f hf b hb m).val
      (16*(effectiveLocalRadius f hf b hb).val*(localHolomorphicValueBound f b hb).val*
        (localCauchyCoefficientRate f hf b hb).val^m) := by
  let J := effectiveLocalRectangle f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  have ho := rectanglePoleInterior_ordered J b hp
  let hdF := rectangleBoundaryDomains_of_rectangle f J ho.1 ho.2 (effectiveLocalRectangle_domain f hf b hb)
  let hdR := rectanglePoleReciprocalBoundaryDomains J b hp
  have hB := ribbonCauchyPowerBoundary_value_bound f J (effectiveLocalRectangle_domain f hf b hb) b hp hdF hdR
    (localHolomorphicValueBound f b hb) (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb))
    (effectiveLocalRectangle_value_bound f hf b hb hdF) (effectiveLocalRectangle_reciprocal_bound f hf b hb hdR) m
  apply converge_bounded _ _ (effectiveLocalPowerValue_converges f hf b hb m)
  intro n
  have hs := continuousRectangleBoundary_value_bound _ J ho.1 ho.2 _ _ hB n
  have he : 4*(J.1.width+J.2.width)*
      (powerKernelValueBound (localHolomorphicValueBound f b hb)
        (centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)) m).val=
      16*(effectiveLocalRadius f hf b hb).val*(localHolomorphicValueBound f b hb).val*
        (localCauchyCoefficientRate f hf b hb).val^m := by
    rw [powerKernelValueBound_formula]
    dsimp [J,effectiveLocalRectangle,rationalCenteredRectangle,QInterval.width,localCauchyCoefficientRate]
    grind only
  rw [he] at hs
  exact hs

/-- The actual constructed coefficients have a geometric growth bound. -/
theorem localCauchyMoment_majorant (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar)
    (hb : f.domain b) (k : Nat) :
    Small (localCauchyMoment f hf b hb k).val
      ((localCauchyCoefficientBound f b hb).val*(localCauchyCoefficientRate f hf b hb).val^k) := by
  have hs := Small.mul inverseGeometricPeriod.property (effectiveLocalPowerValue f hf b hb (k+1)).property
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod))
    (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel)
      (effectiveLocalRadius f hf b hb).property) (localHolomorphicValueBound f b hb).property)
      (Rat.pow_pos (localCauchyCoefficientRate f hf b hb).property)))
    (scalar_small inverseGeometricPeriod) (effectiveLocalPowerValue_bound f hf b hb (k+1))
  have hr : (effectiveLocalRadius f hf b hb).val*(localCauchyCoefficientRate f hf b hb).val=16 := by
    have hn := Rat.ne_of_gt (effectiveLocalRadius f hf b hb).property
    dsimp [localCauchyCoefficientRate,centeredBoundaryReciprocalBound]
    have hc := Rat.div_mul_cancel (a := (8 : Rat)) hn
    grind only
  have he : 2*scalarBound inverseGeometricPeriod*
      (16*(effectiveLocalRadius f hf b hb).val*(localHolomorphicValueBound f b hb).val*
        (localCauchyCoefficientRate f hf b hb).val^(k+1))=
      (localCauchyCoefficientBound f b hb).val*(localCauchyCoefficientRate f hf b hb).val^k := by
    rw [Rat.pow_succ]; dsimp [localCauchyCoefficientBound]; grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
