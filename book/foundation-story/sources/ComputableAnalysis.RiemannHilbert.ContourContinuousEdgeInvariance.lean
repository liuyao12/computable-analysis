import ComputableAnalysis.RiemannHilbert.ContourContinuousEdgeAgreement

/-! Edge quadratures respect equivalent represented function values.
The comparison is required only at actual points of the supplied edge. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem continuousRectangleSample_congr (f g : DomainFunctions.Map) (J : QInterval × QInterval)
    (hf : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hg : ∀ z : Scalar, representedRectangleContains J z → g.domain z)
    (he : ∀ z (hz : representedRectangleContains J z), f.eval z (hf z hz) ≈ g.eval z (hg z hz))
    (q : QComplex) (hq : rationalRectangleContains J q) :
    continuousRectangleSample f J hf q ≈ continuousRectangleSample g J hg q := by
  have hz := rationalRectangle_represented_mem J q hq
  exact Setoid.trans (continuousRectangleSample_agreement f J hf q hq (hf _ hz))
    (Setoid.trans (he _ hz) (Setoid.symm (continuousRectangleSample_agreement g J hg q hq (hg _ hz))))

theorem intervalGridTaggedPrefix_congr (f g : Rat → Scalar) (I : QInterval) (M : Nat) (tag : Nat → Rat)
    (he : ∀ j, j<M → f (tag j) ≈ g (tag j)) :
    intervalGridTaggedPrefix f I M tag ≈ intervalGridTaggedPrefix g I M tag :=
  gridScalarSum_congr_bounded M _ _ (fun j hj => scaleRat_equiv (he j hj))

theorem intervalGridPrefix_congr (f g : Rat → Scalar) (I : QInterval) (M : Nat)
    (he : ∀ j, j<M → f (intervalGridTag I M j) ≈ g (intervalGridTag I M j)) :
    intervalGridPrefix f I M ≈ intervalGridPrefix g I M :=
  intervalGridTaggedPrefix_congr f g I M _ he

theorem horizontalContinuousPrefix_congr (f g : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hI : I.lo≤I.hi)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (hg : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → g.domain z)
    (he : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle I y) z),
      f.eval z (hf z hz) ≈ g.eval z (hg z hz)) (n : Nat) :
    horizontalContinuousPrefix f I y hf n ≈ horizontalContinuousPrefix g I y hg n := by
  apply intervalGridPrefix_congr _ _ I (2^n)
  intro j hj
  have hmem := rectangleGridHorizontalPoint_mem (horizontalIntervalRectangle I y) (2^n) j 0
    hI Rat.le_refl (Nat.two_pow_pos n) hj (Nat.zero_le _)
  rw [intervalGridTag_horizontal_point] at hmem
  exact continuousRectangleSample_congr f g _ hf hg he _ hmem

theorem verticalContinuousPrefix_congr (f g : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hI : I.lo≤I.hi)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (hg : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → g.domain z)
    (he : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle I x) z),
      f.eval z (hf z hz) ≈ g.eval z (hg z hz)) (n : Nat) :
    verticalContinuousPrefix f I x hf n ≈ verticalContinuousPrefix g I x hg n := by
  apply mul_equiv (ofQComplex_valid _) (ofQComplex_valid _)
    (intervalGridPrefix (verticalIntervalSample f I x hf) I (2^n)).property
    (intervalGridPrefix (verticalIntervalSample g I x hg) I (2^n)).property (equiv_refl _ (ofQComplex_valid _))
  apply intervalGridPrefix_congr _ _ I (2^n)
  intro j hj
  have hmem := rectangleGridVerticalPoint_mem (verticalIntervalRectangle I x) (2^n) 0 j
    Rat.le_refl hI (Nat.two_pow_pos n) (Nat.zero_le _) hj
  rw [intervalGridTag_vertical_point] at hmem
  exact continuousRectangleSample_congr f g _ hf hg he _ hmem

end ComputableAnalysis.RiemannHilbert.RectangularContour
