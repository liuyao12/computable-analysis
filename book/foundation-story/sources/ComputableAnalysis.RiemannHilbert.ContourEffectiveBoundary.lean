import ComputableAnalysis.RiemannHilbert.ContourEffectiveRefinement
import ComputableAnalysis.RiemannHilbert.ContourRibbonInvariance

/-! Quantitative tails for actual rectangle boundary quadratures. The
derivative evidence certifies the four represented edges; no interior domain
condition is imposed on a function with a pole inside the rectangle. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

structure RectangleBoundaryDerivativeBound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hd : RectangleBoundaryDomains f J) (B : QPos) : Prop where
  bottom : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle J.1 J.2.lo) z),
    Small (hf.derivative z (hd.bottom z hz)).val B.val
  top : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle J.1 J.2.hi) z),
    Small (hf.derivative z (hd.top z hz)).val B.val
  left : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle J.2 J.1.lo) z),
    Small (hf.derivative z (hd.left z hz)).val B.val
  right : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle J.2 J.1.hi) z),
    Small (hf.derivative z (hd.right z hz)).val B.val

theorem rectangleBoundaryDerivativeBound_of_rectangle (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains J z), Small (hf.derivative z (hdom z hz)).val B.val) :
    RectangleBoundaryDerivativeBound f hf J hd B where
  bottom := fun z hz => hder z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.lo)
    z Rat.le_refl Rat.le_refl Rat.le_refl hY hz)
  top := fun z hz => hder z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.hi)
    z Rat.le_refl Rat.le_refl hY Rat.le_refl hz)
  left := fun z hz => hder z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.lo)
    z Rat.le_refl hX Rat.le_refl Rat.le_refl hz)
  right := fun z hz => hder z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.hi)
    z hX Rat.le_refl Rat.le_refl Rat.le_refl hz)

def effectiveBoundaryConstant (J : QInterval × QInterval) (B : QPos) : Rat :=
  8*B.val*J.1.width*(J.1.width+1)+16*B.val*J.2.width*(J.2.width+1)

theorem effectiveBoundaryConstant_nonneg (J : QInterval × QInterval) (B : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) : 0≤effectiveBoundaryConstant J B := by
  have hx : 0≤J.1.width := by unfold QInterval.width; grind only
  have hy : 0≤J.2.width := by unfold QInterval.width; grind only
  apply Rat.add_nonneg
  · exact Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) B.property)) hx) (by grind only)
  · exact Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) B.property)) hy) (by grind only)

def effectiveBoundaryTail (J : QInterval × QInterval) (B : QPos) (n : Nat) : Rat :=
  effectiveBoundaryConstant J B*((1:Rat)/2)^n

theorem effectiveBoundaryTail_shrinks (J : QInterval × QInterval) (B : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) : ShrinksToZero (effectiveBoundaryTail J B) := by
  intro eps
  exact ⟨RationalMajorant.natRateStage (effectiveBoundaryConstant J B) eps,
    fun n hn => contour_half_rate _ (effectiveBoundaryConstant_nonneg J B hX hY) eps n hn⟩

theorem rectangleEdgeBoundary_difference (b t r l b' t' r' l' : Scalar) :
    gridScalarSub (rectangleEdgeBoundary b t r l) (rectangleEdgeBoundary b' t' r' l') ≈
    rectangleEdgeBoundary (gridScalarSub b b') (gridScalarSub t t')
      (gridScalarSub r r') (gridScalarSub l l') := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub (rectangleEdgeBoundary b t r l) (rectangleEdgeBoundary b' t' r' l')).property)
    (hright := (rectangleEdgeBoundary (gridScalarSub b b') (gridScalarSub t t')
      (gridScalarSub r r') (gridScalarSub l l')).property)
  change ((gridScalarValue b-gridScalarValue t)+(gridScalarValue r-gridScalarValue l))-
      ((gridScalarValue b'-gridScalarValue t')+(gridScalarValue r'-gridScalarValue l'))=
      ((gridScalarValue b-gridScalarValue b')-(gridScalarValue t-gridScalarValue t'))+
      ((gridScalarValue r-gridScalarValue r')-(gridScalarValue l-gridScalarValue l'))
  grind only

theorem continuousRectangleBoundary_effective_cauchy (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hder : RectangleBoundaryDerivativeBound f hf J hd B) (k n : Nat) (hkn : k≤n) :
    Small (sub (continuousRectangleBoundary f J hd n).val (continuousRectangleBoundary f J hd k).val)
      (effectiveBoundaryTail J B k) := by
  have hb := horizontalContinuousPrefix_effective_cauchy f hf J.1 J.2.lo hX hd.bottom B hder.bottom k n hkn
  have ht := horizontalContinuousPrefix_effective_cauchy f hf J.1 J.2.hi hX hd.top B hder.top k n hkn
  have hr := verticalContinuousPrefix_effective_cauchy f hf J.2 J.1.hi hY hd.right B hder.right k n hkn
  have hl := verticalContinuousPrefix_effective_cauchy f hf J.2 J.1.lo hY hd.left B hder.left k n hkn
  have hs := LocalODE.small_add (SeriesLimitLaws.small_sub hb ht) (SeriesLimitLaws.small_sub hr hl)
  have he : (4*B.val*J.1.width*(J.1.width+1)*((1:Rat)/2)^k+
      4*B.val*J.1.width*(J.1.width+1)*((1:Rat)/2)^k)+
      (8*B.val*J.2.width*(J.2.width+1)*((1:Rat)/2)^k+
      8*B.val*J.2.width*(J.2.width+1)*((1:Rat)/2)^k)=effectiveBoundaryTail J B k := by
    dsimp [effectiveBoundaryTail,effectiveBoundaryConstant]; grind only
  rw [he] at hs
  have heq := rectangleEdgeBoundary_difference
    (horizontalContinuousPrefix f J.1 J.2.lo hd.bottom n) (horizontalContinuousPrefix f J.1 J.2.hi hd.top n)
    (verticalContinuousPrefix f J.2 J.1.hi hd.right n) (verticalContinuousPrefix f J.2 J.1.lo hd.left n)
    (horizontalContinuousPrefix f J.1 J.2.lo hd.bottom k) (horizontalContinuousPrefix f J.1 J.2.hi hd.top k)
    (verticalContinuousPrefix f J.2 J.1.hi hd.right k) (verticalContinuousPrefix f J.2 J.1.lo hd.left k)
  exact Small.congr (rectangleEdgeBoundary
    (gridScalarSub (horizontalContinuousPrefix f J.1 J.2.lo hd.bottom n) (horizontalContinuousPrefix f J.1 J.2.lo hd.bottom k))
    (gridScalarSub (horizontalContinuousPrefix f J.1 J.2.hi hd.top n) (horizontalContinuousPrefix f J.1 J.2.hi hd.top k))
    (gridScalarSub (verticalContinuousPrefix f J.2 J.1.hi hd.right n) (verticalContinuousPrefix f J.2 J.1.hi hd.right k))
    (gridScalarSub (verticalContinuousPrefix f J.2 J.1.lo hd.left n) (verticalContinuousPrefix f J.2 J.1.lo hd.left k))).property
    (sub_valid (continuousRectangleBoundary f J hd n).property (continuousRectangleBoundary f J hd k).property)
    (equiv_symm heq) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
