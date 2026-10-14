import ComputableAnalysis.RiemannHilbert.ContourContinuousCover
import ComputableAnalysis.RiemannHilbert.ContourBoundaryAgreement
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Uniform oscillation on sufficiently small actual dyadic cells, derived
from represented value continuity. The depth is existential inside Prop. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem representedRectangle_small (J : QInterval × QInterval) (z : Scalar) (B : Rat)
    (hxl : -B≤J.1.lo) (hxu : J.1.hi≤B) (hyl : -B≤J.2.lo) (hyu : J.2.hi≤B)
    (hz : representedRectangleContains J z) : Small z.val B :=
  ⟨fun n m => Rat.le_trans hxl (hz.1 n m),fun n m => Rat.le_trans (hz.2.1 n m) hxu,
    fun n m => Rat.le_trans hyl (hz.2.2.1 n m),fun n m => Rat.le_trans (hz.2.2.2 n m) hyu⟩

def continuousRectangleSample (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (q : QComplex) : Scalar :=
  if hq : rationalRectangleContains J q then
    f.eval (rationalRectangleScalar q) (hdom _ (rationalRectangle_represented_mem J q hq))
  else rationalRectangleScalar QComplex.zero

theorem continuousRectangleSample_agreement (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (q : QComplex) (hq : rationalRectangleContains J q) (hd : f.domain (rationalRectangleScalar q)) :
    continuousRectangleSample f J hdom q ≈ f.eval (rationalRectangleScalar q) hd := by
  rw [continuousRectangleSample,dif_pos hq]
  exact equiv_refl _ (f.eval (rationalRectangleScalar q) hd).property

theorem representedDifference_common_anchor (x y a : Scalar) :
    (sub (sub x.val a.val) (sub y.val a.val)).Equiv (sub x.val y.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (sub_valid x.property a.property) (sub_valid y.property a.property))
    (hright := sub_valid x.property y.property)
  let X := gridScalarValue x
  let Y := gridScalarValue y
  let A := gridScalarValue a
  change (X-A)-(Y-A)=X-Y
  grind only

theorem continuousRectangle_cell_oscillation (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ j k, j<2^n → k<2^n → ∀ p q : QComplex,
      rationalRectangleContains (rectangleGridCell J (2^n) j k) p →
      rationalRectangleContains (rectangleGridCell J (2^n) j k) q →
      Small (sub (continuousRectangleSample f J hdom q).val
        (continuousRectangleSample f J hdom p).val) eps.val := by
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨N,hN⟩ := valueRectangleNeighborhood_uniform_depth f hc eta J hX hY
    (domain_value_rectangle_cover f hc eta J hX hY hdom)
  refine ⟨N, ?_⟩
  intro n hn j k hj hk p q hp hq
  obtain ⟨choice,he⟩ := rectangleGridCell_bisection J n j k hj hk
  obtain ⟨a,ha,hnear⟩ := hN choice n hn
  rw [he] at hnear
  have hpJ := rectangleGridCell_contains_initial J (2^n) j k (Nat.two_pow_pos n) hj hk hX hY p hp
  have hqJ := rectangleGridCell_contains_initial J (2^n) j k (Nat.two_pow_pos n) hj hk hX hY q hq
  have hP := hdom _ (rationalRectangle_represented_mem J p hpJ)
  have hQ := hdom _ (rationalRectangle_represented_mem J q hqJ)
  have hs := SeriesLimitLaws.small_sub
    (hc.estimate a ha eta _ hQ (hnear q hq))
    (hc.estimate a ha eta _ hP (hnear p hp))
  have hsum : eta.val+eta.val=eps.val := by
    have hd := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at hd
    grind only
  rw [hsum] at hs
  have hv := Small.congr
    (sub_valid (sub_valid (f.eval _ hQ).property (f.eval a ha).property)
      (sub_valid (f.eval _ hP).property (f.eval a ha).property))
    (sub_valid (f.eval _ hQ).property (f.eval _ hP).property)
    (representedDifference_common_anchor (f.eval _ hQ) (f.eval _ hP) (f.eval a ha)) hs
  exact Small.congr (sub_valid (f.eval _ hQ).property (f.eval _ hP).property)
    (sub_valid (continuousRectangleSample f J hdom q).property (continuousRectangleSample f J hdom p).property)
    (FunctionTheory.sub_congr
      (equiv_symm (continuousRectangleSample_agreement f J hdom q hqJ hQ))
      (equiv_symm (continuousRectangleSample_agreement f J hdom p hpJ hP))) hv

end ComputableAnalysis.RiemannHilbert.RectangularContour
