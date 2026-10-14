import ComputableAnalysis.RiemannHilbert.ContourIntervalCauchy
import ComputableAnalysis.RiemannHilbert.ContourIntervalOscillation

/-! Cauchy and tag-agreement laws for actual continuous edge quadratures.
Vertical weights include the actual imaginary velocity. No limit is assumed
for the Cauchy law, and no abstract completion constructs one. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def horizontalContinuousPrefix (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (n : Nat) : Scalar := intervalGridPrefix (horizontalIntervalSample f I y hdom) I (2^n)

def verticalContinuousPrefix (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (n : Nat) : Scalar := scalarProduct (rationalRectangleScalar ⟨0,1⟩)
      (intervalGridPrefix (verticalIntervalSample f I x hdom) I (2^n))

theorem intervalGridProductPrefix_dyadic_cauchy (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (a : Scalar) (eps : QPos) :
    ∃ N, ∀ n m, N≤n → N≤m → Small (sub
      (scalarProduct a (intervalGridPrefix sample I (2^n))).val
      (scalarProduct a (intervalGridPrefix sample I (2^m))).val) eps.val := by
  let D : QPos := ⟨2*scalarBound a,Rat.mul_pos (by decide +kernel) (scalarBound_pos a)⟩
  let eta := divideRadius eps D
  obtain ⟨N,hN⟩ := intervalGridPrefix_dyadic_cauchy sample I hI hosc eta
  refine ⟨N, ?_⟩
  intro n m hn hm
  let p := intervalGridPrefix sample I (2^n)
  let q := intervalGridPrefix sample I (2^m)
  have hs := Small.mul a.property (sub_valid p.property q.property)
    (Rat.le_of_lt (scalarBound_pos a)) (Rat.le_of_lt eta.property) (scalar_small a) (hN n m hn hm)
  have he := divideRadius_identity eps D
  change (2*scalarBound a)*eta.val=eps.val at he
  have he' : 2*scalarBound a*eta.val=eps.val := he
  rw [he'] at hs
  exact Small.congr (mul_valid a.property (sub_valid p.property q.property))
    (sub_valid (scalarProduct a p).property (scalarProduct a q).property)
    (equiv_symm (product_difference_left a p q)) hs

theorem horizontalContinuousPrefix_cauchy (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I : QInterval) (y : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (eps : QPos) : ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (horizontalContinuousPrefix f I y hdom n).val
        (horizontalContinuousPrefix f I y hdom m).val) eps.val :=
  intervalGridPrefix_dyadic_cauchy _ I hI (horizontalIntervalSample_oscillation f hc I y hI hdom) eps

theorem verticalContinuousPrefix_cauchy (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I : QInterval) (x : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (eps : QPos) : ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (verticalContinuousPrefix f I x hdom n).val
        (verticalContinuousPrefix f I x hdom m).val) eps.val :=
  intervalGridProductPrefix_dyadic_cauchy _ I hI (verticalIntervalSample_oscillation f hc I x hI hdom) _ eps

theorem horizontalContinuousPrefix_tags_agree (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I : QInterval) (y : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (eps : QPos) : ∃ N, ∀ n, N≤n → ∀ tag other : Nat → Rat,
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤tag j ∧ tag j≤(intervalGridCell I (2^n) j).hi) →
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤other j ∧ other j≤(intervalGridCell I (2^n) j).hi) →
      Small (sub (intervalGridTaggedPrefix (horizontalIntervalSample f I y hdom) I (2^n) tag).val
        (intervalGridTaggedPrefix (horizontalIntervalSample f I y hdom) I (2^n) other).val) eps.val :=
  intervalGridTaggedPrefix_eventual_agreement _ I hI (horizontalIntervalSample_oscillation f hc I y hI hdom) eps

theorem verticalContinuousSample_tags_agree (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I : QInterval) (x : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (eps : QPos) : ∃ N, ∀ n, N≤n → ∀ tag other : Nat → Rat,
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤tag j ∧ tag j≤(intervalGridCell I (2^n) j).hi) →
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤other j ∧ other j≤(intervalGridCell I (2^n) j).hi) →
      Small (sub (intervalGridTaggedPrefix (verticalIntervalSample f I x hdom) I (2^n) tag).val
        (intervalGridTaggedPrefix (verticalIntervalSample f I x hdom) I (2^n) other).val) eps.val :=
  intervalGridTaggedPrefix_eventual_agreement _ I hI (verticalIntervalSample_oscillation f hc I x hI hdom) eps

end ComputableAnalysis.RiemannHilbert.RectangularContour
