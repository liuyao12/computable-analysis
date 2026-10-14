import ComputableAnalysis.ModularForms.RealExponentialPrefixes
import ComputableAnalysis.ModularForms.ExponentialCenterApproximation

/-! Real-coordinate lower bounds survive justified represented approximation errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem realLower_of_small_difference (f g : Scalar) (a E : Rat)
    (ha : (RealRaw.ofRat a).Le g.val.realPart) (he : Small (sub f.val g.val) E) :
    (RealRaw.ofRat (a-E)).Le f.val.realPart := by
  have hl := RealRaw.le_add_le_add ha he.1
  have hi := ComplexRaw.realPart_equiv (SeriesLimitLaws.add_difference f.val g.val f.property g.property)
  have hv := realPart_valid (add_valid g.property (sub_valid f.property g.property))
  have hb := RealRaw.le_trans hv hl
    (RealRaw.le_of_equiv hv (realPart_valid f.property) hi)
  intro n m
  have h := hb n m
  change a + -E ≤ (f.val.compute m).hi.re at h
  change a-E ≤ (f.val.compute m).hi.re
  grind only

theorem realLower_of_approximations (f : Scalar) (p : Nat → Scalar) (a : Rat)
    (e : Nat → Rat) (he : ShrinksToZero e)
    (hp : ∀ N, (RealRaw.ofRat a).Le (p N).val.realPart)
    (hc : ∀ N, Small (sub f.val (p N).val) (e N)) :
    (RealRaw.ofRat a).Le f.val.realPart := by
  intro n m
  apply RepresentedCauchySum.le_of_shrinking_error e he
  intro N
  have h := realLower_of_small_difference f (p N) a (e N) (hp N) (hc N) 0 m
  change a-e N ≤ (f.val.compute m).hi.re at h
  change a ≤ (f.val.compute m).hi.re+e N
  grind only

end ComputableAnalysis.ModularForms
