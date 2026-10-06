import ComputableAnalysis.RiemannHilbert.RelativeLogarithm
import ComputableAnalysis.RiemannHilbert.LocalLogarithmExponential

/-! Exact exponential semantics of the constructed normalized branch at
every nonzero represented center. The chart and normalization are computed
from the center; no logarithm value is supplied or assumed. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory NonzeroBoxSearch

theorem exponential_value (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    (LocalLogarithm.exponential ((function c hc).eval z hz)).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val z.val) := by
  have he : (LocalLogarithm.onePlus (point c hc z)).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val z.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (LocalLogarithm.onePlus (point c hc z)).property)
      (hright := mul_valid (RepresentedReciprocal.inverse c hc).property z.property)
    let C := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val
      (RepresentedReciprocal.inverse c hc).property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 1+(-1+C*Z)=C*Z
    grind only
  exact equiv_trans (LocalLogarithm.exponential ((function c hc).eval z hz)).property
    (LocalLogarithm.onePlus (point c hc z)).property
    (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)
    (LocalLogarithm.exponential_log (point c hc z) hz) he

theorem center_times_exponential (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    (mul c.val (LocalLogarithm.exponential ((function c hc).eval z hz)).val).Equiv z.val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property (RepresentedReciprocal.inverse c hc).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse c hc)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (LocalLogarithm.exponential ((function c hc).eval z hz)).property)
    (hright := mul_valid (RepresentedReciprocal.inverse c hc).property z.property) (exponential_value c hc z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid c.property (LocalLogarithm.exponential ((function c hc).eval z hz)).property) (hright := z.property)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let E := ComplexRawQuotient.ofRaw (LocalLogarithm.exponential ((function c hc).eval z hz)).val
    (LocalLogarithm.exponential ((function c hc).eval z hz)).property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change C*R=1 at hi
  change E=R*Z at he
  change C*E=Z
  grind only

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm
