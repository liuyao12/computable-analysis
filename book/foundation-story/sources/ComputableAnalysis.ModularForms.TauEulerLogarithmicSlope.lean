import ComputableAnalysis.ModularForms.TauSeriesEulerAgreement
import ComputableAnalysis.ModularForms.ScalarNonvanishingAlgebra

/-! Executable logarithmic slope of the actual nonvanishing Euler product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Constructed division of the proved actual derivative by the Euler product. -/
def tauEulerLogarithmicSlope (q : Scalar) (hq : tauEulerNomeDomain q) : Scalar :=
  scalarProduct (tauEulerNomeDerivativeCandidate q hq)
    (RepresentedReciprocal.inverse (tauEulerNomeMap.eval q hq) (tauEulerNomeMap_nonzero q hq))

/-- The constructed logarithmic slope reconstructs the actual derivative exactly. -/
theorem tauEulerLogarithmicSlope_identity (q : Scalar) (hq : tauEulerNomeDomain q) :
    (mul (tauEulerLogarithmicSlope q hq).val (tauEulerNomeMap.eval q hq).val).Equiv
      (tauEulerNomeDerivativeCandidate q hq).val := by
  let P := tauEulerNomeMap.eval q hq
  let D := tauEulerNomeDerivativeCandidate q hq
  let I := RepresentedReciprocal.inverse P (tauEulerNomeMap_nonzero q hq)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid P.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse P (tauEulerNomeMap_nonzero q hq))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (tauEulerLogarithmicSlope q hq).property P.property) (hright := D.property)
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  change p*i=1 at hi
  change (d*i)*p=d
  grind only

/-- The normalized product is nonzero at every nonzero nome in the disk. -/
theorem tauNormalizedEulerMap_nonzero (q : Scalar) (hq : tauEulerNomeDomain q)
    (hn : NonzeroBoxSearch.Nonzero q) : NonzeroBoxSearch.Nonzero (tauNormalizedEulerMap.eval q hq) :=
  scalar_mul_nonzero (tauEulerNomeMap.eval q hq) q (tauEulerNomeMap_nonzero q hq) hn

end ComputableAnalysis.ModularForms
