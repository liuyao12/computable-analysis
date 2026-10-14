import ComputableAnalysis.ModularForms.TauEulerLambertDifferential

/-! Exact normalized Euler differential equation with its actual Lambert coefficient. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Executable weight-two Fourier expression; transformation laws are separate. -/
def tauWeightTwoNomeValue (q : Scalar) (hq : tauEulerNomeDomain q) : Scalar :=
  ⟨sub one (scaleRat 24 (tauLambertValue q hq).val),
    sub_valid (ofQComplex_valid _) (scaleRat_valid (tauLambertValue q hq).property)⟩

/-- The actual normalized holomorphic product solves the weight-two nome equation. -/
theorem tauNormalizedEulerMap_differential_identity (q : Scalar) (hq : tauEulerNomeDomain q) :
    (mul q.val (tauNormalizedEulerMap_holomorphic.derivative q hq).val).Equiv
      (mul (tauWeightTwoNomeValue q hq).val (tauNormalizedEulerMap.eval q hq).val) := by
  let P := tauEulerNomeMap.eval q hq
  let D := tauEulerNomeDerivativeCandidate q hq
  let L := tauLambertValue q hq
  let A := tauNormalizedEulerMap_holomorphic.derivative q hq
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := A.property)
    (hright := add_valid (mul_valid D.property q.property) P.property)
    (tauNormalizedEulerMap_derivative q hq)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid q.property D.property)
    (hright := neg_valid (scaleRat_valid (mul_valid P.property L.property)))
    (tauEulerNomeDerivative_lambert_identity q hq)
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let l := ComplexRawQuotient.ofRaw L.val L.property
  let a := ComplexRawQuotient.ofRaw A.val A.property
  change a=d*Q+p at hd
  change Q*d= -(ComplexRawQuotient.scaleRat 24 (p*l)) at he
  rw [←ComplexRawQuotient.mul_scaleRat] at he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid q.property A.property)
    (hright := mul_valid (tauWeightTwoNomeValue q hq).property (tauNormalizedEulerMap.eval q hq).property)
  change Q*a=(1-ComplexRawQuotient.scaleRat 24 l)*(p*Q)
  rw [hd]
  calc Q*(d*Q+p) = (Q*d)*Q+p*Q := by grind only
       _ = (1-ComplexRawQuotient.scaleRat 24 l)*(p*Q) := by rw [he]; grind only

end ComputableAnalysis.ModularForms
