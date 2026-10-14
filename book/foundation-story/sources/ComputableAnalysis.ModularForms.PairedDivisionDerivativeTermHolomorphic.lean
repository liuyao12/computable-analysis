import ComputableAnalysis.ModularForms.PairedRegularDivisionDerivative

/-! Holomorphic derivative terms for the actual regular-division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def doubledInput : DomainFunctions.Map :=
  sumOn (affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
    (affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) (fun _ _ => trivial)

private def doubledInput_holomorphic : Holomorphic doubledInput :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).sumOn
    (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) (fun _ _ => trivial)

private def derivativeHalfMap (n : Nat) : DomainFunctions.Map :=
  productOn (negate (productOn (pairedSmallDiskLiteralInverseMap n)
    (pairedSmallDiskLiteralInverseMap n) (fun _ hz => hz))) doubledInput (fun _ _ => trivial)

private def derivativeHalfMap_holomorphic (n : Nat) : Holomorphic (derivativeHalfMap n) :=
  ((pairedSmallDiskLiteralInverseMap_holomorphic n).productOn
    (pairedSmallDiskLiteralInverseMap_holomorphic n) (fun _ hz => hz)).negate.productOn
    doubledInput_holomorphic (fun _ _ => trivial)

def pairedDivisionDerivativeTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (derivativeHalfMap n) (derivativeHalfMap n) (fun _ hz => hz)

def pairedDivisionDerivativeTermMap_holomorphic (n : Nat) :
    Holomorphic (pairedDivisionDerivativeTermMap n) :=
  (derivativeHalfMap_holomorphic n).sumOn (derivativeHalfMap_holomorphic n) (fun _ hz => hz)

theorem pairedDivisionDerivativeTermMap_eval (n : Nat) (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    ((pairedDivisionDerivativeTermMap n).eval z hz).val.Equiv
      (pairedRegularDivisionDerivativeTerm z hz n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedDivisionDerivativeTermMap n).eval z hz).property)
    (hright := (pairedRegularDivisionDerivativeTerm z hz n).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  change (-(I*I)*((0+1*Z)+(0+1*Z)))+(-(I*I)*((0+1*Z)+(0+1*Z))) =
    (-(I*I)*(Z+Z))+(-(I*I)*(Z+Z))
  grind only

end ComputableAnalysis.ModularForms
