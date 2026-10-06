import ComputableAnalysis.ModularForms.EntireExponential
import ComputableAnalysis.ModularForms.ActionHolomorphic
import ComputableAnalysis.GeometricPiRotation

/-! The actual holomorphic nome, using the project's geometric half-pi.
Periodicity, cusp bounds, and comparison with other exponential evaluators
are separate results; none is assumed in the definition. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Four times the imaginary geometric half-pi, representing `2*pi*i`. -/
def nomeSlope : Scalar :=
  ⟨scaleRat 4 (mulI (ofRealRaw GeometricPiRotation.halfPi)),
    scaleRat_valid (mulI_valid (ofRealRaw_valid _ GeometricPiRotation.halfPi_valid))⟩

def nomeExponentMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z _ := scalarProduct nomeSlope z
  domain_congr := upperOpenData.invariant
  eval_congr z w _ _ hzw := mul_equiv nomeSlope.property nomeSlope.property
    z.property w.property (equiv_refl _ nomeSlope.property) hzw

def nomeExponentMap_holomorphic : DomainFunctions.Holomorphic nomeExponentMap := by
  let zeroScalar : Scalar := ⟨zero, ofQComplex_valid _⟩
  apply (DomainFunctions.affine_holomorphic zeroScalar nomeSlope).transfer nomeExponentMap
    (fun _ _ => trivial) ⟨upperRadius, upperRadius_inside⟩
  intro z hz
  exact zero_add_equiv _ ((nomeExponentMap.eval z hz).property)

/-- The nome evaluator on arbitrary valid represented upper-half-plane inputs. -/
def nome : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := entireExponentialValue (nomeExponentMap.eval z hz)
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw hzw := entireExponentialValue_congr _ _
    (nomeExponentMap.eval_congr z w hz hw hzw)

/-- Actual derivative errors and derivative continuity for the nome. -/
def nome_holomorphic : DomainFunctions.Holomorphic nome := by
  have h := entireExponential_holomorphic.compose nomeExponentMap_holomorphic
  apply h.transfer nome (fun _ hz => ⟨hz,trivial⟩) ⟨upperRadius, upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ (nome.eval z hz).property

end ComputableAnalysis.ModularForms
