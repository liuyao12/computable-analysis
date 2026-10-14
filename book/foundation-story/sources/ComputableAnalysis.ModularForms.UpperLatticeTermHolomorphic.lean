import ComputableAnalysis.ModularForms.ActionHolomorphic
import ComputableAnalysis.ModularForms.UpperLatticeCongruence
import ComputableAnalysis.ModularForms.UpperLatticePointTerms

/-! Actual holomorphic reciprocal-power terms on the represented upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def latticeReciprocalMap (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := latticeInverse z hz u hu
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := latticeInverse_congr z w hz hw u hu he

def latticeReciprocalMap_holomorphic (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    DomainFunctions.Holomorphic (latticeReciprocalMap u hu) := by
  have h := ReciprocalHolomorphic.holomorphic.compose (integerAffineMap_holomorphic u.y u.x)
  apply h.transfer (latticeReciprocalMap u hu)
    (fun z hz => ⟨hz,latticeVector_nonzero z hz u hu⟩) ⟨upperRadius,upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ (latticeInverse z hz u hu).property

def latticePowerMap (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨LocalODE.power (latticeInverse z hz u hu).val k,
    LocalODE.power_valid _ (latticeInverse z hz u hu).property k⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := LocalODE.power_congr _ _
    (latticeInverse z hz u hu).property (latticeInverse w hw u hu).property
    (latticeInverse_congr z w hz hw u hu he) k

def latticePowerMap_holomorphic (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (k : Nat) : DomainFunctions.Holomorphic (latticePowerMap u hu k) := by
  induction k with
  | zero =>
    have h := constantOn_holomorphic upperOpenData
      (⟨ComplexRaw.one,ofQComplex_valid _⟩ : Scalar)
    apply h.transfer (latticePowerMap u hu 0) (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih =>
    have h := ih.productOn (latticeReciprocalMap_holomorphic u hu) (fun _ hz => hz)
    apply h.transfer (latticePowerMap u hu (k+1)) (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (mul_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)
      (latticeInverse z hz u hu).property)

end ComputableAnalysis.ModularForms
