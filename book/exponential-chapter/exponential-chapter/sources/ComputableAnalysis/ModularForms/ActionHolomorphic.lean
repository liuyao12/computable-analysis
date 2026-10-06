import ComputableAnalysis.ModularForms.UpperNeighborhood
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! Actual holomorphic matrix transformations on the entire represented upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

 def upperOpenData : ScalarTopology.OpenData (fun z => InUpperHalfPlane z.val) where
  invariant z w hzw := upperHalfPlane_congr z.property w.property hzw
  radius := upperRadius
  inside := upperRadius_inside

def integerAffineMap (a b : Int) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z _ := ⟨integerAffine a b z.val, integerAffine_valid _ _ z.property⟩
  domain_congr := upperOpenData.invariant
  eval_congr _ _ _ _ hzw := integerAffine_equiv _ _ hzw

def rationalInteger (a : Int) : Scalar := ⟨ofQComplex ⟨(a : Rat),0⟩, ofQComplex_valid _⟩

def integerAffineMap_holomorphic (a b : Int) : DomainFunctions.Holomorphic (integerAffineMap a b) := by
  apply (DomainFunctions.affine_holomorphic (rationalInteger b) (rationalInteger a)).transfer
    (integerAffineMap a b) (fun _ _ => trivial) ⟨upperRadius, upperRadius_inside⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((DomainFunctions.affine (rationalInteger b) (rationalInteger a)).eval z trivial).property)
    (hright := integerAffine_valid _ _ z.property)
  change ComplexRawQuotient.ofQComplex ⟨(b : Rat),0⟩ +
    ComplexRawQuotient.ofQComplex ⟨(a : Rat),0⟩ * ComplexRawQuotient.ofRaw z.val z.property = _
  rw [integer_constant, integer_constant, integerAffine_class]
  grind

def reciprocalDenominatorMap (g : SL2Z) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := RepresentedReciprocal.inverse
    ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩ (denominator_nonzero g z hz)
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw hzw := RepresentedReciprocal.inverse_congr _ _
    (denominator_nonzero g z hz) (denominator_nonzero g w hw) (integerAffine_equiv _ _ hzw)

def reciprocalDenominatorMap_holomorphic (g : SL2Z) : DomainFunctions.Holomorphic (reciprocalDenominatorMap g) := by
  have h := ReciprocalHolomorphic.holomorphic.compose (integerAffineMap_holomorphic g.c g.d)
  apply h.transfer (reciprocalDenominatorMap g)
    (fun z hz => ⟨hz, denominator_nonzero g z hz⟩) ⟨upperRadius, upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ ((reciprocalDenominatorMap g).eval z hz).property

/-- The function is the existing matrix evaluator, with its actual domain. -/
def matrixMap (g : SL2Z) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval := fractionalLinear g
  domain_congr := upperOpenData.invariant
  eval_congr := fractionalLinear_congr g

/-- Complex derivative, remainder estimates, and derivative continuity are constructed
for every integer determinant-one transformation on the entire upper half-plane. -/
def matrixMap_holomorphic (g : SL2Z) : DomainFunctions.Holomorphic (matrixMap g) := by
  have h := (integerAffineMap_holomorphic g.a g.b).productOn
    (reciprocalDenominatorMap_holomorphic g) (fun _ hz => hz)
  apply h.transfer (matrixMap g) (fun _ hz => hz) ⟨upperRadius, upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ ((matrixMap g).eval z hz).property

end ComputableAnalysis.ModularForms
