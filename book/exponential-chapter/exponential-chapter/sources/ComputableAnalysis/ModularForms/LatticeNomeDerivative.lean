import ComputableAnalysis.ModularForms.LatticePartialFractionFourier
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Differentiating the proved lattice/nome identity with actual derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def latticeNomeFormulaMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ latticeFourierCoefficient) upperNomeCotangentMap

def latticeNomeFormulaMap_holomorphic : Holomorphic latticeNomeFormulaMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ latticeFourierCoefficient).compose
    upperNomeCotangentMap_holomorphic

theorem latticeNomeFormulaMap_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    latticeNomeFormulaMap.domain z := ⟨hz,trivial⟩

theorem latticeNomeFormulaMap_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (latticeNomeFormulaMap.eval z (latticeNomeFormulaMap_mem z hz)).val := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let k := upperNomeCotangentMap.eval z hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property)
    (hright := neg_valid (mul_valid latticeImaginaryUnit.property (mul_valid latticeFrequency.property k.property)))
    (latticePartialFraction_nome_formula z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := p.property)
    (hright := (latticeNomeFormulaMap.eval z (latticeNomeFormulaMap_mem z hz)).property)
  let P := gridScalarValue p
  let K := gridScalarValue k
  let I := gridScalarValue latticeImaginaryUnit
  let A := gridScalarValue latticeFrequency
  change P= -(I*(A*K)) at hp
  change P=0+(-(I*A))*K
  grind only

theorem latticePartialFraction_nome_derivative (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (mul latticeFourierCoefficient.val (upperNomeCotangentDerivative z hz).val) := by
  have ho := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative_equiv_on_overlap
    latticeNomeFormulaMap_holomorphic (fun w _ hw => latticeNomeFormulaMap_agreement w hw.1)
    z (pairedGlobalOffPole_upper_mem z hz) (latticeNomeFormulaMap_mem z hz)
  have hd := upperNomeCotangentMap_derivative z hz
  have hm := mul_equiv latticeFourierCoefficient.property latticeFourierCoefficient.property
    (upperNomeCotangentMap_holomorphic.derivative z hz).property
    (upperNomeCotangentDerivative z hz).property
    (equiv_refl _ latticeFourierCoefficient.property) hd
  have hc : (latticeNomeFormulaMap_holomorphic.derivative z (latticeNomeFormulaMap_mem z hz)).val.Equiv
      (mul latticeFourierCoefficient.val (upperNomeCotangentMap_holomorphic.derivative z hz).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (latticeNomeFormulaMap_holomorphic.derivative z (latticeNomeFormulaMap_mem z hz)).property)
      (hright := mul_valid latticeFourierCoefficient.property
        (upperNomeCotangentMap_holomorphic.derivative z hz).property)
    rfl
  exact equiv_trans (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
    (pairedGlobalOffPole_upper_mem z hz)).property
    (latticeNomeFormulaMap_holomorphic.derivative z (latticeNomeFormulaMap_mem z hz)).property
    (mul_valid latticeFourierCoefficient.property (upperNomeCotangentDerivative z hz).property) ho
    (equiv_trans (latticeNomeFormulaMap_holomorphic.derivative z (latticeNomeFormulaMap_mem z hz)).property
      (mul_valid latticeFourierCoefficient.property (upperNomeCotangentMap_holomorphic.derivative z hz).property)
      (mul_valid latticeFourierCoefficient.property (upperNomeCotangentDerivative z hz).property) hc hm)

end ComputableAnalysis.ModularForms
