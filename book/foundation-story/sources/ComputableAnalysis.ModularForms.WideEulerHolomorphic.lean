import ComputableAnalysis.ModularForms.WideEulerTailHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private def leadingFactorsMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q _ := finiteDiscriminantEulerProduct q 2
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w _ _ he := finiteDiscriminantEulerProduct_congr q w he 2

private noncomputable def leadingFactorsMap_holomorphic : Holomorphic leadingFactorsMap :=
  (finiteDiscriminantEulerMap_holomorphic 2).transfer leadingFactorsMap (fun _ _ => trivial)
    { radius := wideLambertFifthDomain_openData.radius, inside := wideLambertFifthDomain_openData.inside }
    (fun q _ => equiv_refl _ (finiteDiscriminantEulerProduct q 2).property)

/-- The executable full Euler product is holomorphic throughout the wider nome disk. -/
noncomputable def wideEulerNomeMap_holomorphic : Holomorphic wideEulerNomeMap := by
  let h := leadingFactorsMap_holomorphic.productOn wideEulerTailNomeMap_holomorphic (fun _ h => h)
  exact h.transfer wideEulerNomeMap (fun _ h => h)
    { radius := wideLambertFifthDomain_openData.radius, inside := wideLambertFifthDomain_openData.inside }
    (fun q hq => equiv_refl _ (wideEulerNomeMap.eval q hq).property)

/-- The executable normalized product is holomorphic on the same wider disk. -/
noncomputable def wideNormalizedEulerMap_holomorphic : Holomorphic wideNormalizedEulerMap :=
  wideEulerNomeMap_holomorphic.productOn tauCoordinateMap_holomorphic (fun _ _ => trivial)

/-- Exact derivative formula from the actual leading factors and constructed infinite-tail slope. -/
theorem wideEulerNomeMap_derivative (q : Scalar) (hq : wideLambertFifthDomain q) :
    (wideEulerNomeMap_holomorphic.derivative q hq).val.Equiv
      (add (mul (finiteDiscriminantEulerSlope q 2).val (wideEulerTailNomeMap.eval q hq).val)
        (mul (finiteDiscriminantEulerProduct q 2).val (wideEulerTailDerivativeCandidate q hq).val)) := by
  have he := finiteDiscriminantEulerSlope_actual q 2
  exact add_equiv
    (mul_equiv ((finiteDiscriminantEulerMap_holomorphic 2).derivative q trivial).property
      (finiteDiscriminantEulerSlope q 2).property (wideEulerTailNomeMap.eval q hq).property
      (wideEulerTailNomeMap.eval q hq).property he (equiv_refl _ (wideEulerTailNomeMap.eval q hq).property))
    (equiv_refl _ (mul_valid (finiteDiscriminantEulerProduct q 2).property
      (wideEulerTailDerivativeCandidate q hq).property))

end ComputableAnalysis.ModularForms
