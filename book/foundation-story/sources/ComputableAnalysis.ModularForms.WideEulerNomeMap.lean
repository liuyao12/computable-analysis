import ComputableAnalysis.ModularForms.ScalarProductNonvanishing
import ComputableAnalysis.ModularForms.WideEulerProductComparison
import ComputableAnalysis.ModularForms.TauNormalizedEulerMap
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Executable, representation-invariant Euler product on the wider open nome disk. -/
def wideEulerNomeMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := wideEulerProductValue q (LocalODE.interior_bound _ q hq)
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := wideEulerProductValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he

theorem wideEulerNomeMap_nonzero (q : Scalar) (hq : wideLambertFifthDomain q) :
    NonzeroBoxSearch.Nonzero (wideEulerNomeMap.eval q hq) :=
  wideEulerProductValue_nonzero q (LocalODE.interior_bound _ q hq)

/-- Actual normalized Euler product; agreement with Eisenstein discriminants is separate. -/
def wideNormalizedEulerMap : DomainFunctions.Map :=
  productOn wideEulerNomeMap tauCoordinateMap (fun _ _ => trivial)

theorem wideEulerNomeMap_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideEulerNomeMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (tauEulerNomeMap.eval q hq).val :=
  wideEulerProductValue_original_agreement q (1/1024) (by decide +kernel) Rat.le_refl
    (LocalODE.interior_bound _ q hq)
    (LocalODE.interior_bound _ q (tauEulerNomeDomain_wide_fifth_mem q hq))

theorem wideNormalizedEulerMap_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideNormalizedEulerMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (tauNormalizedEulerMap.eval q hq).val :=
  mul_equiv (wideEulerNomeMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property
    (tauEulerNomeMap.eval q hq).property q.property q.property
    (wideEulerNomeMap_original_agreement q hq) (equiv_refl _ q.property)

/-- Exact nonvanishing criterion for the normalized actual product on the wider disk. -/
theorem wideNormalizedEulerMap_nonzero_iff (q : Scalar) (hq : wideLambertFifthDomain q) :
    NonzeroBoxSearch.Nonzero (wideNormalizedEulerMap.eval q hq) ↔ NonzeroBoxSearch.Nonzero q := by
  constructor
  · intro hn
    exact ((scalar_mul_nonzero_iff (wideEulerNomeMap.eval q hq) q).mp hn).2
  · intro hn
    exact scalar_mul_nonzero (wideEulerNomeMap.eval q hq) q (wideEulerNomeMap_nonzero q hq) hn

end ComputableAnalysis.ModularForms
