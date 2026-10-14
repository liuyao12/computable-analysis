import ComputableAnalysis.ModularForms.TauEulerProductLimit
import ComputableAnalysis.RiemannHilbert.CenteredUniqueness

/-! The executable Euler product as an invariant map on an open nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauEulerProduct_at_zero (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (hz : q.val.Equiv zero) :
    (tauEulerProduct q r hr hrMax hq).val.Equiv one := by
  have hq0 : Small q.val 0 := Small.congr (ofQComplex_valid _) q.property
    (equiv_symm hz) (Small.zero Rat.le_refl)
  have he := tauEulerProduct_congr q q r 0 hr Rat.le_refl hrMax
    (by decide +kernel) hq hq0 (equiv_refl _ q.property)
  have hclose := tauEulerProduct_close_prefix q 0 Rat.le_refl (by decide +kernel) hq0 0
  have hzero : Small (sub (tauEulerProduct q 0 Rat.le_refl (by decide +kernel) hq0).val one) 0 := by
    simpa only [finiteDiscriminantEulerProduct,Nat.zero_add,Rat.pow_one,Rat.mul_zero] using hclose
  exact equiv_trans (tauEulerProduct q r hr hrMax hq).property
    (tauEulerProduct q 0 Rat.le_refl (by decide +kernel) hq0).property (ofQComplex_valid _)
    he (SeriesLimitLaws.equiv_of_small_sub_zero _ _ hzero)

def tauEulerNomeDomain (q : Scalar) : Prop := LocalODE.interior (1/1024:Rat) q

def tauEulerNomeDomain_openData : ScalarTopology.OpenData tauEulerNomeDomain where
  invariant q w he := ⟨Centered.interior_congr _ q w he,
    Centered.interior_congr _ w q (equiv_symm he)⟩
  radius := LocalODE.interiorRadius (1/1024:Rat)
  inside := LocalODE.interiorRadius_inside (1/1024:Rat)

/-- A fixed admissible convergence bound hides the radius input from callers. -/
def tauEulerNomeMap : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval q hq := tauEulerProduct q (1/1024) (by decide +kernel) Rat.le_refl
    (LocalODE.interior_bound _ q hq)
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr q w hq hw he := tauEulerProduct_congr q w _ _ (by decide +kernel)
    (by decide +kernel) Rat.le_refl Rat.le_refl
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he

/-- The map agrees with every independently supplied admissible radius. -/
theorem tauEulerNomeMap_agreement (q : Scalar) (hq : tauEulerNomeDomain q)
    (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/1024) (hs : Small q.val r) :
    (tauEulerNomeMap.eval q hq).val.Equiv (tauEulerProduct q r hr hrMax hs).val :=
  tauEulerProduct_congr q q _ r (by decide +kernel) hr Rat.le_refl hrMax
    (LocalODE.interior_bound _ q hq) hs (equiv_refl _ q.property)

theorem tauEulerNomeMap_at_zero (q : Scalar) (hq : tauEulerNomeDomain q) (hz : q.val.Equiv zero) :
    (tauEulerNomeMap.eval q hq).val.Equiv one :=
  tauEulerProduct_at_zero q _ (by decide +kernel) Rat.le_refl
    (LocalODE.interior_bound _ q hq) hz

theorem tauEulerNomeMap_nonzero (q : Scalar) (hq : tauEulerNomeDomain q) :
    NonzeroBoxSearch.Nonzero (tauEulerNomeMap.eval q hq) :=
  tauEulerProduct_nonzero q _ (by decide +kernel) Rat.le_refl
    (LocalODE.interior_bound _ q hq)

end ComputableAnalysis.ModularForms
