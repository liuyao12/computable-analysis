import ComputableAnalysis.ModularForms.PairedDivisionDerivativeUniformBounds

/-! Uniform derivative control through the Riccati pole extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularPartDerivative_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) : Small (pairedRegularPartDerivative z hz).val 80 := by
  have ht := pairedRegularDivisionValue_bound z (LocalODE.interior_bound _ z hz)
  have hd := pairedRegularDivisionDerivativeValue_uniform_bound z hz
  have hm := Small.mul z.property (pairedRegularDivisionDerivative z hz).property
    (show (0:Rat)≤1/4 by decide +kernel) (show (0:Rat)≤128 by decide +kernel)
    (LocalODE.interior_bound _ z hz) hd
  exact (Small.congr
    (add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (pairedRegularPartDerivative z hz).property
    (equiv_symm (pairedRegularPartDerivative_division z hz))
    (LocalODE.small_add ht hm)).mono (by decide +kernel)

theorem pairedRiccatiExtensionMap_derivative_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    Small (pairedRiccatiExtensionMap_holomorphic.derivative z hz).val 4352 := by
  let id := DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ ⟨one,ofQComplex_valid _⟩
  have he : (id.eval z trivial).val.Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (id.eval z trivial).property) (hright := z.property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+1*Z=Z
    grind only
  have hzid := Small.congr z.property (id.eval z trivial).property (equiv_symm he)
    (LocalODE.interior_bound _ z hz)
  have hone : Small one 1 := (BoxApproximation.rational_small QComplex.one).mono (by decide +kernel)
  have hd := pairedRegularDivisionMap_derivative_uniform_bound z hz
  have hdd := pairedDivisionFirstDerivativeMap_derivative_uniform_bound z hz
  have hs : Small (pairedRegularPartMap.eval z hz).val 8 := by
    have h := pairedRegularPart_bound z (LocalODE.interior_bound _ z hz) (1/4)
      (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)
    exact h.mono (by decide +kernel)
  have hsd := pairedRegularPartDerivative_uniform_bound z hz
  have ha := Small.mul (pairedDivisionFirstDerivativeMap_holomorphic.derivative z hz).property
    (id.eval z trivial).property (show (0:Rat)≤2304 by decide +kernel)
    (show (0:Rat)≤1/4 by decide +kernel) hdd hzid
  have hb := Small.mul (pairedDivisionFirstDerivativeMap.eval z hz).property (ofQComplex_valid _)
    (show (0:Rat)≤128 by decide +kernel) (show (0:Rat)≤1 by decide +kernel) hd hone
  have hc := Small.mul (pairedRegularPartDerivative z hz).property (pairedRegularPartMap.eval z hz).property
    (show (0:Rat)≤80 by decide +kernel) (show (0:Rat)≤8 by decide +kernel) hsd hs
  have hd' := Small.mul (pairedRegularPartMap.eval z hz).property (pairedRegularPartDerivative z hz).property
    (show (0:Rat)≤8 by decide +kernel) (show (0:Rat)≤80 by decide +kernel) hs hsd
  exact (LocalODE.small_add hd (LocalODE.small_add hd (LocalODE.small_add hd
    (LocalODE.small_add (LocalODE.small_add ha hb) (LocalODE.small_add hc hd'))))).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
