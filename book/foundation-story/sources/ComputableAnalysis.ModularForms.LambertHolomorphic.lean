import ComputableAnalysis.ModularForms.LambertContinuity

/-! Holomorphicity of actual Lambert values on executable open small disks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def lambertOpenMap (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) : DomainFunctions.Map where
  domain := LocalODE.interior r
  eval z hz := (lambertDiskMap r hr hlocal).eval z (LocalODE.interior_bound r z hz)
  domain_congr z w he := by
    constructor
    · rintro ⟨s,hs,hsr,hz⟩
      exact ⟨s,hs,hsr,Small.congr z.property w.property he hz⟩
    · rintro ⟨s,hs,hsr,hw⟩
      exact ⟨s,hs,hsr,Small.congr w.property z.property (equiv_symm he) hw⟩
  eval_congr z w hz hw he := lambertFactor_congr z w r r hr hr hlocal hlocal
    (LocalODE.interior_bound r z hz) (LocalODE.interior_bound r w hw) he

def lambertOpenMap_holomorphic (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    Holomorphic (lambertOpenMap r hr hlocal) where
  openDomain := ⟨LocalODE.interiorRadius r,LocalODE.interiorRadius_inside r⟩
  derivative a ha := lambertDiskDerivative a r hr hlocal (LocalODE.interior_bound r a ha)
  atPoint a ha := {
    delta := (lambertDiskMap_hasDerivativeAt r hr hlocal a (LocalODE.interior_bound r a ha)).delta
    estimate := fun eps H z hz hH hd =>
      (lambertDiskMap_hasDerivativeAt r hr hlocal a (LocalODE.interior_bound r a ha)).estimate
        eps H z (LocalODE.interior_bound r z hz) hH hd }
  derivative_congr a z ha hz he := lambertDiskDerivative_congr a z r r hr hr hlocal hlocal
    (LocalODE.interior_bound r a ha) (LocalODE.interior_bound r z hz) he
  continuousDerivative := {
    delta := fun a ha => (lambertDiskDerivative_continuous r hr hlocal).delta a
      (LocalODE.interior_bound r a ha)
    estimate := fun a ha eps z hz hd =>
      (lambertDiskDerivative_continuous r hr hlocal).estimate a (LocalODE.interior_bound r a ha)
        eps z (LocalODE.interior_bound r z hz) hd }

end ComputableAnalysis.ModularForms
