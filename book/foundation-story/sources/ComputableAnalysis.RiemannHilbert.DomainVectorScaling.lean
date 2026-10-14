import ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra

/-! Holomorphic scalar multiplication of actual finite vector maps.
Domain openness is retained independently of rank. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory
variable {n : Nat}

def onVectorDomain (f : Map n) (s : DomainFunctions.Map)
    (hfs : ∀ z, f.domain z → s.domain z) : DomainFunctions.Map where
  domain := f.domain
  eval z hz := s.eval z (hfs z hz)
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := s.eval_congr z w _ _ hzw

def onVectorDomain_holomorphic (f : Map n) (hf : OpenDomain f) (s : DomainFunctions.Map)
    (hs : DomainFunctions.Holomorphic s) (hfs : ∀ z, f.domain z → s.domain z) :
    DomainFunctions.Holomorphic (onVectorDomain f s hfs) where
  openDomain := { radius := hf.radius, inside := hf.inside }
  derivative z hz := hs.derivative z (hfs z hz)
  atPoint a ha := {
    delta := (hs.atPoint a (hfs a ha)).delta
    estimate eps H z hz hH hza := (hs.atPoint a (hfs a ha)).estimate eps H z (hfs z hz) hH hza }
  derivative_congr a b ha hb hab := hs.derivative_congr a b _ _ hab
  continuousDerivative := DomainFunctions.restrictContinuous hs.derivative hs.continuousDerivative hfs

def scaled (f : Map n) (s : DomainFunctions.Map) (hfs : ∀ z, f.domain z → s.domain z) : Map n where
  domain := f.domain
  eval z hz := Fiber.scale (s.eval z (hfs z hz)) (f.eval z hz)
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := Fiber.scale_congr
    (s.eval_congr z w _ _ hzw) (f.eval_congr z w hz hw hzw)

def scaled_holomorphic (f : Map n) (hf : Holomorphic f) (s : DomainFunctions.Map)
    (hs : DomainFunctions.Holomorphic s) (hfs : ∀ z, f.domain z → s.domain z) :
    Holomorphic (scaled f s hfs) where
  openDomain := { radius := hf.openDomain.radius, inside := hf.openDomain.inside }
  coordinates i := (onVectorDomain_holomorphic f hf.openDomain s hs hfs).productOn (hf i) (fun _ hz => hz)

theorem scaled_derivative (f : Map n) (hf : Holomorphic f) (s : DomainFunctions.Map)
    (hs : DomainFunctions.Holomorphic s) (hfs : ∀ z, f.domain z → s.domain z)
    (z : Scalar) (hz : f.domain z) :
    derivative (scaled f s hfs) (scaled_holomorphic f hf s hs hfs) z hz ≈
      Fiber.add (Fiber.scale (hs.derivative z (hfs z hz)) (f.eval z hz))
        (Fiber.scale (s.eval z (hfs z hz)) (derivative f hf z hz)) :=
  fun i => equiv_refl _ (add_valid
    (mul_valid (hs.derivative z (hfs z hz)).property ((f.eval z hz).property i))
    (mul_valid (s.eval z (hfs z hz)).property ((derivative f hf z hz).property i)))

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
