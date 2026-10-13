import ComputableAnalysis.RiemannHilbert.CertifiedFunctions

/-! Functions whose executable evaluation uses evidence of domain membership.
This permits terminating searches on open domains such as the nonzero
complex numbers, without a total extension across a pole. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

structure Map where
  domain : Scalar → Prop
  eval : (z : Scalar) → domain z → Scalar
  domain_congr : ∀ z w, z.val.Equiv w.val → (domain z ↔ domain w)
  eval_congr : ∀ z w hz hw, z.val.Equiv w.val → (eval z hz).val.Equiv (eval w hw).val

def ofCertified (f : CertifiedFunctions.Map) : Map where
  domain := f.domain
  eval z hz := ⟨f.eval z, f.valid z hz⟩
  domain_congr := f.domain_congr
  eval_congr := f.eval_congr

def remainder (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (z : Scalar) (hz : f.domain z) : ComplexRaw :=
  sub (sub (f.eval z hz).val (f.eval a ha).val) (mul d.val (sub z.val a.val))

structure HasDerivativeAt (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar) where
  delta : QPos → QPos
  estimate : ∀ (eps H : QPos) (z : Scalar) (hz : f.domain z),
    H.val ≤ (delta eps).val → Small (sub z.val a.val) H.val →
    Small (remainder f a ha d z hz) (eps.val*H.val)

structure OpenDomain (f : Map) where
  radius : ∀ a, f.domain a → QPos
  inside : ∀ a ha z, Small (sub z.val a.val) (radius a ha).val → f.domain z

structure ContinuousOn (domain : Scalar → Prop) (g : ∀ z, domain z → Scalar) where
  delta : ∀ a, domain a → QPos → QPos
  estimate : ∀ a ha (eps : QPos) z hz,
    Small (sub z.val a.val) (delta a ha eps).val →
    Small (sub (g z hz).val (g a ha).val) eps.val

structure Holomorphic (f : Map) where
  openDomain : OpenDomain f
  derivative : ∀ a, f.domain a → Scalar
  atPoint : ∀ a ha, HasDerivativeAt f a ha (derivative a ha)
  derivative_congr : ∀ a b ha hb, a.val.Equiv b.val →
    (derivative a ha).val.Equiv (derivative b hb).val
  continuousDerivative : ContinuousOn f.domain derivative

def ofCertifiedHolomorphic {f : CertifiedFunctions.Map} (h : CertifiedFunctions.Holomorphic f) :
    Holomorphic (ofCertified f) where
  openDomain := {
    radius := h.openDomain.radius
    inside := h.openDomain.inside }
  derivative a ha := ⟨h.derivative a, (h.atPoint a ha).derivative_valid⟩
  atPoint a ha := {
    delta := (h.atPoint a ha).delta
    estimate := (h.atPoint a ha).estimate }
  derivative_congr a b ha hb hab := h.derivative_congr a b ha hb hab
  continuousDerivative := {
    delta := h.continuousDerivative.delta
    estimate := h.continuousDerivative.estimate }

end ComputableAnalysis.RiemannHilbert.DomainFunctions
