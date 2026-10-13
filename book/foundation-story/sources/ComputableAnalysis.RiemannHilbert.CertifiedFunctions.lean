import ComputableAnalysis.RiemannHilbert.RepresentedFiber
import ComputableAnalysis.Holomorphic

/-!
Represented functions whose evaluator takes the validity evidence of its input.
This permits finite precision searches to terminate from that evidence without
deciding validity of an arbitrary raw program. The existing raw-map interface
embeds into this interface; both derivative laws use the same exact remainder.
-/
namespace ComputableAnalysis.RiemannHilbert.CertifiedFunctions
open ComplexRaw FunctionTheory

structure Map where
  domain : Scalar → Prop
  eval : Scalar → ComplexRaw
  valid : ∀ z, domain z → (eval z).Valid
  domain_congr : ∀ z w, z.val.Equiv w.val → (domain z ↔ domain w)
  eval_congr : ∀ z w, domain z → domain w → z.val.Equiv w.val → (eval z).Equiv (eval w)

def ofRawMap (f : FunctionTheory.Map) : Map where
  domain z := f.domain z.val
  eval z := f.eval z.val
  valid z hz := f.valid z.val z.property hz
  domain_congr z w hzw := f.domain_congr z.property w.property hzw
  eval_congr z w hz hw hzw := f.eval_congr z.property w.property hz hw hzw

def remainder (f : Map) (a : Scalar) (d : ComplexRaw) (z : Scalar) : ComplexRaw :=
  sub (sub (f.eval z) (f.eval a)) (mul d (sub z.val a.val))

structure HasDerivativeAt (f : Map) (a : Scalar) (d : ComplexRaw) where
  point_mem : f.domain a
  derivative_valid : d.Valid
  delta : QPos → QPos
  estimate : ∀ (eps H : QPos) (z : Scalar), f.domain z →
    H.val ≤ (delta eps).val → Small (sub z.val a.val) H.val →
    Small (remainder f a d z) (eps.val*H.val)

def ofRawDerivative {f : FunctionTheory.Map} {a d : ComplexRaw}
    (h : FunctionTheory.HasDerivativeAt f a d) :
    HasDerivativeAt (ofRawMap f) ⟨a, h.point_valid⟩ d where
  point_mem := h.point_mem
  derivative_valid := h.derivative_valid
  delta := h.delta
  estimate eps H z hz hH hza := h.estimate eps H z.val z.property hz hH hza


structure OpenDomain (f : Map) where
  radius : ∀ a, f.domain a → QPos
  inside : ∀ a ha z, Small (sub z.val a.val) (radius a ha).val → f.domain z

structure ContinuousOn (domain : Scalar → Prop) (g : Scalar → ComplexRaw) where
  delta : ∀ a, domain a → QPos → QPos
  estimate : ∀ a ha (eps : QPos) z, domain z →
    Small (sub z.val a.val) (delta a ha eps).val → Small (sub (g z) (g a)) eps.val

structure Holomorphic (f : Map) where
  openDomain : OpenDomain f
  derivative : Scalar → ComplexRaw
  atPoint : ∀ a, f.domain a → HasDerivativeAt f a (derivative a)
  derivative_congr : ∀ a b, f.domain a → f.domain b → a.val.Equiv b.val →
    (derivative a).Equiv (derivative b)
  continuousDerivative : ContinuousOn f.domain derivative

def ofRawHolomorphic {f : FunctionTheory.Map} (h : FunctionTheory.Holomorphic f) :
    Holomorphic (ofRawMap f) where
  openDomain := {
    radius := fun a ha => h.openDomain.radius a.val a.property ha
    inside := fun a ha z hz => h.openDomain.inside a.val a.property ha z.val z.property hz }
  derivative a := h.derivative a.val
  atPoint a ha := ofRawDerivative (h.atPoint a.val a.property ha)
  derivative_congr a b ha hb hab := h.derivative_congr a.property b.property ha hb hab
  continuousDerivative := {
    delta := fun a ha eps => h.continuousDerivative.delta a.val a.property ha eps
    estimate := fun a ha eps z hz hza =>
      h.continuousDerivative.estimate a.val a.property ha eps z.val z.property hz hza }

end ComputableAnalysis.RiemannHilbert.CertifiedFunctions
