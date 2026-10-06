import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws
import ComputableAnalysis.RiemannHilbert.DomainVectorFunctions

/-! Actual vector holomorphicity respects value agreement and restriction.
Constant vector fields retain an effective open domain even at rank zero. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory
variable {n : Nat}

def Holomorphic.transfer {f : Map n} (hf : Holomorphic f) (g : Map n)
    (hgf : ∀ z, g.domain z → f.domain z) (hg : OpenDomain g)
    (he : ∀ z hz, f.eval z (hgf z hz) ≈ g.eval z hz) : Holomorphic g where
  openDomain := hg
  coordinates i := (hf.coordinates i).transfer (coordinate g i) hgf ⟨hg.radius,hg.inside⟩
    (fun z hz => he z hz i)

def onDomain (f : Map n) {E : Scalar → Prop} (hE : ∀ z w, z ≈ w → (E z ↔ E w))
    (hEF : ∀ z, E z → f.domain z) : Map n where
  domain := E
  eval z hz := f.eval z (hEF z hz)
  domain_congr := hE
  eval_congr z w hz hw hzw := f.eval_congr z w (hEF z hz) (hEF w hw) hzw

def Holomorphic.onDomain {f : Map n} (hf : Holomorphic f) {E : Scalar → Prop}
    (hE : ScalarTopology.OpenData E) (hEF : ∀ z, E z → f.domain z) :
    Holomorphic (onDomain f hE.invariant hEF) :=
  hf.transfer _ hEF ⟨hE.radius,hE.inside⟩ (fun z hz => Setoid.refl (f.eval z (hEF z hz)))

def constantOn (E : Scalar → Prop) (hE : ∀ z w, z ≈ w → (E z ↔ E w)) (x : Fiber n) : Map n where
  domain := E
  eval _ _ := x
  domain_congr := hE
  eval_congr _ _ _ _ _ := Setoid.refl x

def constantOn_holomorphic {E : Scalar → Prop} (hE : ScalarTopology.OpenData E) (x : Fiber n) :
    Holomorphic (constantOn E hE.invariant x) where
  openDomain := ⟨hE.radius,hE.inside⟩
  coordinates i := DomainFunctions.constantOn_holomorphic hE ⟨x.val i,x.property i⟩

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
