import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra
import ComputableAnalysis.RiemannHilbert.ScalarTopology

/-! Exact value agreement transports actual holomorphic evaluators and
their rational derivative estimates, including restriction to a supplied
effective open domain. Constant maps are constructed on those domains. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

theorem remainder_transfer (f g : Map) (hgf : ∀ z, g.domain z → f.domain z)
    (he : ∀ z hz, (f.eval z (hgf z hz)).val.Equiv (g.eval z hz).val)
    (a : Scalar) (ha : g.domain a) (d : Scalar) (z : Scalar) (hz : g.domain z) :
    (remainder f a (hgf a ha) d z (hgf z hz)).Equiv (remainder g a ha d z hz) :=
  FunctionTheory.sub_congr (FunctionTheory.sub_congr (he z hz) (he a ha))
    (equiv_refl _ (mul_valid d.property (sub_valid z.property a.property)))

/-- Holomorphicity is invariant under exact represented value agreement.
Open-domain evidence is retained for the actual target domain. -/
def Holomorphic.transfer {f : Map} (hf : Holomorphic f) (g : Map)
    (hgf : ∀ z, g.domain z → f.domain z) (hg : OpenDomain g)
    (he : ∀ z hz, (f.eval z (hgf z hz)).val.Equiv (g.eval z hz).val) : Holomorphic g where
  openDomain := hg
  derivative z hz := hf.derivative z (hgf z hz)
  atPoint a ha := {
    delta := (hf.atPoint a (hgf a ha)).delta
    estimate eps H z hz hH hza := Small.congr (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _)
      (remainder_transfer f g hgf he a ha _ z hz)
      ((hf.atPoint a (hgf a ha)).estimate eps H z (hgf z hz) hH hza) }
  derivative_congr a b ha hb hab := hf.derivative_congr a b (hgf a ha) (hgf b hb) hab
  continuousDerivative := restrictContinuous hf.derivative hf.continuousDerivative hgf

def onDomain (f : Map) {E : Scalar → Prop} (hE : ∀ z w, z ≈ w → (E z ↔ E w))
    (hEF : ∀ z, E z → f.domain z) : Map where
  domain := E
  eval z hz := f.eval z (hEF z hz)
  domain_congr := hE
  eval_congr z w hz hw hzw := f.eval_congr z w (hEF z hz) (hEF w hw) hzw

def Holomorphic.onDomain {f : Map} (hf : Holomorphic f) {E : Scalar → Prop}
    (hE : ScalarTopology.OpenData E) (hEF : ∀ z, E z → f.domain z) :
    Holomorphic (onDomain f hE.invariant hEF) :=
  hf.transfer _ hEF ⟨hE.radius,hE.inside⟩
    (fun z hz => equiv_refl _ (f.eval z (hEF z hz)).property)

def constantOn (E : Scalar → Prop) (hE : ∀ z w, z ≈ w → (E z ↔ E w)) (c : Scalar) : Map where
  domain := E
  eval _ _ := c
  domain_congr := hE
  eval_congr _ _ _ _ _ := equiv_refl _ c.property

theorem constantOn_remainder (E : Scalar → Prop) (hE : ∀ z w, z ≈ w → (E z ↔ E w))
    (c a z : Scalar) (ha : E a) (hz : E z) :
    (remainder (constantOn E hE c) a ha ⟨zero,ofQComplex_valid _⟩ z hz).Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _) (hright := ofQComplex_valid _)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change (C + -C) + -(0*(Z + -A)) = 0
  grind

def constantOn_holomorphic {E : Scalar → Prop} (hE : ScalarTopology.OpenData E) (c : Scalar) :
    Holomorphic (constantOn E hE.invariant c) where
  openDomain := ⟨hE.radius,hE.inside⟩
  derivative _ _ := ⟨zero,ofQComplex_valid _⟩
  atPoint a ha := {
    delta _ := unitError
    estimate eps H z hz _ _ := Small.congr (ofQComplex_valid _) (remainder_valid _ _ _ _ _ _)
      (equiv_symm (constantOn_remainder E hE.invariant c a z ha hz))
      (Small.zero (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property))) }
  derivative_congr _ _ _ _ _ := equiv_refl _ (ofQComplex_valid _)
  continuousDerivative := {
    delta _ _ eps := eps
    estimate _ _ eps _ _ _ := Small.congr (ofQComplex_valid _)
      (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (equiv_symm (add_neg_equiv zero (ofQComplex_valid _)))
      (Small.zero (Rat.le_of_lt eps.property)) }

end ComputableAnalysis.RiemannHilbert.DomainFunctions
