import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws

/-! The sum rule for actual domain-dependent scalar functions, proved from
the exact sum remainder and rational half-error estimates. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def sumOn (f g : Map) (hfg : ∀ z, f.domain z → g.domain z) : Map where
  domain := f.domain
  eval z hz := scalarSum (f.eval z hz) (g.eval z (hfg z hz))
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := add_equiv (f.eval_congr z w hz hw hzw) (g.eval_congr z w _ _ hzw)

theorem sum_remainder (f g : Map) (hfg : ∀ z, f.domain z → g.domain z)
    (a : Scalar) (ha : f.domain a) (df dg : Scalar) (z : Scalar) (hz : f.domain z) :
    (remainder (sumOn f g hfg) a ha (scalarSum df dg) z hz).Equiv
      (add (remainder f a ha df z hz) (remainder g a (hfg a ha) dg z (hfg z hz))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _) (hright := add_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
  let FA := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let FZ := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let GA := ComplexRawQuotient.ofRaw (g.eval a (hfg a ha)).val (g.eval a (hfg a ha)).property
  let GZ := ComplexRawQuotient.ofRaw (g.eval z (hfg z hz)).val (g.eval z (hfg z hz)).property
  let DF := ComplexRawQuotient.ofRaw df.val df.property
  let DG := ComplexRawQuotient.ofRaw dg.val dg.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ((FZ+GZ) + -(FA+GA)) + -((DF+DG)*(Z + -A)) =
    ((FZ + -FA) + -(DF*(Z + -A))) + ((GZ + -GA) + -(DG*(Z + -A)))
  grind

def sumDerivative (f g : Map) (hfg : ∀ z, f.domain z → g.domain z)
    (a : Scalar) (ha : f.domain a) (df dg : Scalar)
    (hf : HasDerivativeAt f a ha df) (hg : HasDerivativeAt g a (hfg a ha) dg) :
    HasDerivativeAt (sumOn f g hfg) a ha (scalarSum df dg) where
  delta eps := minRadius (hf.delta (halfError eps)) (hg.delta (halfError eps))
  estimate eps H z hz hH hza := by
    have hs := LocalODE.small_add
      (hf.estimate (halfError eps) H z hz (Rat.le_trans hH (minRadius_left _ _)) hza)
      (hg.estimate (halfError eps) H z (hfg z hz) (Rat.le_trans hH (minRadius_right _ _)) hza)
    have he : (halfError eps).val*H.val+(halfError eps).val*H.val=eps.val*H.val := by
      have hh := halfError_identity eps
      grind
    rw [he] at hs
    exact Small.congr (add_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
      (remainder_valid _ _ _ _ _ _) (equiv_symm (sum_remainder f g hfg a ha df dg z hz)) hs

def Holomorphic.sumOn {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g)
    (hfg : ∀ z, f.domain z → g.domain z) : Holomorphic (sumOn f g hfg) where
  openDomain := ⟨hf.openDomain.radius,hf.openDomain.inside⟩
  derivative a ha := scalarSum (hf.derivative a ha) (hg.derivative a (hfg a ha))
  atPoint a ha := sumDerivative f g hfg a ha _ _ (hf.atPoint a ha) (hg.atPoint a (hfg a ha))
  derivative_congr a b ha hb hab := add_equiv
    (hf.derivative_congr a b ha hb hab) (hg.derivative_congr a b _ _ hab)
  continuousDerivative := sumContinuous hf.derivative (fun z hz => hg.derivative z (hfg z hz))
    hf.continuousDerivative (restrictContinuous hg.derivative hg.continuousDerivative hfg)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
