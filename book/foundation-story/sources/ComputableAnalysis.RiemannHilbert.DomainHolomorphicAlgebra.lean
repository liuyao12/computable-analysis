import ComputableAnalysis.RiemannHilbert.DomainProductRule

/-! Holomorphic products and negation of executable scalar maps, and
continuity of sums. Derivative data are constructed from actual remainders. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

theorem scalarSum_difference (a b c d : Scalar) :
    (sub (scalarSum a b).val (scalarSum c d).val).Equiv
      (add (sub a.val c.val) (sub b.val d.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarSum a b).property (scalarSum c d).property)
    (hright := add_valid (sub_valid a.property c.property) (sub_valid b.property d.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change (A+B) + -(C+D) = (A + -C)+(B + -D)
  grind

def sumContinuous {D : Scalar → Prop} (f g : ∀ z, D z → Scalar)
    (hf : ContinuousOn D f) (hg : ContinuousOn D g) :
    ContinuousOn D (fun z hz => scalarSum (f z hz) (g z hz)) where
  delta a ha eps := minRadius (hf.delta a ha (halfError eps)) (hg.delta a ha (halfError eps))
  estimate a ha eps z hz hza := by
    have hs := LocalODE.small_add
      (hf.estimate a ha (halfError eps) z hz (hza.mono (minRadius_left _ _)))
      (hg.estimate a ha (halfError eps) z hz (hza.mono (minRadius_right _ _)))
    have he : (halfError eps).val+(halfError eps).val=eps.val := by
      have h := halfError_identity eps
      grind only
    rw [he] at hs
    exact Small.congr (add_valid (sub_valid (f z hz).property (f a ha).property)
      (sub_valid (g z hz).property (g a ha).property))
      (sub_valid (scalarSum (f z hz) (g z hz)).property (scalarSum (f a ha) (g a ha)).property)
      (equiv_symm (scalarSum_difference _ _ _ _)) hs

def Holomorphic.productOn {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g)
    (hfg : ∀ z, f.domain z → g.domain z) : Holomorphic (productOn f g hfg) where
  openDomain := { radius := hf.openDomain.radius, inside := hf.openDomain.inside }
  derivative a ha := productSlope (f.eval a ha) (g.eval a (hfg a ha))
    (hf.derivative a ha) (hg.derivative a (hfg a ha))
  atPoint a ha := productDerivative f g hfg a ha _ _ (hf.atPoint a ha) (hg.atPoint a (hfg a ha))
  derivative_congr a b ha hb hab := add_equiv
    (mul_equiv (hf.derivative a ha).property (hf.derivative b hb).property
      (g.eval a (hfg a ha)).property (g.eval b (hfg b hb)).property
      (hf.derivative_congr a b ha hb hab) (g.eval_congr a b _ _ hab))
    (mul_equiv (f.eval a ha).property (f.eval b hb).property
      (hg.derivative a (hfg a ha)).property (hg.derivative b (hfg b hb)).property
      (f.eval_congr a b ha hb hab) (hg.derivative_congr a b _ _ hab))
  continuousDerivative := sumContinuous _ _
    (productContinuous hf.derivative (fun z hz => g.eval z (hfg z hz))
      hf.continuousDerivative (restrictContinuous g.eval hg.continuous hfg))
    (productContinuous f.eval (fun z hz => hg.derivative z (hfg z hz))
      hf.continuous (restrictContinuous hg.derivative hg.continuousDerivative hfg))

def scalarNeg (a : Scalar) : Scalar := ⟨neg a.val, neg_valid a.property⟩

def negate (f : Map) : Map where
  domain := f.domain
  eval z hz := scalarNeg (f.eval z hz)
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := neg_equiv (f.eval_congr z w hz hw hzw)

theorem scalarNeg_difference (a b : Scalar) :
    (sub (scalarNeg a).val (scalarNeg b).val).Equiv (neg (sub a.val b.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarNeg a).property (scalarNeg b).property)
    (hright := neg_valid (sub_valid a.property b.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  change -A + -(-B) = -(A + -B)
  grind

theorem negate_remainder (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (z : Scalar) (hz : f.domain z) :
    (remainder (negate f) a ha (scalarNeg d) z hz).Equiv (neg (remainder f a ha d z hz)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _)
    (hright := neg_valid (remainder_valid _ _ _ _ _ _))
  let X := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let Y := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (-X + -(-Y)) + -((-D)*(Z + -A)) = -((X + -Y) + -(D*(Z + -A)))
  grind

def negateContinuous {D : Scalar → Prop} (f : ∀ z, D z → Scalar) (hf : ContinuousOn D f) :
    ContinuousOn D (fun z hz => scalarNeg (f z hz)) where
  delta := hf.delta
  estimate a ha eps z hz hza := Small.congr
    (neg_valid (sub_valid (f z hz).property (f a ha).property))
    (sub_valid (scalarNeg (f z hz)).property (scalarNeg (f a ha)).property)
    (equiv_symm (scalarNeg_difference _ _))
    (SeriesLimitLaws.small_neg (hf.estimate a ha eps z hz hza))

def negateDerivative (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (h : HasDerivativeAt f a ha d) : HasDerivativeAt (negate f) a ha (scalarNeg d) where
  delta := h.delta
  estimate eps H z hz hH hza := Small.congr (neg_valid (remainder_valid _ _ _ _ _ _))
    (remainder_valid _ _ _ _ _ _) (equiv_symm (negate_remainder f a ha d z hz))
    (SeriesLimitLaws.small_neg (h.estimate eps H z hz hH hza))

def Holomorphic.negate {f : Map} (hf : Holomorphic f) : Holomorphic (negate f) where
  openDomain := { radius := hf.openDomain.radius, inside := hf.openDomain.inside }
  derivative a ha := scalarNeg (hf.derivative a ha)
  atPoint a ha := negateDerivative f a ha _ (hf.atPoint a ha)
  derivative_congr a b ha hb hab := neg_equiv (hf.derivative_congr a b ha hb hab)
  continuousDerivative := negateContinuous hf.derivative hf.continuousDerivative

def derivativeMap (f : Map) (hf : Holomorphic f) : Map where
  domain := f.domain
  eval := hf.derivative
  domain_congr := f.domain_congr
  eval_congr := hf.derivative_congr

end ComputableAnalysis.RiemannHilbert.DomainFunctions
