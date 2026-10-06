import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Derivative witnesses transport across equivalent derivative and
base-point representations, preserving the complete remainder estimates. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def HasDerivativeAt.congrDerivative {f : Map} {a : Scalar} {ha : f.domain a} {d e : Scalar}
    (h : HasDerivativeAt f a ha d) (hde : d.val.Equiv e.val) : HasDerivativeAt f a ha e where
  delta := h.delta
  estimate eps H z hz hH hza := Small.congr (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _)
    (FunctionTheory.sub_congr (equiv_refl _ (sub_valid (f.eval z hz).property (f.eval a ha).property))
      (mul_equiv d.property e.property (sub_valid z.property a.property) (sub_valid z.property a.property)
        hde (equiv_refl _ (sub_valid z.property a.property))))
    (h.estimate eps H z hz hH hza)

def HasDerivativeAt.congrPoint {f : Map} {a b : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasDerivativeAt f a ha d) (hb : f.domain b) (hab : a.val.Equiv b.val) : HasDerivativeAt f b hb d where
  delta := h.delta
  estimate eps H z hz hH hzb := by
    have hza := Small.congr (sub_valid z.property b.property) (sub_valid z.property a.property)
      (FunctionTheory.sub_congr (equiv_refl _ z.property) (equiv_symm hab)) hzb
    exact Small.congr (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _)
      (FunctionTheory.sub_congr (FunctionTheory.sub_congr (equiv_refl _ (f.eval z hz).property)
        (f.eval_congr a b ha hb hab))
        (mul_equiv d.property d.property (sub_valid z.property a.property) (sub_valid z.property b.property)
          (equiv_refl _ d.property) (FunctionTheory.sub_congr (equiv_refl _ z.property) hab)))
      (h.estimate eps H z hz hH hza)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
