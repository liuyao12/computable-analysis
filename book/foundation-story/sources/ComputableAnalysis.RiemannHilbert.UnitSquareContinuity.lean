import ComputableAnalysis.RiemannHilbert.UnitSquareTopology
import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments
import ComputableAnalysis.RiemannHilbert.DomainProductRule

/-! Executable continuity moduli for actual scalar expressions in two
represented unit parameters. Sum, negation and product estimates use the
proved finite rational scalar bounds. -/
namespace ComputableAnalysis.RiemannHilbert.UnitSquare
open ComplexRaw FunctionTheory DomainFunctions

structure ScalarContinuousData (f : Point → Scalar) where
  congr : ∀ s t, s ≈ t → f s ≈ f t
  delta : Point → QPos → QPos
  estimate : ∀ s eps t, Near s t (delta s eps) → Small (sub (f t).val (f s).val) eps.val

theorem ScalarContinuousData.continuous {f : Point → Scalar} (hf : ScalarContinuousData f)
    (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) : IsOpen (fun s => D (f s)) where
  invariant s t hst := hD.invariant _ _ (hf.congr s t hst)
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hD.neighborhood (f s) hs
    exact ⟨hf.delta s r,fun t ht => hr (f t) (hf.estimate s r t ht)⟩

def first {f : UnitInterval.Point → Scalar} (hf : UnitInterval.ScalarContinuousData f) : ScalarContinuousData (fun s : Point => f s.1) where
  congr s t hst := hf.congr s.1 t.1 hst.1
  delta s eps := hf.delta s.1 eps
  estimate s eps t ht := hf.estimate s.1 eps t.1 ht.1

def second {f : UnitInterval.Point → Scalar} (hf : UnitInterval.ScalarContinuousData f) : ScalarContinuousData (fun s : Point => f s.2) where
  congr s t hst := hf.congr s.2 t.2 hst.2
  delta s eps := hf.delta s.2 eps
  estimate s eps t ht := hf.estimate s.2 eps t.2 ht.2

def ScalarContinuousData.diagonal {f : Point → Scalar} (hf : ScalarContinuousData f) :
    UnitInterval.ScalarContinuousData (fun t => f (t,t)) where
  congr s t hst := hf.congr (s,s) (t,t) ⟨hst,hst⟩
  delta s eps := hf.delta (s,s) eps
  estimate s eps t ht := hf.estimate (s,s) eps (t,t) ⟨ht,ht⟩

def parameterContinuousData : UnitInterval.ScalarContinuousData UnitInterval.scalar where
  congr _ _ h := UnitInterval.scalar_congr h
  delta _ eps := eps
  estimate _ _ _ ht := ht

def ScalarContinuousData.neg {f : Point → Scalar} (hf : ScalarContinuousData f) :
    ScalarContinuousData (fun s => scalarNeg (f s)) where
  congr s t hst := neg_equiv (hf.congr s t hst)
  delta := hf.delta
  estimate s eps t ht := by
    have he : (sub (scalarNeg (f t)).val (scalarNeg (f s)).val).Equiv
        (sub (f s).val (f t).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (scalarNeg (f t)).property (scalarNeg (f s)).property)
        (hright := sub_valid (f s).property (f t).property)
      let S := ComplexRawQuotient.ofRaw (f s).val (f s).property
      let T := ComplexRawQuotient.ofRaw (f t).val (f t).property
      change -T-(-S)=S-T
      grind only
    exact Small.congr (sub_valid (f s).property (f t).property)
      (sub_valid (scalarNeg (f t)).property (scalarNeg (f s)).property) (equiv_symm he)
      (RepresentedCauchySum.small_sub_symm _ _ _ (hf.estimate s eps t ht))

def ScalarContinuousData.add {f g : Point → Scalar} (hf : ScalarContinuousData f) (hg : ScalarContinuousData g) :
    ScalarContinuousData (fun s => scalarSum (f s) (g s)) where
  congr s t hst := add_equiv (hf.congr s t hst) (hg.congr s t hst)
  delta s eps := minRadius (hf.delta s (halfError eps)) (hg.delta s (halfError eps))
  estimate s eps t ht := by
    have hF := hf.estimate s (halfError eps) t (ht.mono (minRadius_left _ _))
    have hG := hg.estimate s (halfError eps) t (ht.mono (minRadius_right _ _))
    have hb := LocalODE.small_add hF hG
    have he : (halfError eps).val+(halfError eps).val=eps.val := by
      have h := halfError_identity eps
      grind only
    rw [he] at hb
    exact Small.congr (add_valid (sub_valid (f t).property (f s).property) (sub_valid (g t).property (g s).property))
      (sub_valid (scalarSum (f t) (g t)).property (scalarSum (f s) (g s)).property)
      (equiv_symm (SeriesLimitLaws.addition_difference _ _ _ _ (f t).property (f s).property (g t).property (g s).property)) hb

def ScalarContinuousData.product {f g : Point → Scalar} (hf : ScalarContinuousData f) (hg : ScalarContinuousData g) :
    ScalarContinuousData (fun s => scalarProduct (f s) (g s)) where
  congr s t hst := mul_equiv (f s).property (f t).property (g s).property (g t).property (hf.congr s t hst) (hg.congr s t hst)
  delta s eps := minRadius (hg.delta s unitError)
    (minRadius (hf.delta s (productLeftError eps (g s))) (hg.delta s (productRightError eps (f s))))
  estimate s eps t ht := by
    let alpha := productLeftError eps (g s)
    let beta := productRightError eps (f s)
    have h1 := hg.estimate s unitError t (ht.mono (minRadius_left _ _))
    have hrest := ht.mono (minRadius_right (hg.delta s unitError)
      (minRadius (hf.delta s alpha) (hg.delta s beta)))
    have hF := hf.estimate s alpha t (hrest.mono (minRadius_left _ _))
    have hG := hg.estimate s beta t (hrest.mono (minRadius_right _ _))
    have hsum := LocalODE.small_add (scalar_small (g s)) h1
    have hgt : Small (g t).val (scalarBound (g s)+1) := Small.congr
      (add_valid (g s).property (sub_valid (g t).property (g s).property)) (g t).property
      (SeriesLimitLaws.add_difference _ _ (g t).property (g s).property) hsum
    have hl := Small.mul (sub_valid (f t).property (f s).property) (g t).property
      (Rat.le_of_lt alpha.property) (by have h := scalarBound_pos (g s); grind only) hF hgt
    have hr := Small.mul (f s).property (sub_valid (g t).property (g s).property)
      (Rat.le_of_lt (scalarBound_pos _)) (Rat.le_of_lt beta.property) (scalar_small _) hG
    exact Small.congr
      (add_valid (mul_valid (sub_valid (f t).property (f s).property) (g t).property)
        (mul_valid (f s).property (sub_valid (g t).property (g s).property)))
      (sub_valid (scalarProduct (f t) (g t)).property (scalarProduct (f s) (g s)).property)
      (equiv_symm (scalarProduct_difference _ _ _ _))
      ((LocalODE.small_add hl hr).mono (product_error_bound eps (f s) (g s)))

def interpolationContinuousData {f g : UnitInterval.Point → Scalar}
    (hf : UnitInterval.ScalarContinuousData f) (hg : UnitInterval.ScalarContinuousData g) :
    ScalarContinuousData (fun s : Point => RepresentedAffineSegment.point (f s.2) (g s.2) s.1) :=
  (second hf).add (((second hg).add (second hf).neg).product (first parameterContinuousData))

end ComputableAnalysis.RiemannHilbert.UnitSquare
