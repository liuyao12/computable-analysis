import ComputableAnalysis.RiemannHilbert.RationalNeighborhoods
import ComputableAnalysis.RiemannHilbert.DomainContinuity

/-! Exact agreement on rational points determines continuous represented
functions on an effective open domain. The approximating points are computed
from narrow rational boxes; no completed scalar or compactness is used. -/
namespace ComputableAnalysis.RiemannHilbert.RationalDensity
open ComplexRaw FunctionTheory DomainFunctions ScalarTopology
set_option autoImplicit false

theorem continuous_agreement {D : Scalar → Prop} (O : OpenData D)
    (f g : ∀ z, D z → Scalar) (hf : ContinuousOn D f) (hg : ContinuousOn D g)
    (he : ∀ (q : QComplex) (hq : D (rationalScalar q)),
      f (rationalScalar q) hq ≈ g (rationalScalar q) hq)
    (a : Scalar) (ha : D a) : f a ha ≈ g a ha := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun n => 2*(RepresentedCauchySum.error n).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks 2 (by decide))
  intro n
  let eps := RepresentedCauchySum.error n
  let r := minRadius (O.radius a ha) (minRadius (hf.delta a ha eps) (hg.delta a ha eps))
  let q := rationalCenter a r
  let b := rationalScalar q
  have hba : Small (sub b.val a.val) r.val := by
    have h := RepresentedCauchySum.small_sub_symm _ _ _ (rationalCenter_error a r)
    apply h.mono
    have hi := quarterRadius_identity r
    have hp := r.property
    grind only
  have hb : D b := O.inside a ha b (hba.mono (minRadius_left _ _))
  have hr := hba.mono (minRadius_right (O.radius a ha) _)
  have hfb := hf.estimate a ha eps b hb (hr.mono (minRadius_left _ _))
  have hgb := hg.estimate a ha eps b hb (hr.mono (minRadius_right _ _))
  have hmiddle : Small (sub (f b hb).val (g b hb).val) 0 := by
    exact Small.congr (ofQComplex_valid _) (sub_valid (f b hb).property (g b hb).property)
      (equiv_symm (equiv_trans (sub_valid (f b hb).property (g b hb).property)
        (sub_valid (g b hb).property (g b hb).property) (ofQComplex_valid _)
        (FunctionTheory.sub_congr (he q hb) (equiv_refl _ (g b hb).property))
        (add_neg_equiv _ (g b hb).property))) (Small.zero (by decide))
  have hsum := LocalODE.small_add
    (LocalODE.small_add (RepresentedCauchySum.small_sub_symm _ _ _ hfb) hmiddle) hgb
  have hv := SeriesLimitLaws.difference_via (f a ha).val (g a ha).val (f b hb).val (g b hb).val
    (f a ha).property (g a ha).property (f b hb).property (g b hb).property
  have hs := Small.congr
    (add_valid (add_valid (sub_valid (f a ha).property (f b hb).property)
      (sub_valid (f b hb).property (g b hb).property)) (sub_valid (g b hb).property (g a ha).property))
    (sub_valid (f a ha).property (g a ha).property) (equiv_symm hv) hsum
  exact hs.mono (by change eps.val+0+eps.val ≤ 0+2*eps.val; grind only)

end ComputableAnalysis.RiemannHilbert.RationalDensity
