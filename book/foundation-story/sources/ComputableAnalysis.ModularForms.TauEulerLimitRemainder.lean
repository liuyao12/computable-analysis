import ComputableAnalysis.ModularForms.TauUniformQuadraticBudget
import ComputableAnalysis.ModularForms.TauEulerDerivativeLimit

/-! Passing uniform quadratic remainders to the actual Euler-product limit. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The constructed slope limit has a quadratic remainder for the actual
infinite Euler product, proved by passage from finite analytic remainders. -/
theorem tauEulerNomeMap_quadratic_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder tauEulerNomeMap a ha
      (tauEulerNomeDerivativeCandidate a ha) z hz) (13*tauEulerFactorRemainderConstant*H^2) := by
  let F := tauEulerNomeMap.eval z hz
  let G := tauEulerNomeMap.eval a ha
  let D := tauEulerNomeDerivativeCandidate a ha
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let e := fun N => tauEulerProductTail (1/1024) (N+1)+
    tauEulerProductTail (1/1024) (N+1)+2*tauEulerDerivativeTail (1/1024) (N+1)*H
  have hprod := SeriesLimitLaws.shrinks_shift _
    (tauEulerProductTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl) 1
  have hder := SeriesLimitLaws.shrinks_shift _
    (tauEulerDerivativeTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl) 1
  have hscale := SeriesLimitLaws.shrinks_scale _ hder (2*H)
    (Rat.mul_nonneg (by decide +kernel) hH)
  have he : ShrinksToZero e := by
    have hs := RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ hprod hprod) hscale
    have heq : e=(fun N =>
      (tauEulerProductTail (1/1024) (N+1)+tauEulerProductTail (1/1024) (N+1))+
        (2*H)*tauEulerDerivativeTail (1/1024) (N+1)) := by
      funext N
      dsimp [e]
      grind only
    rw [heq]
    exact hs
  apply SeriesLimitLaws.small_of_prefix_bound _
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (fun N => DomainFunctions.remainder (finiteDiscriminantEulerMap (N+1)) a trivial
      ((finiteDiscriminantEulerMap_holomorphic (N+1)).derivative a trivial) z trivial)
    (fun N => DomainFunctions.remainder_valid _ _ _ _ _ _) _ e he
  · intro N
    have hv : 0≤tauEulerDerivativeTail (1/1024) (N+1) := by
      unfold tauEulerDerivativeTail
      exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
    exact SeriesLimitLaws.remainder_close F.val G.val D.val
      (finiteDiscriminantEulerProduct z (N+1)).val (finiteDiscriminantEulerProduct a (N+1)).val
      ((finiteDiscriminantEulerMap_holomorphic (N+1)).derivative a trivial).val h.val
      F.property G.property D.property (finiteDiscriminantEulerProduct z (N+1)).property
      (finiteDiscriminantEulerProduct a (N+1)).property
      ((finiteDiscriminantEulerMap_holomorphic (N+1)).derivative a trivial).property h.property
      _ _ _ H hv hH
      (tauEulerProduct_close_prefix z (1/1024) (by decide +kernel) Rat.le_refl
        (LocalODE.interior_bound _ z hz) (N+1))
      (tauEulerProduct_close_prefix a (1/1024) (by decide +kernel) Rat.le_refl
        (LocalODE.interior_bound _ a ha) (N+1))
      (tauEulerDerivativeValue_close_actual_prefix a (1/1024) (by decide +kernel) Rat.le_refl
        (LocalODE.interior_bound _ a ha) (N+1)) hza
  · intro N
    exact finiteDiscriminantEuler_actual_remainder_uniform_bound a z (1/1024) H
      (by decide +kernel) Rat.le_refl hH (LocalODE.interior_bound _ a ha)
      (LocalODE.interior_bound _ z hz) hza N

/-- An executable derivative radius for the actual infinite Euler product. -/
def tauEulerNomeMap_hasDerivativeAt (a : Scalar) (ha : tauEulerNomeDomain a) :
    HasDerivativeAt tauEulerNomeMap a ha (tauEulerNomeDerivativeCandidate a ha) where
  delta eps := divideRadius eps ⟨13*tauEulerFactorRemainderConstant+1,by decide +kernel⟩
  estimate eps H z hz hd hza := by
    have h := tauEulerNomeMap_quadratic_remainder_bound a z ha hz H.val
      (Rat.le_of_lt H.property) hza
    have hi := divideRadius_identity eps ⟨13*tauEulerFactorRemainderConstant+1,by decide +kernel⟩
    have hm := Rat.mul_le_mul_of_nonneg_right hd
      (show (0:Rat)≤13*tauEulerFactorRemainderConstant+1 by decide +kernel)
    have hcH : 13*tauEulerFactorRemainderConstant*H.val≤eps.val := by grind only
    have hf := Rat.mul_le_mul_of_nonneg_right hcH (Rat.le_of_lt H.property)
    apply h.mono
    rw [Rat.pow_succ,Rat.pow_one]
    grind only

/-- Genuine holomorphicity of the executable infinite Euler product.
Only the previously proved continuity witness uses proof-only choice. -/
noncomputable def tauEulerNomeMap_holomorphic : Holomorphic tauEulerNomeMap where
  openDomain := {
    radius := tauEulerNomeDomain_openData.radius
    inside := tauEulerNomeDomain_openData.inside }
  derivative := tauEulerNomeDerivativeCandidate
  atPoint := tauEulerNomeMap_hasDerivativeAt
  derivative_congr a b ha hb he := tauEulerDerivativeValue_congr a b (1/1024) (1/1024)
    (by decide +kernel) (by decide +kernel) Rat.le_refl Rat.le_refl
    (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ b hb) he
  continuousDerivative := Classical.choice tauEulerNomeDerivativeCandidate_continuous

end ComputableAnalysis.ModularForms
