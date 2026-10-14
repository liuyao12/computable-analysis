import ComputableAnalysis.ModularForms.WideEulerTailUniformRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Executable actual infinite Euler tail on the wider open nome disk. -/
def wideEulerTailNomeMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := wideEulerTailValue q (LocalODE.interior_bound _ q hq)
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := wideEulerTailValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he

/-- The constructed slope limit has a quadratic remainder for the actual
infinite Euler product, proved by passage from finite analytic remainders. -/
theorem wideEulerTailNomeMap_quadratic_remainder_bound (a z : Scalar)
    (ha : wideLambertFifthDomain a) (hz : wideLambertFifthDomain z) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder wideEulerTailNomeMap a ha
      (wideEulerTailDerivativeCandidate a ha) z hz) (2*tauEulerFactorRemainderConstant*H^2) := by
  let F := wideEulerTailNomeMap.eval z hz
  let G := wideEulerTailNomeMap.eval a ha
  let D := wideEulerTailDerivativeCandidate a ha
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let e := fun N => wideEulerTailError (N+1)+
    wideEulerTailError (N+1)+2*wideEulerTailDerivativeError (N+1)*H
  have hprod := SeriesLimitLaws.shrinks_shift _
    wideEulerTailError_shrinks 1
  have hder := SeriesLimitLaws.shrinks_shift _
    wideEulerTailDerivativeError_shrinks 1
  have hscale := SeriesLimitLaws.shrinks_scale _ hder (2*H)
    (Rat.mul_nonneg (by decide +kernel) hH)
  have he : ShrinksToZero e := by
    have hs := RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ hprod hprod) hscale
    have heq : e=(fun N =>
      (wideEulerTailError (N+1)+wideEulerTailError (N+1))+
        (2*H)*wideEulerTailDerivativeError (N+1)) := by
      funext N
      dsimp [e]
      grind only
    rw [heq]
    exact hs
  apply SeriesLimitLaws.small_of_prefix_bound _
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (fun N => DomainFunctions.remainder (wideEulerTailMap (N+1)) a trivial
      ((wideEulerTailMap_holomorphic (N+1)).derivative a trivial) z trivial)
    (fun N => DomainFunctions.remainder_valid _ _ _ _ _ _) _ e he
  · intro N
    have hv : 0≤wideEulerTailDerivativeError (N+1) := by
      unfold wideEulerTailDerivativeError
      exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
    exact SeriesLimitLaws.remainder_close F.val G.val D.val
      (wideEulerTailPrefix z (N+1)).val (wideEulerTailPrefix a (N+1)).val
      ((wideEulerTailMap_holomorphic (N+1)).derivative a trivial).val h.val
      F.property G.property D.property (wideEulerTailPrefix z (N+1)).property
      (wideEulerTailPrefix a (N+1)).property
      ((wideEulerTailMap_holomorphic (N+1)).derivative a trivial).property h.property
      _ _ _ H hv hH
      (wideEulerTailValue_close_prefix z
        (LocalODE.interior_bound _ z hz) (N+1))
      (wideEulerTailValue_close_prefix a
        (LocalODE.interior_bound _ a ha) (N+1))
      (wideEulerTailDerivativeValue_close_actual_prefix a
        (LocalODE.interior_bound _ a ha) (N+1)) hza
  · intro N
    exact wideEulerTailMap_actual_remainder_uniform_bound a z (LocalODE.interior_bound _ a ha)
      (LocalODE.interior_bound _ z hz) H hH hza (N+1)

/-- An executable derivative radius for the actual infinite Euler product. -/
def wideEulerTailNomeMap_hasDerivativeAt (a : Scalar) (ha : wideLambertFifthDomain a) :
    HasDerivativeAt wideEulerTailNomeMap a ha (wideEulerTailDerivativeCandidate a ha) where
  delta eps := divideRadius eps ⟨2*tauEulerFactorRemainderConstant+1,by decide +kernel⟩
  estimate eps H z hz hd hza := by
    have h := wideEulerTailNomeMap_quadratic_remainder_bound a z ha hz H.val
      (Rat.le_of_lt H.property) hza
    have hi := divideRadius_identity eps ⟨2*tauEulerFactorRemainderConstant+1,by decide +kernel⟩
    have hm := Rat.mul_le_mul_of_nonneg_right hd
      (show (0:Rat)≤2*tauEulerFactorRemainderConstant+1 by decide +kernel)
    have hcH : 2*tauEulerFactorRemainderConstant*H.val≤eps.val := by grind only
    have hf := Rat.mul_le_mul_of_nonneg_right hcH (Rat.le_of_lt H.property)
    apply h.mono
    rw [Rat.pow_succ,Rat.pow_one]
    grind only

/-- Genuine holomorphicity of the executable infinite Euler product.
Only the previously proved continuity witness uses proof-only choice. -/
noncomputable def wideEulerTailNomeMap_holomorphic : Holomorphic wideEulerTailNomeMap where
  openDomain := {
    radius := wideLambertFifthDomain_openData.radius
    inside := wideLambertFifthDomain_openData.inside }
  derivative := wideEulerTailDerivativeCandidate
  atPoint := wideEulerTailNomeMap_hasDerivativeAt
  derivative_congr a b ha hb he := wideEulerTailDerivativeValue_congr a b
    (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ b hb) he
  continuousDerivative := Classical.choice wideEulerTailDerivativeCandidate_continuous


end ComputableAnalysis.ModularForms
