import ComputableAnalysis.ModularForms.TauHigherLambertRemainder

/-! Actual holomorphic weighted Lambert values through degree five. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem ratio_local (k : Nat) (hk : k≤5) : weightedLambertRatio (1/1024) k≤(1:Rat)/2 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;> decide +kernel

theorem tauHigherLambertValue_congr (k : Nat) (hk : k≤5) (q w : Scalar)
    (hq : tauEulerNomeDomain q) (hw : tauEulerNomeDomain w) (he : q.val.Equiv w.val) :
    (tauHigherLambertValue q hq k hk).val.Equiv (tauHigherLambertValue w hw k hk).val :=
  weightedLambertSum_congr q w (1/1024) (1/1024) k
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw)
    (ratio_local k hk) (ratio_local k hk) he

def tauHigherLambertNomeMap (k : Nat) (hk : k≤5) : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := fun q hq => tauHigherLambertValue q hq k hk
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr := tauHigherLambertValue_congr k hk

private def remainderConstant (k : Nat) : QPos :=
  ⟨4096+67584*2^k, by
    have h : 0≤(2:Rat)^k := Rat.pow_nonneg (by decide +kernel)
    have hm := Rat.mul_nonneg (show (0:Rat)≤67584 by decide +kernel) h
    grind only⟩

/-- Actual differentiation of each infinite weighted Lambert construction. -/
def tauHigherLambertNomeMap_hasDerivativeAt (k : Nat) (hk : k≤5) (a : Scalar) (ha : tauEulerNomeDomain a) :
    HasDerivativeAt (tauHigherLambertNomeMap k hk) a ha (tauWeightedLambertSlopeValue a ha k hk) where
  delta eps := divideRadius eps (remainderConstant k)
  estimate eps H z hz hH hd := by
    have hb := tauHigherLambertValue_remainder_bound k hk a z ha hz H.val (Rat.le_of_lt H.property) hd
    have hm := Rat.mul_le_mul_of_nonneg_left hH (Rat.le_of_lt (remainderConstant k).property)
    rw [divideRadius_identity eps (remainderConstant k)] at hm
    have hp := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    change (4096+67584*(2:Rat)^k)*H.val*H.val≤eps.val*H.val at hp
    apply hb.mono
    change (4096+67584*(2:Rat)^k)*H.val≤eps.val at hm
    rw [Rat.pow_succ,Rat.pow_one]
    grind only

/-- Holomorphicity, including the proved continuous actual derivative. -/
noncomputable def tauHigherLambertNomeMap_holomorphic (k : Nat) (hk : k≤5) :
    Holomorphic (tauHigherLambertNomeMap k hk) where
  openDomain := ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
  derivative := fun q hq => tauWeightedLambertSlopeValue q hq k hk
  atPoint := tauHigherLambertNomeMap_hasDerivativeAt k hk
  derivative_congr := fun q w hq hw he => tauWeightedLambertSlopeValue_congr q w k hk hq hw he
  continuousDerivative := tauWeightedLambertSlopeMap_continuous k hk

end ComputableAnalysis.ModularForms
