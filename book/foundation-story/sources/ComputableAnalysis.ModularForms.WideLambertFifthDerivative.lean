import ComputableAnalysis.ModularForms.WideLambertFifthValueRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def wideLambertFifthDomain (q : Scalar) : Prop := LocalODE.interior (1/64:Rat) q

def wideLambertFifthDomain_openData : ScalarTopology.OpenData wideLambertFifthDomain where
  invariant q w he := ⟨Centered.interior_congr _ q w he,
    Centered.interior_congr _ w q (equiv_symm he)⟩
  radius := LocalODE.interiorRadius (1/64:Rat)
  inside := LocalODE.interiorRadius_inside (1/64:Rat)

/-- Actual executable larger-disk evaluator with represented-value invariance. -/
def wideLambertFifthMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := wideLambertFifthValue q (LocalODE.interior_bound _ q hq)
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := wideLambertFifthValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he

/-- The wider slope sum is the actual derivative at every represented point of the open disk. -/
def wideLambertFifthMap_hasDerivativeAt (a : Scalar) (ha : wideLambertFifthDomain a) :
    HasDerivativeAt wideLambertFifthMap a ha
      (wideLambertFifthSlopeValue a (LocalODE.interior_bound _ a ha)) where
  delta eps := divideRadius eps (⟨135168,by decide +kernel⟩ : QPos)
  estimate eps H z hz hH hd := by
    have hb := wideLambertFifthValue_remainder_bound a z (LocalODE.interior_bound _ a ha)
      (LocalODE.interior_bound _ z hz) H.val (Rat.le_of_lt H.property) hd
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤135168 by decide +kernel)
    rw [divideRadius_identity eps (⟨135168,by decide +kernel⟩ : QPos)] at hm
    have hh := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    apply hb.mono
    change 135168*H.val≤eps.val at hm
    rw [Rat.pow_succ H.val 1,Rat.pow_one]
    grind only

/-- The original chart lies in the wider open domain without an extra radius hypothesis. -/
theorem tauEulerNomeDomain_wide_fifth_mem (q : Scalar) (hq : tauEulerNomeDomain q) :
    wideLambertFifthDomain q := by
  obtain ⟨r,hr,hrR,hq⟩ := hq
  have h : (1:Rat)/1024<(1:Rat)/64 := by decide +kernel
  exact ⟨r,hr,(by grind only),hq⟩

/-- Exact evaluator agreement on the original chart, with wider domain evidence constructed. -/
theorem wideLambertFifthMap_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideLambertFifthMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (tauHigherLambertValue q hq 5 (by decide +kernel)).val :=
  wideLambertFifthValue_tau_agreement q hq _
end ComputableAnalysis.ModularForms
