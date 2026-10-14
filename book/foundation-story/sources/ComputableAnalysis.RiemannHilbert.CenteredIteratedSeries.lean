import ComputableAnalysis.RiemannHilbert.GeneralSeriesIteratedCoefficients
import ComputableAnalysis.RiemannHilbert.IteratedHolomorphicDerivatives
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Actual holomorphic series for every finite differentiated coefficient
profile. Derivative uniqueness identifies them with iterated derivatives
of any supplied holomorphic evaluator agreeing with the original series. -/
namespace ComputableAnalysis.RiemannHilbert.CenteredSeries
open ComplexRaw FunctionTheory LocalODE DomainFunctions BoundedSeries
set_option autoImplicit false
variable (p : Scalar) (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (C K : Rat) (R : QPos) (hC : 0≤C) (hK : 0≤K)
    (hb : ∀ k, Small (c k) (C*K^k)) (hl : 8*K*R.val≤(1:Rat)/2)

def profileFunction (n : Nat) : DomainFunctions.Map :=
  function p (derivativeProfile c n) (derivativeProfile_valid c hc n)
    (derivativeProfileBound C K n) (derivativeProfileRate K n) (derivativeProfileRadius R n).val
    (derivativeProfileBound_nonneg C K hC hK n) (derivativeProfileRate_nonneg K hK n)
    (Rat.le_of_lt (derivativeProfileRadius R n).property) (derivativeProfile_majorant c hc C K hC hK hb n)
    (derivativeProfile_series_budget K R hl n)

def profileHolomorphic (n : Nat) : Holomorphic (profileFunction p c hc C K R hC hK hb hl n) :=
  holomorphic p (derivativeProfile c n) (derivativeProfile_valid c hc n)
    (derivativeProfileBound C K n) (derivativeProfileRate K n) (derivativeProfileRadius R n).val
    (derivativeProfileBound_nonneg C K hC hK n) (derivativeProfileRate_nonneg K hK n)
    (Rat.le_of_lt (derivativeProfileRadius R n).property) (derivativeProfile_majorant c hc C K hC hK hb n)
    (derivativeProfile_series_budget K R hl n)

theorem profile_center (n : Nat) : (profileFunction p c hc C K R hC hK hb hl n).domain p :=
  Centered.center_mem p (derivativeProfileRadius R n)

theorem profile_include (n : Nat) (z : Scalar) (hz : (profileFunction p c hc C K R hC hK hb hl (n+1)).domain z) :
    (profileFunction p c hc C K R hC hK hb hl n).domain z := by
  obtain ⟨r,hr,hrS,hsmall⟩ := hz
  exact ⟨r,hr,by have h := derivativeProfileRadius_step R n; grind only,hsmall⟩

theorem profile_original_domain (n : Nat) (z : Scalar) (hz : (profileFunction p c hc C K R hC hK hb hl n).domain z) :
    (profileFunction p c hc C K R hC hK hb hl 0).domain z := by
  obtain ⟨r,hr,hrS,hsmall⟩ := hz
  exact ⟨r,hr,by change r<R.val; have h := derivativeProfileRadius_le R n; grind only,hsmall⟩

theorem profile_value_center (n : Nat) :
    (profileFunction p c hc C K R hC hK hb hl n).eval p (profile_center p c hc C K R hC hK hb hl n)≈
      ⟨derivativeProfile c n 0,derivativeProfile_valid c hc n 0⟩ := by
  let D := derivativeProfileBound C K n
  let L := derivativeProfileRate K n
  let S := derivativeProfileRadius R n
  have hD := derivativeProfileBound_nonneg C K hC hK n
  have hL := derivativeProfileRate_nonneg K hK n
  have hS := Rat.le_of_lt S.property
  have hq : 0≤L*S.val := Rat.mul_nonneg hL hS
  have hbudget := derivativeProfile_series_budget K R hl n
  have hlocal : 2*L*S.val≤(1:Rat)/2 := by change 8*L*S.val≤(1:Rat)/2 at hbudget; grind only
  have he := coefficientSum_congr (derivativeProfile c n) (derivativeProfile c n) (Centered.offset p p).val zero
    (derivativeProfile_valid c hc n) (derivativeProfile_valid c hc n) (Centered.offset p p).property (ofQComplex_valid _)
    (fun k => equiv_refl _ (derivativeProfile_valid c hc n k)) (Centered.offset_self p) D L S.val hD hL hS
    (derivativeProfile_majorant c hc C K hC hK hb n) (interior_bound _ _ (profile_center p c hc C K R hC hK hb hl n)) hlocal
  exact equiv_trans ((profileFunction p c hc C K R hC hK hb hl n).eval p _).property
    (coefficientSum_valid _ zero (derivativeProfile_valid c hc n) (ofQComplex_valid _) D L S.val hD hL hS
      (derivativeProfile_majorant c hc C K hC hK hb n) (Small.zero hS) hlocal)
    (derivativeProfile_valid c hc n 0) he
    (coefficientSum_zero _ (derivativeProfile_valid c hc n) D L S.val hD hL hS
      (derivativeProfile_majorant c hc C K hC hK hb n) hlocal)

/-- The next actual series is the actual derivative of the preceding one. -/
theorem profile_derivative (n : Nat) (z : Scalar) (hz : (profileFunction p c hc C K R hC hK hb hl (n+1)).domain z) :
    (profileFunction p c hc C K R hC hK hb hl (n+1)).eval z hz≈
      (profileHolomorphic p c hc C K R hC hK hb hl n).derivative z (profile_include p c hc C K R hC hK hb hl n z hz) := by
  let D := derivativeProfileBound C K n
  let L := derivativeProfileRate K n
  let S := derivativeProfileRadius R n
  let T := derivativeProfileRadius R (n+1)
  have hD := derivativeProfileBound_nonneg C K hC hK n
  have hL := derivativeProfileRate_nonneg K hK n
  have hS := Rat.le_of_lt S.property
  have hT := Rat.le_of_lt T.property
  have hqS : 0≤L*S.val := Rat.mul_nonneg hL hS
  have hqT : 0≤L*T.val := Rat.mul_nonneg hL hT
  have hbudget := derivativeProfile_series_budget K R hl n
  have hbudgetT := derivativeProfile_series_budget K R hl (n+1)
  have hlocal : 4*L*S.val≤(1:Rat)/2 := by change 8*L*S.val≤(1:Rat)/2 at hbudget; grind only
  have hlocalT : 4*L*T.val≤(1:Rat)/2 := by change 8*(2*L)*T.val≤(1:Rat)/2 at hbudgetT; grind only
  exact derivativeCoefficients_sum (derivativeProfile c n) (derivativeProfile_valid c hc n)
    (Centered.offset p z).val (Centered.offset p z).property D L S.val T.val hD hL hS hT
    (derivativeProfile_majorant c hc C K hC hK hb n)
    (interior_bound _ _ (profile_include p c hc C K R hC hK hb hl n z hz)) (interior_bound _ _ hz) hlocal hlocalT

/-- Supplied exact evaluator agreement transports every finite actual derivative.
The original coefficient bound is justified evidence; higher derivative agreement is proved. -/
theorem profile_iterated_agreement (f : DomainFunctions.Map) (hf : Holomorphic f)
    (hi : ∀ z, (profileFunction p c hc C K R hC hK hb hl 0).domain z → f.domain z)
    (he : ∀ z hz, (profileFunction p c hc C K R hC hK hb hl 0).eval z hz≈f.eval z (hi z hz))
    (n : Nat) (z : Scalar) (hz : (profileFunction p c hc C K R hC hK hb hl n).domain z) :
    (profileFunction p c hc C K R hC hK hb hl n).eval z hz≈
      (iteratedDerivativeMap f hf n).eval z ((iteratedDerivative_domain f hf n z).2
        (hi z (profile_original_domain p c hc C K R hC hK hb hl n z hz))) := by
  induction n generalizing z with
  | zero => exact he z hz
  | succ n ih =>
    let hp := profile_include p c hc C K R hC hK hb hl n z hz
    let hzF := (iteratedDerivative_domain f hf n z).2 (hi z (profile_original_domain p c hc C K R hC hK hb hl n z hp))
    have hder := (profileHolomorphic p c hc C K R hC hK hb hl n).derivative_equiv_on_overlap
      (iteratedDerivativeHolomorphic f hf n) (fun w hw _ => ih w hw) z hp hzF
    exact Setoid.trans (b := (profileHolomorphic p c hc C K R hC hK hb hl n).derivative z hp)
      (profile_derivative p c hc C K R hC hK hb hl n z hz) hder

/-- Factorial-scaled coefficient identity at an arbitrary represented center. -/
theorem profile_factorial_derivative (f : DomainFunctions.Map) (hf : Holomorphic f)
    (hi : ∀ z, (profileFunction p c hc C K R hC hK hb hl 0).domain z → f.domain z)
    (he : ∀ z hz, (profileFunction p c hc C K R hC hK hb hl 0).eval z hz≈f.eval z (hi z hz))
    (n : Nat) (hp : f.domain p) :
    (iteratedDerivativeMap f hf n).eval p ((iteratedDerivative_domain f hf n p).2 hp)≈
      ⟨scaleRat (factorialRat n) (c n),scaleRat_valid (hc n)⟩ := by
  exact Setoid.trans (equiv_symm (profile_iterated_agreement p c hc C K R hC hK hb hl f hf hi he n p
    (profile_center p c hc C K R hC hK hb hl n)))
    (Setoid.trans (b := (⟨derivativeProfile c n 0,derivativeProfile_valid c hc n 0⟩ : Scalar))
      (profile_value_center p c hc C K R hC hK hb hl n) (derivativeProfile_initial c hc n))

end ComputableAnalysis.RiemannHilbert.CenteredSeries
