import ComputableAnalysis.RiemannHilbert.GeneralSeriesDerivativeSeries

/-! Executable repeated coefficient differentiation, with proved rising
factorial identities and geometric majorants at every finite order. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def derivativeProfile (c : Nat → ComplexRaw) : Nat → Nat → ComplexRaw
  | 0 => c
  | n+1 => derivativeCoefficients (derivativeProfile c n)

theorem derivativeProfile_valid (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid) (n k : Nat) :
    (derivativeProfile c n k).Valid := by
  induction n generalizing k with
  | zero => exact hc k
  | succ n ih => exact derivativeCoefficients_valid _ ih k

theorem derivativeProfile_congr (c d : Nat → ComplexRaw) (_hc : ∀ k, (c k).Valid) (_hd : ∀ k, (d k).Valid)
    (he : ∀ k, (c k).Equiv (d k)) (n k : Nat) : (derivativeProfile c n k).Equiv (derivativeProfile d n k) := by
  induction n generalizing k with
  | zero => exact he k
  | succ n ih => exact scaleRat_equiv (ih (k+1))

def risingFactorialRat (k : Nat) : Nat → Rat
  | 0 => 1
  | n+1 => ((k+n+1:Nat):Rat)*risingFactorialRat k n

theorem risingFactorialRat_front (k n : Nat) :
    risingFactorialRat k (n+1)=((k+1:Nat):Rat)*risingFactorialRat (k+1) n := by
  induction n with
  | zero => simp only [risingFactorialRat,Nat.add_zero,Rat.mul_one]
  | succ n ih =>
    change ((k+(n+1)+1:Nat):Rat)*risingFactorialRat k (n+1)=
      ((k+1:Nat):Rat)*(((k+1+n+1:Nat):Rat)*risingFactorialRat (k+1) n)
    rw [ih,show k+(n+1)+1=k+1+n+1 by omega]
    grind only

theorem risingFactorialRat_zero (n : Nat) : risingFactorialRat 0 n=factorialRat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [risingFactorialRat,FormalPowerSeries.factorialRat_succ,ih,Nat.zero_add]

theorem risingFactorialRat_pos (k n : Nat) : 0<risingFactorialRat k n := by
  induction n with
  | zero => change (0:Rat)<1; decide +kernel
  | succ n ih => exact Rat.mul_pos (Rat.natCast_pos.mpr (by omega)) ih

/-- Each repeated coefficient operation equals its explicit finite rising-factorial formula. -/
theorem derivativeProfile_formula (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid) (n k : Nat) :
    (derivativeProfile c n k).Equiv (scaleRat (risingFactorialRat k n) (c (k+n))) := by
  induction n generalizing k with
  | zero => simpa only [Nat.add_zero,risingFactorialRat,derivativeProfile] using equiv_symm (scaleRat_one_equiv (c k) (hc k))
  | succ n ih =>
    change (scaleRat ((k+1:Nat):Rat) (derivativeProfile c n (k+1))).Equiv
      (scaleRat (risingFactorialRat k (n+1)) (c (k+(n+1))))
    have hi := scaleRat_equiv (r := ((k+1:Nat):Rat)) (ih (k+1))
    have hs := scaleRat_scaleRat_equiv ((k+1:Nat):Rat) (risingFactorialRat (k+1) n) (c (k+1+n)) (hc (k+1+n))
    rw [←risingFactorialRat_front,show k+1+n=k+(n+1) by omega] at hs
    rw [show k+1+n=k+(n+1) by omega] at hi
    exact equiv_trans (derivativeProfile_valid c hc (n+1) k)
      (scaleRat_valid (scaleRat_valid (hc (k+(n+1))))) (scaleRat_valid (hc (k+(n+1)))) hi hs

theorem derivativeProfile_initial (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid) (n : Nat) :
    (derivativeProfile c n 0).Equiv (scaleRat (factorialRat n) (c n)) := by
  simpa only [risingFactorialRat_zero,Nat.zero_add] using derivativeProfile_formula c hc n 0

def derivativeProfileRate (K : Rat) : Nat → Rat
  | 0 => K
  | n+1 => 2*derivativeProfileRate K n

def derivativeProfileBound (C K : Rat) : Nat → Rat
  | 0 => C
  | n+1 => derivativeProfileBound C K n*derivativeProfileRate K n

def derivativeProfileRadius (R : QPos) : Nat → QPos
  | 0 => R
  | n+1 => divideRadius (derivativeProfileRadius R n) ⟨2,by decide +kernel⟩

theorem derivativeProfileRate_nonneg (K : Rat) (hK : 0≤K) (n : Nat) : 0≤derivativeProfileRate K n := by
  induction n with
  | zero => exact hK
  | succ n ih => exact Rat.mul_nonneg (by decide +kernel) ih

theorem derivativeProfileBound_nonneg (C K : Rat) (hC : 0≤C) (hK : 0≤K) (n : Nat) : 0≤derivativeProfileBound C K n := by
  induction n with
  | zero => exact hC
  | succ n ih => exact Rat.mul_nonneg ih (derivativeProfileRate_nonneg K hK n)

theorem derivativeProfileRadius_identity (R : QPos) (n : Nat) :
    2*(derivativeProfileRadius R (n+1)).val=(derivativeProfileRadius R n).val :=
  divideRadius_identity (derivativeProfileRadius R n) (⟨2,by decide +kernel⟩ : QPos)

theorem derivativeProfileRadius_step (R : QPos) (n : Nat) :
    (derivativeProfileRadius R (n+1)).val<(derivativeProfileRadius R n).val := by
  have h := derivativeProfileRadius_identity R n
  have hp := (derivativeProfileRadius R (n+1)).property
  grind only

theorem derivativeProfileRadius_le (R : QPos) (n : Nat) : (derivativeProfileRadius R n).val≤R.val := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih => exact Rat.le_trans (Rat.le_of_lt (derivativeProfileRadius_step R n)) ih

theorem derivativeProfile_rate_radius (K : Rat) (R : QPos) (n : Nat) :
    derivativeProfileRate K n*(derivativeProfileRadius R n).val=K*R.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (2*derivativeProfileRate K n)*(derivativeProfileRadius R (n+1)).val=K*R.val
    rw [show (2*derivativeProfileRate K n)*(derivativeProfileRadius R (n+1)).val=
      derivativeProfileRate K n*(2*(derivativeProfileRadius R (n+1)).val) by grind only,derivativeProfileRadius_identity]
    exact ih

theorem derivativeProfile_series_budget (K : Rat) (R : QPos) (hl : 8*K*R.val≤(1:Rat)/2) (n : Nat) :
    8*derivativeProfileRate K n*(derivativeProfileRadius R n).val≤(1:Rat)/2 := by
  rw [Rat.mul_assoc,derivativeProfile_rate_radius,←Rat.mul_assoc]
  exact hl

theorem derivativeProfile_majorant (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (C K : Rat) (hC : 0≤C) (hK : 0≤K) (hb : ∀ k, Small (c k) (C*K^k)) (n k : Nat) :
    Small (derivativeProfile c n k) (derivativeProfileBound C K n*(derivativeProfileRate K n)^k) := by
  induction n generalizing k with
  | zero => exact hb k
  | succ n ih =>
    exact derivativeCoefficients_majorant _ (derivativeProfile_valid c hc n) _ _
      (derivativeProfileBound_nonneg C K hC hK n) (derivativeProfileRate_nonneg K hK n) ih k

end ComputableAnalysis.RiemannHilbert.BoundedSeries
