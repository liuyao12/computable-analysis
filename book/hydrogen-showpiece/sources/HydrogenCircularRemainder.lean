import ComputableAnalysis.ComputableCoefficientErrorBounds
import ComputableAnalysis.HydrogenCircularLimits
import ComputableAnalysis.HydrogenTwoPLimit

/-! Explicit finite-coupling remainder bounds for the constructed circular
splittings and their exact regularized ratio. No measured constants enter. -/
namespace ComputableAnalysis.HydrogenCircularRemainder
open ComputableCoefficient QuotientBridge RationalLimits HydrogenCoupling HydrogenCircularComputations
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n
local instance : NatCast ComplexRawQuotient.Value :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).natCast

private theorem cast_two : ((2:Nat):Rat)=2 := by decide +kernel
private theorem cast_three : ((3:Nat):Rat)=3 := by decide +kernel

variable (A : Coupling) (e : Rat) (he : 0<e) (he1 : e≤1/8)
variable (hu : A.squared.preferred.Le (RealRaw.ofRat e))

include he he1 hu in
theorem exponent_near (k : Nat) (hk : 0<k) : Near (HydrogenCircularComputations.exponent k hk A) (k:Rat) e := by
  have hK := Rat.natCast_le_natCast.mpr (show 1≤k by omega)
  rw [show ((1:Nat):Rat)=1 by decide +kernel] at hK
  have hu' := HydrogenTwoPComputations.value_le A e hu
  have hm := Rat.mul_le_mul_of_nonneg_right hK (Rat.le_of_lt he)
  have hRad : Near (A.angularRadicand k) ((k:Rat)*(k:Rat)) ((k:Rat)*e) := by
    constructor
    · intro i j
      have h := hu' j 0
      change (A.value.real.compute j).lo≤e at h
      change (k:Rat)*(k:Rat)-(k:Rat)*e≤(k:Rat)*(k:Rat)+ -(A.value.real.compute j).lo
      grind only
    · intro i j
      have h := (A.bounded_interval i).1
      have ho := RealRaw.interval_order_of_valid _ A.bounded.valid i
      change 0≤(A.value.real.compute i).lo at h
      change (A.value.real.compute i).lo≤(A.value.real.compute i).hi at ho
      change (k:Rat)*(k:Rat)+ -(A.value.real.compute i).hi≤(k:Rat)*(k:Rat)+(k:Rat)*e
      grind only
  exact near_square_root _ _ (k:Rat) (Rat.natCast_pos.mpr hk) ⟨e,he⟩ (by grind only)
    (exponent_nonnegative k hk A) (A.angularRoot_square k hk) hRad

include he he1 hu in
theorem denominator_squared_near : Near (denominatorSquared 2 (by decide +kernel) A) 9 (2*e) := by
  have hs := exponent_near A e he he1 hu 2 (by decide +kernel)
  have hh := near_add (near_rational 5) (near_scale 2 (by decide +kernel) hs)
  have hr : (5:Rat)+2*2=9 := by decide +kernel
  rw [cast_two,hr,Rat.zero_add] at hh
  have heq : (Value.add (Value.rational 5) (Value.mul (Value.rational 2) (HydrogenCircularComputations.exponent 2 (by decide +kernel) A))).real.preferred.Equiv
      (denominatorSquared 2 (by decide +kernel) A).real.preferred := by
    have hInd := quotient_eq (indicial 2 (by decide +kernel) A)
    simp only [quotient_add,quotient_mul] at hInd
    change quotient (HydrogenCircularComputations.exponent 2 (by decide +kernel) A)*quotient (HydrogenCircularComputations.exponent 2 (by decide +kernel) A)+quotient A.value=2*2 at hInd
    apply raw_equiv_of_quotient_eq
    simp only [denominatorSquared,shifted,quotient_add,quotient_mul,quotient_one]
    change 5+2*quotient (HydrogenCircularComputations.exponent 2 (by decide +kernel) A)=
      (quotient (HydrogenCircularComputations.exponent 2 (by decide +kernel) A)+1)*(quotient (HydrogenCircularComputations.exponent 2 (by decide +kernel) A)+1)+quotient A.value
    grind only
  exact near_congr hh heq

include he he1 hu in
theorem denominator_near : Near (HydrogenCircularComputations.denominator 2 (by decide +kernel) A) 3 ((2/3)*e) := by
  apply near_square_root _ _ 3 (by decide +kernel) ⟨(2/3)*e,Rat.mul_pos (by decide +kernel) he⟩ (by grind only)
    (fun n => Rat.le_of_lt (HydrogenCircularComputations.denominator_positive 2 (by decide +kernel) A n))
    (denominator_square 2 (by decide +kernel) A)
  rw [show (3:Rat)*3=9 by decide +kernel]
  change Near (denominatorSquared 2 (by decide +kernel) A) 9 (3*((2/3)*e))
  rw [show (3:Rat)*((2/3)*e)=2*e by grind only]
  exact denominator_squared_near A e he he1 hu

include he he1 hu in
theorem denominator_inverse_near : Near (denominatorInverse 2 (by decide +kernel) A) (1/3) ((4/27)*e) := by
  have hh := near_positiveInv (show (0:Rat)<3 by decide +kernel)
    ⟨(2/3)*e,Rat.mul_pos (by decide +kernel) he⟩ (by change (2/3:Rat)*e≤3/2;grind only)
    (denominator_near A e he he1 hu) 0 (HydrogenCircularComputations.denominator_positive 2 (by decide +kernel) A 0)
  rw [show (3:Rat)⁻¹=1/3 by decide +kernel,
    show (inverseBudget 3 (by decide +kernel)).val=2/9 by decide +kernel] at hh
  exact near_mono hh (by grind only)

include he he1 hu in
theorem lower_energy_near : Near (lowerEnergy 2 (by decide +kernel) A) 1 e := by
  have hs := near_add (exponent_near A e he he1 hu 2 (by decide +kernel)) (near_rational 1)
  rw [cast_two,show (2:Rat)+1=3 by decide +kernel,Rat.add_zero] at hs
  have hh := near_mul_errors he (Rat.mul_pos (show (0:Rat)<4/27 by decide +kernel) he) hs (denominator_inverse_near A e he he1 hu)
  have hsq := Rat.mul_le_mul_of_nonneg_left (show e≤(1:Rat) by grind only) (Rat.le_of_lt he)
  rw [Rat.mul_one] at hsq
  rw [qabs_eq_self_of_nonneg (show (0:Rat)≤3 by decide +kernel),
    qabs_eq_self_of_nonneg (show (0:Rat)≤1/3 by decide +kernel),
    show (3:Rat)*(1/3)=1 by decide +kernel] at hh
  change Near (lowerEnergy 2 (by decide +kernel) A) 1 (3*((4/27)*e)+(1/3)*e+e*((4/27)*e)) at hh
  exact near_mono hh (by grind only)

include he he1 hu in
theorem upper_energy_near : Near (upperEnergy 2 A) 1 e := by
  have hh := near_scale (1/3) (by decide +kernel) (exponent_near A e he he1 hu 3 (by decide +kernel))
  have heq : (Value.mul (Value.rational (1/3)) (HydrogenCircularComputations.exponent 3 (by decide +kernel) A)).real.preferred.Equiv (upperEnergy 2 A).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro m hm s hs
    change (1/3:Rat)*s (HydrogenCircularComputations.exponent 3 (by decide +kernel) A).real=
      s (HydrogenCircularComputations.exponent 3 (by decide +kernel) A).real*(1/3)
    grind only
  rw [cast_three,show (1/3:Rat)*3=1 by decide +kernel] at hh
  exact near_mono (near_congr hh heq) (by grind only)

include he he1 hu in
theorem splitting_denominator_near : Near (HydrogenCircularSplitting.denominator 2 (by decide +kernel) A) 648 (1332*e) := by
  have hs := near_add (exponent_near A e he he1 hu 2 (by decide +kernel)) (near_rational 2)
  rw [cast_two,show (2:Rat)+2=4 by decide +kernel,Rat.add_zero] at hs
  have hn := near_scale 9 (by decide +kernel) hs
  have hEq : (Value.mul (Value.rational 9) (HydrogenCircularSplitting.angularSum 2 (by decide +kernel) A)).real.preferred.Equiv
      (Value.mul (HydrogenCircularSplitting.angularSum 2 (by decide +kernel) A) (HydrogenCircularSplitting.principalSquare 2)).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro m hm s hs
    change (9:Rat)*(s (HydrogenCircularComputations.exponent 2 (by decide +kernel) A).real+2)=
      (s (HydrogenCircularComputations.exponent 2 (by decide +kernel) A).real+2)*(3*3)
    grind only
  rw [show (9:Rat)*4=36 by decide +kernel] at hn
  have hp := near_mul_errors (Rat.mul_pos (show (0:Rat)<9 by decide +kernel) he)
    (Rat.mul_pos (show (0:Rat)<2 by decide +kernel) he) (near_congr hn hEq) (denominator_squared_near A e he he1 hu)
  have hsq := Rat.mul_le_mul_of_nonneg_left (show e≤(1:Rat) by grind only) (Rat.le_of_lt he)
  rw [Rat.mul_one] at hsq
  have hp' : Near (Value.mul (Value.mul (HydrogenCircularSplitting.angularSum 2 (by decide +kernel) A)
      (HydrogenCircularSplitting.principalSquare 2)) (denominatorSquared 2 (by decide +kernel) A)) 324 (171*e) := by
    rw [qabs_eq_self_of_nonneg (show (0:Rat)≤36 by decide +kernel),
      qabs_eq_self_of_nonneg (show (0:Rat)≤9 by decide +kernel),
      show (36:Rat)*9=324 by decide +kernel] at hp
    change Near _ 324 (36*(2*e)+9*(9*e)+(9*e)*(2*e)) at hp
    exact near_mono hp (by grind only)
  have hSum := near_add (upper_energy_near A e he he1 hu) (lower_energy_near A e he he1 hu)
  rw [show (1:Rat)+1=2 by decide +kernel] at hSum
  have hh := near_mul_errors (Rat.mul_pos (show (0:Rat)<171 by decide +kernel) he)
    (show (0:Rat)<e+e by grind only) hp' hSum
  rw [qabs_eq_self_of_nonneg (show (0:Rat)≤324 by decide +kernel),
    qabs_eq_self_of_nonneg (show (0:Rat)≤2 by decide +kernel),
    show (324:Rat)*2=648 by decide +kernel] at hh
  change Near _ 648 (324*(e+e)+2*(171*e)+(171*e)*(e+e)) at hh
  exact near_mono hh (by grind only)

include he he1 hu in
/-- Explicit uniform coefficient error for the constructed principal-three pair. -/
theorem coefficient_two_near : Near (HydrogenCircularSplitting.coefficient 2 (by decide +kernel) A) (1/324) (e/64) := by
  have hh := near_positiveInv (show (0:Rat)<648 by decide +kernel)
    ⟨1332*e,Rat.mul_pos (by decide +kernel) he⟩ (by change (1332:Rat)*e≤648/2;grind only)
    (splitting_denominator_near A e he he1 hu) 0 (HydrogenCircularSplitting.denominator_positive 2 (by decide +kernel) A 0)
  have hc := near_scale 2 (by decide +kernel) hh
  change Near (HydrogenCircularSplitting.coefficient 2 (by decide +kernel) A) (2*(648:Rat)⁻¹)
    (2*((inverseBudget 648 (by decide +kernel)).val*(1332*e))) at hc
  rw [show (2:Rat)*648⁻¹=1/324 by decide +kernel,
    show (inverseBudget 648 (by decide +kernel)).val=1/209952 by decide +kernel] at hc
  exact near_mono hc (by grind only [Rat.div_def])

/-- The cancellation-free first coefficient agrees with the independent two-P
computation, including zero coupling where splitting cancellation is unavailable. -/
theorem coefficient_one_agreement : (HydrogenCircularSplitting.coefficient 1 (by decide +kernel) A).real.preferred.Equiv
    (HydrogenTwoPComputations.scaledSplitting A).real.preferred := by
  by_cases h0 : A.squared.preferred.Equiv RealRaw.zero
  · have hNew := HydrogenCircularZero.coefficient_zero 1 (by decide +kernel) A h0
    rw [show (2:Rat)/HydrogenCircularZero.zeroDenominator 1=1/32 by decide +kernel] at hNew
    exact RealRaw.equiv_trans (y := RealRaw.ofRat (1/32)) (HydrogenCircularSplitting.coefficient 1 (by decide +kernel) A).real.valid
      (RealRaw.ofRat_valid (1/32)) (HydrogenTwoPComputations.scaledSplitting A).real.valid
      hNew (RealRaw.equiv_symm (HydrogenTwoPComputations.scaledSplitting_zero A h0))
  · have hn : ¬A.value.real.preferred.Equiv RealRaw.zero := by
      intro h
      exact h0 (RealRaw.equiv_trans A.squared.valid A.bounded.valid (RealRaw.ofRat_valid 0)
        (RealRaw.equiv_symm A.bounded_equiv) h)
    have hC := quotient_eq (HydrogenCircularSplitting.splitting_identity 1 (by decide +kernel) A)
    have hO := quotient_eq (HydrogenTwoPComputations.splitting_identity A)
    have hA := quotient_eq (HydrogenCircularTwoPAgreement.splitting_agreement A)
    have hi := quotient_eq (y := Value.rational 1) (Value.mul_inverse A.value hn)
    simp only [quotient_mul,quotient_one] at hC hO hi
    have hEq : (quotient A.value*quotient A.value)*quotient (HydrogenCircularSplitting.coefficient 1 (by decide +kernel) A)=
        (quotient A.value*quotient A.value)*quotient (HydrogenTwoPComputations.scaledSplitting A) := by
      rw [←hC,hA,hO]
    have hm := congrArg (fun z : ComplexRawQuotient.Value => z*(quotient (Value.inverse A.value hn)*quotient (Value.inverse A.value hn))) hEq
    apply raw_equiv_of_quotient_eq
    grind only

/-- Uniform first coefficient error; no limiting interpretation is needed. -/
theorem coefficient_one_near (he : 0<e) (he1 : e≤1/2)
    (hu : A.squared.preferred.Le (RealRaw.ofRat e)) :
    Near (HydrogenCircularSplitting.coefficient 1 (by decide +kernel) A) (1/32) e := by
  have hh := HydrogenTwoPComputations.scaledSplitting_small_bound A e he he1 hu
  have hn : Near (HydrogenTwoPComputations.scaledSplitting A) (1/32) e := by
    constructor
    · intro i j
      have h := hh.1 0 j
      change (1/32:Rat)≤((HydrogenTwoPComputations.scaledSplitting A).real.compute j).hi at h
      change 1/32-e≤((HydrogenTwoPComputations.scaledSplitting A).real.compute j).hi
      grind only
    · exact hh.2
  exact near_congr hn (RealRaw.equiv_symm (coefficient_one_agreement A))

/-- Explicit error of the exact regularized ratio at any coupling bounded by e. -/
theorem ratio_near (he : 0<e) (he1 : e≤1/64)
    (hu : A.squared.preferred.Le (RealRaw.ofRat e)) :
    Near (HydrogenCircularRatio.ratio A) (8/81) (8*e) := by
  have hC := coefficient_one_near A e he (by grind only) hu
  have hi := near_positiveInv (show (0:Rat)<1/32 by decide +kernel) ⟨e,he⟩ (by change e≤(1/32:Rat)/2;grind only)
    hC 0 (HydrogenCircularSplitting.coefficient_positive 1 (by decide +kernel) A 0)
  rw [show (1/32:Rat)⁻¹=32 by decide +kernel,
    show (inverseBudget (1/32) (by decide +kernel)).val=2048 by decide +kernel] at hi
  have hh := near_mul_errors (Rat.mul_pos he (show (0:Rat)<(64:Rat)⁻¹ by decide +kernel))
    (Rat.mul_pos (show (0:Rat)<2048 by decide +kernel) he)
    (coefficient_two_near A e he (by grind only) hu) hi
  rw [qabs_eq_self_of_nonneg (show (0:Rat)≤1/324 by decide +kernel),
    qabs_eq_self_of_nonneg (show (0:Rat)≤32 by decide +kernel)] at hh
  change Near (HydrogenCircularRatio.ratio A) ((1/324:Rat)*32)
    ((1/324)*(2048*e)+32*(e*(64:Rat)⁻¹)+(e*(64:Rat)⁻¹)*(2048*e)) at hh
  rw [show (1/324:Rat)*32=8/81 by decide +kernel] at hh
  have hsq := Rat.mul_le_mul_of_nonneg_left he1 (Rat.le_of_lt he)
  exact near_mono hh (by grind only [Rat.div_def])

def coefficientError (k : Nat) (hk : 0<k) (c : Rat) : Value :=
  Value.sub (HydrogenCircularSplitting.coefficient k hk A) (Value.rational c)
def remainder (k : Nat) (hk : 0<k) (c : Rat) : Value :=
  Value.sub (HydrogenCircularSplitting.splitting k hk A)
    (Value.mul (Value.mul A.value A.value) (Value.rational c))
def cubic : Value := Value.mul (Value.mul A.value A.value) A.value

private theorem value_nonnegative : (RealRaw.ofRat 0).Le A.value.real.preferred :=
  Order.nonnegative_of_literal A.value (fun n => (A.bounded_interval n).1)

/-- Exact coefficient remainder, in the actual represented squared coupling. -/
theorem coefficient_one_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    (Value.neg A.value).real.preferred.Le (coefficientError A 1 (by decide +kernel) (1/32)).real.preferred ∧
      (coefficientError A 1 (by decide +kernel) (1/32)).real.preferred.Le A.value.real.preferred := by
  have hh := bounds_of_upper_estimates (coefficientError A 1 (by decide +kernel) (1/32)) A.value 1 (1/2)
    (by decide +kernel) (by decide +kernel) (value_nonnegative A)
    (by simpa only [show (1/2:Rat)/2=1/4 by decide +kernel] using HydrogenTwoPComputations.value_le A (1/4) hu)
    (by
      intro e he heb hue
      have hRaw : A.squared.preferred.Le (RealRaw.ofRat e) := RealRaw.le_trans A.bounded.valid
        (RealRaw.le_of_equiv A.squared.valid A.bounded.valid (RealRaw.equiv_symm A.bounded_equiv)) hue
      simpa only [coefficientError,Rat.one_mul] using near_center (coefficient_one_near A e he heb hRaw))
  exact ⟨le_congr (neg_equiv (Value.one_mul A.value)) (Value.equiv_refl _) hh.1,
    le_congr (Value.equiv_refl _) (Value.one_mul A.value) hh.2⟩

theorem coefficient_two_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/16))) :
    (Value.neg (Value.mul (Value.rational (1/64)) A.value)).real.preferred.Le (coefficientError A 2 (by decide +kernel) (1/324)).real.preferred ∧
      (coefficientError A 2 (by decide +kernel) (1/324)).real.preferred.Le (Value.mul (Value.rational (1/64)) A.value).real.preferred := by
  apply bounds_of_upper_estimates _ A.value (1/64) (1/8) (by decide +kernel) (by decide +kernel) (value_nonnegative A)
    (by simpa only [show (1/8:Rat)/2=1/16 by decide +kernel] using HydrogenTwoPComputations.value_le A (1/16) hu)
  intro e he heb hue
  have hRaw : A.squared.preferred.Le (RealRaw.ofRat e) := RealRaw.le_trans A.bounded.valid
    (RealRaw.le_of_equiv A.squared.valid A.bounded.valid (RealRaw.equiv_symm A.bounded_equiv)) hue
  have hh := near_center (coefficient_two_near A e he heb hRaw)
  exact near_mono hh (by grind only [Rat.div_def])

def ratioError : Value := Value.sub (HydrogenCircularRatio.ratio A) (Value.rational (8/81))

/-- A uniform exact ratio error, including zero, under a stated coupling range. -/
theorem ratio_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/128))) :
    (Value.neg (Value.mul (Value.rational 8) A.value)).real.preferred.Le (ratioError A).real.preferred ∧
      (ratioError A).real.preferred.Le (Value.mul (Value.rational 8) A.value).real.preferred := by
  apply bounds_of_upper_estimates _ A.value 8 (1/64) (by decide +kernel) (by decide +kernel) (value_nonnegative A)
    (by simpa only [show (1/64:Rat)/2=1/128 by decide +kernel] using HydrogenTwoPComputations.value_le A (1/128) hu)
  intro e he heb hue
  have hRaw : A.squared.preferred.Le (RealRaw.ofRat e) := RealRaw.le_trans A.bounded.valid
    (RealRaw.le_of_equiv A.squared.valid A.bounded.valid (RealRaw.equiv_symm A.bounded_equiv)) hue
  exact near_center (ratio_near A e he heb hRaw)

/-- The energy error is the exact squared-coupling factor times its
coefficient error; no untracked asymptotic equality is used. -/
theorem remainder_factor (k : Nat) (hk : 0<k) (c : Rat) :
    (remainder A k hk c).real.preferred.Equiv
      (Value.mul (Value.mul A.value A.value) (coefficientError A k hk c)).real.preferred := by
  have hh := quotient_eq (HydrogenCircularSplitting.splitting_identity k hk A)
  simp only [quotient_mul] at hh
  apply raw_equiv_of_quotient_eq
  simp only [remainder,coefficientError,quotient_sub,quotient_mul,hh]
  grind only

private theorem remainder_bound_of_coefficient (k : Nat) (hk : 0<k) (c C : Rat)
    (h : (Value.neg (Value.mul (Value.rational C) A.value)).real.preferred.Le (coefficientError A k hk c).real.preferred ∧
      (coefficientError A k hk c).real.preferred.Le (Value.mul (Value.rational C) A.value).real.preferred) :
    (Value.neg (Value.mul (Value.rational C) (cubic A))).real.preferred.Le (remainder A k hk c).real.preferred ∧
      (remainder A k hk c).real.preferred.Le (Value.mul (Value.rational C) (cubic A)).real.preferred := by
  have hU := Order.mul_nonnegative A.value A.value (value_nonnegative A) (value_nonnegative A)
  have hL := Order.mul_mono_left (Value.mul A.value A.value) _ _ hU h.1
  have hR := Order.mul_mono_left (Value.mul A.value A.value) _ _ hU h.2
  have hEqL : (Value.mul (Value.mul A.value A.value) (Value.neg (Value.mul (Value.rational C) A.value))).real.preferred.Equiv
      (Value.neg (Value.mul (Value.rational C) (cubic A))).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [cubic,quotient_mul,quotient_neg]
    grind only
  have hEqR : (Value.mul (Value.mul A.value A.value) (Value.mul (Value.rational C) A.value)).real.preferred.Equiv
      (Value.mul (Value.rational C) (cubic A)).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [cubic,quotient_mul]
    grind only
  exact ⟨le_congr hEqL (RealRaw.equiv_symm (remainder_factor A k hk c)) hL,
    le_congr (RealRaw.equiv_symm (remainder_factor A k hk c)) hEqR hR⟩

/-- Absolute first-doublet energy remainder at most the sixth power of alpha. -/
theorem two_p_remainder_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    (Value.neg (cubic A)).real.preferred.Le (remainder A 1 (by decide +kernel) (1/32)).real.preferred ∧
      (remainder A 1 (by decide +kernel) (1/32)).real.preferred.Le (cubic A).real.preferred := by
  have hh := remainder_bound_of_coefficient A 1 (by decide +kernel) (1/32) 1 (by
    exact ⟨le_congr (RealRaw.equiv_symm (neg_equiv (Value.one_mul A.value))) (Value.equiv_refl _) (coefficient_one_bound A hu).1,
      le_congr (Value.equiv_refl _) (RealRaw.equiv_symm (Value.one_mul A.value)) (coefficient_one_bound A hu).2⟩)
  exact ⟨le_congr (neg_equiv (Value.one_mul (cubic A))) (Value.equiv_refl _) hh.1,
    le_congr (Value.equiv_refl _) (Value.one_mul (cubic A)) hh.2⟩

/-- Absolute principal-three circular energy remainder at most alpha^6/64. -/
theorem circular_three_remainder_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/16))) :
    (Value.neg (Value.mul (Value.rational (1/64)) (cubic A))).real.preferred.Le (remainder A 2 (by decide +kernel) (1/324)).real.preferred ∧
      (remainder A 2 (by decide +kernel) (1/324)).real.preferred.Le (Value.mul (Value.rational (1/64)) (cubic A)).real.preferred :=
  remainder_bound_of_coefficient A 2 (by decide +kernel) (1/324) (1/64) (coefficient_two_bound A hu)

end ComputableAnalysis.HydrogenCircularRemainder
