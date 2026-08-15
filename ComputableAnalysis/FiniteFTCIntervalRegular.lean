import ComputableAnalysis.Calculus
import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.Series

/-!
# Interval-regular integral certificates

This module names the current boundary between interval regularity and
integrability.  `IntervalRegularOn` supplies the pointwise interval modulus;
the integral construction is still explicit certificate data.  The general
construction theorem is therefore not asserted, while exact constants give a
fully checked first instance.
-/

namespace ComputableAnalysis

namespace Integral

structure IntervalRegularIntegralCertificate (F : FunctionOnInterval) where
  regular : IntervalRegularOn F
  construction : ConstructionFor F

def raw (F : FunctionOnInterval)
    (certificate : IntervalRegularIntegralCertificate F) : RealRaw :=
  integralFor F certificate.construction

theorem raw_valid (F : FunctionOnInterval)
    (certificate : IntervalRegularIntegralCertificate F) :
    (raw F certificate).Valid := by
  exact integralFor_valid F certificate.construction

def exactRat_constant (c a b : Rat) :
    IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun _ => c) a b) where
  regular := exactRat_constant_intervalRegularOn c a b
  construction := (constantMonotoneConstructionFor c a b).construction

theorem exactRat_constant_raw_eq_ofRat (c a b : Rat) :
    raw (FunctionOnInterval.exactRat (fun _ => c) a b)
      (exactRat_constant c a b) =
      RealRaw.ofRat ((b - a) * c) := by
  rfl

theorem exactRat_constant_raw_valid (c a b : Rat) :
    (raw (FunctionOnInterval.exactRat (fun _ => c) a b)
      (exactRat_constant c a b)).Valid := by
  exact raw_valid _ (exactRat_constant c a b)

/-- The interval image of a rational affine map with nonnegative slope. -/
def affineInterval (r c : Rat) (I : QInterval) : QInterval :=
  { lo := r * I.lo + c, hi := r * I.hi + c }

/-- A rational affine map with slope in `[0,1]` has a computable interval
modulus, witnessed by the finite schedule `n+1`. -/
def exactRat_affine_intervalRegularOn_of_unit_slope
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  evalInterval := fun I _hI _n => affineInterval r c I
  inputPrecision := fun n => n + 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hscaled_nonneg : 0 <= r * I.width :=
      Rat.mul_nonneg hr0 hwidth_nonneg
    have hscaled_le : r * I.width <= I.width := by
      have hmul := Rat.mul_le_mul_of_nonneg_right hr1 hwidth_nonneg
      simpa using hmul
    have hwidth : (affineInterval r c I).width = r * I.width := by
      unfold affineInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
    rw [hwidth]
    constructor
    · exact hscaled_nonneg
    · have hbound : r * I.width <= 1 / ((n + 1 : Nat) : Rat) :=
        Rat.le_trans hscaled_le hsmall
      simpa [Rat.sub_eq_add_neg, Rat.mul_add] using hbound
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold affineInterval QInterval.ContainsInterval
    change r * I.lo + c <= r * x + c ∧
      r * x + c <= r * I.hi + c
    constructor
    · grind [Rat.mul_le_mul_of_nonneg_left hIlo hr0]
    · grind [Rat.mul_le_mul_of_nonneg_left hIhi hr0]

def exactRat_affine_unitSlope (r c a b : Rat)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  regular := exactRat_affine_intervalRegularOn_of_unit_slope r c a b hr0 hr1
  construction := (affineMonotoneConstructionFor hr0).construction

theorem exactRat_affine_unitSlope_raw_eq_ofRat
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_unitSlope r c a b hr0 hr1) =
      RealRaw.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  rfl

theorem exactRat_affine_unitSlope_raw_valid
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    (raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_unitSlope r c a b hr0 hr1)).Valid := by
  exact raw_valid _ (exactRat_affine_unitSlope r c a b hr0 hr1)

/-- The interval image of an affine map, with endpoint order selected by the
sign of its slope. -/
def signedAffineInterval (r c : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    affineInterval r c I
  else
    { lo := r * I.hi + c, hi := r * I.lo + c }

/-- Exact rational affine functions with slope in `[-1,1]` satisfy the same
computable interval-regularity contract in both monotonicity directions. -/
def exactRat_affine_intervalRegularOn_of_signed_unit_slope
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  evalInterval := fun I _hI _n => signedAffineInterval r c I
  inputPrecision := fun n => n + 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    by_cases hr : 0 <= r
    · simp only [signedAffineInterval, if_pos hr]
      have hscaled_nonneg : 0 <= r * I.width :=
        Rat.mul_nonneg hr hwidth_nonneg
      have hscaled_le : r * I.width <= I.width := by
        have hmul := Rat.mul_le_mul_of_nonneg_right hrpos hwidth_nonneg
        simpa using hmul
      have hwidth : (affineInterval r c I).width = r * I.width := by
        unfold affineInterval QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      rw [hwidth]
      constructor
      · exact hscaled_nonneg
      · exact Rat.le_trans hscaled_le hsmall
    · simp only [signedAffineInterval, if_neg hr]
      have hminus_nonneg : 0 <= -r := by grind
      have hminus_le : -r <= 1 := by grind
      have hscaled_nonneg : 0 <= (-r) * I.width :=
        Rat.mul_nonneg hminus_nonneg hwidth_nonneg
      have hscaled_le : (-r) * I.width <= I.width := by
        have hmul := Rat.mul_le_mul_of_nonneg_right hminus_le hwidth_nonneg
        simpa using hmul
      have hwidth :
          (QInterval.mk (r * I.hi + c) (r * I.lo + c)).width =
            (-r) * I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      rw [hwidth]
      constructor
      · exact hscaled_nonneg
      · exact Rat.le_trans hscaled_le hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold signedAffineInterval
    by_cases hr : 0 <= r
    · simp only [if_pos hr]
      unfold affineInterval QInterval.ContainsInterval
      change r * I.lo + c <= r * x + c ∧
        r * x + c <= r * I.hi + c
      constructor <;> grind [Rat.mul_le_mul_of_nonneg_left hIlo hr,
        Rat.mul_le_mul_of_nonneg_left hIhi hr]
    · simp only [if_neg hr]
      unfold QInterval.ContainsInterval
      change r * I.hi + c <= r * x + c ∧
        r * x + c <= r * I.lo + c
      have hminus : 0 <= -r := by grind
      have hhi' := Rat.mul_le_mul_of_nonneg_left hIhi hminus
      have hlo' := Rat.mul_le_mul_of_nonneg_left hIlo hminus
      constructor <;> grind

def exactRat_affine_signed_unitSlope (r c a b : Rat)
    (hrneg : -1 <= r) (hrpos : r <= 1) :
    IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  regular := exactRat_affine_intervalRegularOn_of_signed_unit_slope
    r c a b hrneg hrpos
  construction := by
    by_cases hr : 0 <= r
    · exact (affineMonotoneConstructionFor hr).construction
    · have hrle : r <= 0 := by grind
      exact (affineMonotoneConstructionFor_of_nonpos hrle).construction

theorem exactRat_affine_signed_unitSlope_raw_eq_ofRat
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_signed_unitSlope r c a b hrneg hrpos) =
      RealRaw.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  by_cases hr : 0 <= r
  · unfold raw exactRat_affine_signed_unitSlope
    simp only [dif_pos hr]
    rfl
  · have hrle : r <= 0 := by grind
    unfold raw exactRat_affine_signed_unitSlope
    simp only [dif_neg hr]
    rfl

theorem exactRat_affine_signed_unitSlope_raw_valid
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    (raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_signed_unitSlope r c a b hrneg hrpos)).Valid := by
  exact raw_valid _ (exactRat_affine_signed_unitSlope r c a b hrneg hrpos)

def exactSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

private theorem two_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((2 * (n + 1) : Nat) : Rat)) :
    2 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    2 * w <= 2 * (1 / ((2 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hn : (n + 1 : Nat) ≠ 0 := by omega
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      have htwo : (2 : Rat) ≠ 0 := by native_decide
      rw [show ((2 * (n + 1) : Nat) : Rat) =
        (2 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 2 * (n + 1) = 2 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The exact rational square function on `[0,1]` has a finite interval
modulus.  This is the non-affine polynomial base case for the interval-regular
FTC bridge; its schedule is `2*(n+1)` because the square width is bounded by
`2*width(I)` on the unit interval. -/
def exactRat_square_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => x * x) 0 1) where
  evalInterval := fun I _hI _n => exactSquareInterval I
  inputPrecision := fun n => 2 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hsum_nonneg : 0 <= I.hi + I.lo := by
      have hlo_nonneg : 0 <= I.lo := by
        have h := hI.1
        change (0 : Rat) <= I.lo at h
        exact h
      have hhi_nonneg : 0 <= I.hi := by grind
      exact Rat.add_nonneg hhi_nonneg hlo_nonneg
    have hsum_le_two : I.hi + I.lo <= 2 := by
      have hlo_nonneg : 0 <= I.lo := by
        have h := hI.1
        change (0 : Rat) <= I.lo at h
        exact h
      have hhi_le_one : I.hi <= 1 := by
        have h := hI.2.2
        change I.hi <= (1 : Rat) at h
        exact h
      grind
    have hwidth : (exactSquareInterval I).width =
        I.width * (I.hi + I.lo) := by
      unfold exactSquareInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · have hprod : I.width * (I.hi + I.lo) <= I.width * 2 :=
        Rat.mul_le_mul_of_nonneg_left hsum_le_two hwidth_nonneg
      have htwo : 2 * I.width <= 1 / ((n + 1 : Nat) : Rat) :=
        two_width_le_one_div_succ_of_width_le n hsmall
      calc
        I.width * (I.hi + I.lo) <= I.width * 2 := hprod
        _ = 2 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) := htwo
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactSquareInterval QInterval.ContainsInterval
    change I.lo * I.lo <= x * x ∧ x * x <= I.hi * I.hi
    have hlo_nonneg : 0 <= I.lo := by
      simpa [FunctionOnInterval.exactRat] using hI.1
    have hhi_nonneg : 0 <= I.hi := by
      have : 0 <= I.lo := hlo_nonneg
      grind
    have hxl_nonneg : 0 <= x + I.lo := by grind
    have hxh_nonneg : 0 <= x + I.hi := by grind
    constructor
    · have hmul := Rat.mul_le_mul_of_nonneg_right hIlo hxl_nonneg
      grind [Rat.mul_add, Rat.add_mul]
    · have hmul := Rat.mul_le_mul_of_nonneg_right hIhi hxh_nonneg
      grind [Rat.mul_add, Rat.add_mul]

def exactSquare_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x * x) 2 := by
  constructor
  · native_decide
  · intro s t hs hs1 ht ht1
    have hsum_nonneg : 0 <= s + t := Rat.add_nonneg hs ht
    have hsum_le_two : s + t <= 2 := by grind
    have hfactor : s * s - t * t = (s - t) * (s + t) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    rw [hfactor, qabs_mul, qabs_eq_self_of_nonneg hsum_nonneg]
    have hst : qabs (s - t) = qabs (t - s) := by
      rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]
    rw [hst]
    have hbound := Rat.mul_le_mul_of_nonneg_left hsum_le_two
      (qabs_nonneg (t - s))
    simpa [Rat.mul_comm] using hbound

def exactRat_square_integral_certificate :
    Integral.IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1) where
  regular := exactRat_square_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x * x) 2
      exactSquare_lipschitz_on_unit

theorem exactRat_square_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_square_integral_certificate

theorem exactSquare_uniformLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x * x) n =
      Series.squareSum n / (n : Rat) ^ 3 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j : Rat) / (n : Rat)) * ((j : Rat) / (n : Rat)))) 0 =
        Series.squareSum k / (n : Rat) ^ 3 := by
    intro k
    induction k with
    | zero =>
        simp [Series.squareSum, Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.squareSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactSquare_uniformRightSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x * x) n =
      Series.squareSum (n + 1) / (n : Rat) ^ 3 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hfrac (a b : Rat) :
      a / (n : Rat) ^ 3 + b / (n : Rat) ^ 3 =
        (a + b) / (n : Rat) ^ 3 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
      Rat.pow_succ, Rat.mul_inv_cancel]
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j + 1 : Nat) : Rat) / (n : Rat) *
                (((j + 1 : Nat) : Rat) / (n : Rat)))) 0 =
        Series.squareSum (k + 1) / (n : Rat) ^ 3 := by
    intro k
    induction k with
    | zero =>
        simp [Series.squareSum, Rat.div_def]
        grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm :
            (1 / (n : Rat)) *
                (((k : Rat) + 1) / (n : Rat) *
                  (((k : Rat) + 1) / (n : Rat))) =
              ((k : Rat) + 1) ^ 2 / (n : Rat) ^ 3 := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ,
            Rat.mul_inv_cancel]
        rw [hterm]
        have hs : Series.squareSum (k + 1 + 1) =
            Series.squareSum (k + 1) + ((k + 1 : Nat) : Rat) ^ 2 := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Series.squareSum_succ]
        rw [hs]
        simpa [Rat.natCast_add] using hfrac _ _
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactSquare_uniformLeftSum_le_one_third
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x * x) n <= 1 / 3 := by
  rw [exactSquare_uniformLeftSum_eq hn, Series.squareSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 3 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 3)
  · rw [Rat.div_def, Rat.div_def]
    have hpoly : (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1)
        <= 2 * (n : Rat) ^ 3 := by
      have hn1 : 1 <= (n : Rat) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
      have hnonneg : 0 <= (n : Rat) * (3 * (n : Rat) - 1) := by
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) (by grind)
      have hid : 2 * (n : Rat) ^ 3 -
          (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) =
          (n : Rat) * (3 * (n : Rat) - 1) := by
            grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.add_mul, Rat.sub_eq_add_neg]
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 6)))
    have hcancel : ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
          6⁻¹ * ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 =
          (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) * 6⁻¹ := by
            calc
              _ = ((n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) * 6⁻¹) *
                  (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
      _ <= 2 * (n : Rat) ^ 3 * 6⁻¹ := hscaled
      _ = 1 / 3 * (n : Rat) ^ 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact hden

theorem exactSquare_uniformRightSum_ge_one_third
    {n : Nat} (hn : 0 < n) :
    1 / 3 <=
      IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x * x) n := by
  rw [exactSquare_uniformRightSum_eq hn, Series.squareSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 3 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 3)
  · rw [Rat.div_def, Rat.div_def]
    have hnp1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hnp1]
    have hminus : (n : Rat) + 1 - 1 = (n : Rat) := by grind
    rw [hminus]
    have htwo : 2 * ((n : Rat) + 1) - 1 = 2 * (n : Rat) + 1 := by grind
    rw [htwo]
    rw [Rat.div_def]
    have hpoly : 2 * (n : Rat) ^ 3
        <= (n : Rat) * ((n : Rat) + 1) * (2 * (n : Rat) + 1) := by
      have hnonneg : 0 <= (n : Rat) * (3 * (n : Rat) + 1) := by
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) (by grind)
      have hid : (n : Rat) * ((n : Rat) + 1) * (2 * (n : Rat) + 1) -
          2 * (n : Rat) ^ 3 = (n : Rat) * (3 * (n : Rat) + 1) := by
            grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.add_mul]
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 6)))
    have hscaled' : 2 * (n : Rat) ^ 3 * 6⁻¹ <=
        ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹ := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    have hcancel : ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      1 / 3 * (n : Rat) ^ 3 = 2 * (n : Rat) ^ 3 * 6⁻¹ := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹ := hscaled'
      _ = ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) *
          6⁻¹ * ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 := by
        calc
          _ = (((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹) *
              (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ = _ := by
            symm
            calc
              _ = (((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹) *
                  (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
  · exact hden

theorem exactSquare_compute_contains_one_third (stage : Nat) :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x * x) 2 stage).ContainsInterval
      { lo := 1 / 3, hi := 1 / 3 } := by
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactSquare_lipschitz_on_unit stage
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactSquare_lipschitz_on_unit stage
  have hleft := exactSquare_uniformLeftSum_le_one_third hn
  have hright := exactSquare_uniformRightSum_ge_one_third hn
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 hleft
  · exact Rat.le_trans hright hr.2

theorem exactRat_square_integral_raw_equiv_one_third :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 3)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x * x) 2 n)
    { lo := 1 / 3, hi := 1 / 3 }
  unfold QInterval.Overlaps
  exact exactSquare_compute_contains_one_third n

def exactCubeInterval (I : QInterval) : QInterval :=
  { lo := I.lo ^ 3, hi := I.hi ^ 3 }

private theorem three_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((3 * (n + 1) : Nat) : Rat)) :
    3 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    3 * w <= 3 * (1 / ((3 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      rw [show ((3 * (n + 1) : Nat) : Rat) =
        (3 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 3 * (n + 1) = 3 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def exactRat_cube_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) where
  evalInterval := fun I _hI _n => exactCubeInterval I
  inputPrecision := fun n => 3 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_le_one : I.hi <= 1 := by
      have h := hI.2.2
      change I.hi <= (1 : Rat) at h
      exact h
    have hwidth : (exactCubeInterval I).width =
        I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) := by
      unfold exactCubeInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · have hsum_nonneg : 0 <= I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2 := by
        exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
          (Rat.mul_nonneg (by grind) hlo_nonneg)) (Rat.pow_nonneg hlo_nonneg)
      exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · have hhi_nonneg : 0 <= I.hi := by grind
      have hterm1 : I.hi ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hhi_le_one (by grind : 0 <= I.hi)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hhi_le_one
      have hterm2 : I.hi * I.lo <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hhi_le_one hlo_nonneg)
          (by grind)
      have hterm3 : I.lo ^ 2 <= 1 := by
        have hlo_le_one : I.lo <= 1 := by grind
        have h := Rat.mul_le_mul_of_nonneg_left hlo_le_one hlo_nonneg
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hlo_le_one
      have hsum_le_three : I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2 <= 3 := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hsum_le_three hwidth_nonneg
      calc
        I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) <= I.width * 3 := hprod
        _ = 3 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) :=
          three_width_le_one_div_succ_of_width_le n hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactCubeInterval QInterval.ContainsInterval
    change I.lo ^ 3 <= x ^ 3 ∧ x ^ 3 <= I.hi ^ 3
    have hx' : 0 <= x ∧ x <= 1 := by
      simpa [FunctionOnInterval.exactRat, inDomainInterval] using hx
    have hx_nonneg : 0 <= x := hx'.1
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_nonneg : 0 <= I.hi := by grind
    have hsum_lo : 0 <= x ^ 2 + x * I.lo + I.lo ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hx_nonneg)
        (Rat.mul_nonneg hx_nonneg hlo_nonneg)) (Rat.pow_nonneg hlo_nonneg)
    have hsum_hi : 0 <= I.hi ^ 2 + I.hi * x + x ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hhi_nonneg)
        (Rat.mul_nonneg hhi_nonneg hx_nonneg)) (Rat.pow_nonneg hx_nonneg)
    have hlow : 0 <= (x - I.lo) *
        (x ^ 2 + x * I.lo + I.lo ^ 2) := by
      exact Rat.mul_nonneg (by grind) hsum_lo
    have hhigh : 0 <= (I.hi - x) *
        (I.hi ^ 2 + I.hi * x + x ^ 2) := by
      exact Rat.mul_nonneg (by grind) hsum_hi
    constructor <;> grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]

def exactCube_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x ^ 3) 3 := by
  constructor
  · native_decide
  · intro s t hs hs1 ht ht1
    have hsum_nonneg : 0 <= s ^ 2 + s * t + t ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
        (Rat.mul_nonneg (by grind) (by grind))) (Rat.pow_nonneg (by grind))
    have hsum_le_three : s ^ 2 + s * t + t ^ 2 <= 3 := by
      have hs0 : 0 <= s := by grind
      have ht0 : 0 <= t := by grind
      have hs2 : s ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hs1 (by grind : 0 <= s)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hs1
      have ht2 : t ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left ht1 (by grind : 0 <= t)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) ht1
      have hst : s * t <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hs1 ht0) (by grind)
      grind
    have hfactor : s ^ 3 - t ^ 3 = (s - t) * (s ^ 2 + s * t + t ^ 2) := by
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hfactor, qabs_mul]
    have hbound := Rat.mul_le_mul_of_nonneg_left hsum_le_three
      (qabs_nonneg (s - t))
    calc
      qabs (s - t) * qabs (s ^ 2 + s * t + t ^ 2) <=
          qabs (s - t) * 3 :=
        Rat.mul_le_mul_of_nonneg_left
          (by simpa [qabs_eq_self_of_nonneg hsum_nonneg] using hsum_le_three)
          (qabs_nonneg _)
      _ = 3 * qabs (t - s) := by
        rw [show qabs (s - t) = qabs (t - s) by
          rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
        grind [Rat.mul_comm]

def exactRat_cube_integral_certificate :
    Integral.IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) where
  regular := exactRat_cube_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x ^ 3) 3
      exactCube_lipschitz_on_unit

theorem exactRat_cube_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_cube_integral_certificate

theorem exactCube_uniformLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 3) n =
      Series.cubeSum n / (n : Rat) ^ 4 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j : Rat) / (n : Rat)) ^ 3)) 0 =
        Series.cubeSum k / (n : Rat) ^ 4 := by
    intro k
    induction k with
    | zero =>
        simp [Series.cubeSum, Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.cubeSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactCube_uniformRightSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 3) n =
      Series.cubeSum (n + 1) / (n : Rat) ^ 4 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hfrac (a b : Rat) :
      a / (n : Rat) ^ 4 + b / (n : Rat) ^ 4 =
        (a + b) / (n : Rat) ^ 4 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
      Rat.pow_succ, Rat.mul_inv_cancel]
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              ((((j + 1 : Nat) : Rat) / (n : Rat)) ^ 3)) 0 =
        Series.cubeSum (k + 1) / (n : Rat) ^ 4 := by
    intro k
    induction k with
    | zero =>
        simp [Series.cubeSum, Rat.div_def]
        grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm :
            (1 / (n : Rat)) *
                ((((k : Rat) + 1) / (n : Rat)) ^ 3) =
              ((k : Rat) + 1) ^ 3 / (n : Rat) ^ 4 := by
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
        change Series.cubeSum (k + 1) / (n : Rat) ^ 4 +
          (1 / (n : Rat)) * (((k : Rat) + 1) / (n : Rat)) ^ 3 =
          Series.cubeSum (k + 1 + 1) / (n : Rat) ^ 4
        rw [hterm]
        have hs : Series.cubeSum (k + 1 + 1) =
            Series.cubeSum (k + 1) + ((k + 1 : Nat) : Rat) ^ 3 := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Series.cubeSum_succ]
        rw [hs]
        simpa [Rat.natCast_add] using hfrac _ _
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactCube_uniformLeftSum_le_one_fourth
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 3) n <= 1 / 4 := by
  rw [exactCube_uniformLeftSum_eq hn, Series.cubeSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 4 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 4)
  · rw [Rat.div_def, Rat.div_def]
    have hn1 : 1 <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    have hpoly : (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 <= (n : Rat) ^ 4 := by
      have hsq : ((n : Rat) - 1) ^ 2 <= (n : Rat) ^ 2 := by
        grind [Rat.pow_succ, Rat.sub_eq_add_neg]
      have h : (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 <=
          (n : Rat) ^ 2 * (n : Rat) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_left hsq
          (Rat.pow_nonneg (Rat.le_of_lt hnrat) : 0 <= (n : Rat) ^ 2)
      simpa [Rat.pow_succ, Rat.mul_assoc] using h
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 4)))
    have hcancel : ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹ *
          ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 =
          (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹ := by
            calc
              _ = ((n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹) *
                  (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
      _ <= (n : Rat) ^ 4 * 4⁻¹ := hscaled
      _ = 1 / 4 * (n : Rat) ^ 4 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

theorem exactCube_uniformRightSum_ge_one_fourth
    {n : Nat} (hn : 0 < n) :
    1 / 4 <=
      IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 3) n := by
  rw [exactCube_uniformRightSum_eq hn, Series.cubeSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 4 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 4)
  · rw [Rat.div_def, Rat.div_def]
    have hnp1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hnp1]
    have hminus : (n : Rat) + 1 - 1 = (n : Rat) := by grind
    rw [hminus]
    have hpoly : (n : Rat) ^ 4 <= ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 := by
      have hnonneg : 0 <= (n : Rat) := Rat.le_of_lt hnrat
      have hsq : (n : Rat) ^ 2 <= ((n : Rat) + 1) ^ 2 := by
        grind [Rat.pow_succ]
      have h : (n : Rat) ^ 2 * (n : Rat) ^ 2 <=
          ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_right hsq
          (Rat.pow_nonneg hnonneg : 0 <= (n : Rat) ^ 2)
      simpa [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm] using h
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 4)))
    have hcancel : ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    have horder : ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 =
        (n : Rat) ^ 2 * ((n : Rat) + 1) ^ 2 := by
      grind [Rat.mul_comm]
    calc
      1 / 4 * (n : Rat) ^ 4 = (n : Rat) ^ 4 * 4⁻¹ := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹ := by
        simpa [Rat.mul_assoc, Rat.mul_comm] using hscaled
      _ = ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹ *
          ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 := by
        calc
          _ = (((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹) *
              (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ = _ := by
            symm
            calc
              _ = (((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹) *
                  (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
  · exact hden

theorem exactCube_compute_contains_one_fourth (stage : Nat) :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 3) 3 stage).ContainsInterval
      { lo := 1 / 4, hi := 1 / 4 } := by
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactCube_lipschitz_on_unit stage
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactCube_lipschitz_on_unit stage
  have hleft := exactCube_uniformLeftSum_le_one_fourth hn
  have hright := exactCube_uniformRightSum_ge_one_fourth hn
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 hleft
  · exact Rat.le_trans hright hr.2

theorem exactRat_cube_integral_raw_equiv_one_fourth :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 3) 3 n)
    { lo := 1 / 4, hi := 1 / 4 }
  unfold QInterval.Overlaps
  exact exactCube_compute_contains_one_fourth n

end Integral

end ComputableAnalysis
