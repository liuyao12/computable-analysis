import ComputableAnalysis.FTC
import ComputableAnalysis.FunctionDomains

/-!
# A certified logarithmic-series value

This module starts the logarithm layer with the concrete value
`logTwoSeries = 1 - 1/2 + 1/3 - ...`.  The construction is entirely finite
rational arithmetic: its `n`th box is enclosed by two adjacent alternating
partial sums.  It is deliberately *not* yet identified with the integral
`∫_1^2 dt/t`; that identification belongs to the still-open general integral
construction and FTC bridge.
-/

namespace ComputableAnalysis

namespace Logarithm

/-- Reciprocation reverses the positive rational order.  This finite lemma is
the only order calculation needed for the interval evaluator of `1/x`. -/
private theorem one_div_antitone_of_pos {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact habpos

/-- Interval evaluation of the positive reciprocal kernel on `[1,2]`. -/
def oneOverXOneTwoEvalInterval (I : QInterval) : QInterval :=
  { lo := 1 / I.hi, hi := 1 / I.lo }

private theorem oneOverXOneTwoEvalInterval_width
    {I : QInterval} (hI : subintervalOf I 1 2) :
    (oneOverXOneTwoEvalInterval I).width =
      I.width * (1 / (I.lo * I.hi)) := by
  rcases hI with ⟨hlo, _hord, _hhi⟩
  have hlopos : 0 < I.lo := by grind
  have hhipos : 0 < I.hi := by grind
  have hlone : I.lo ≠ 0 := Rat.ne_of_gt hlopos
  have hhine : I.hi ≠ 0 := Rat.ne_of_gt hhipos
  unfold oneOverXOneTwoEvalInterval QInterval.width
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hlocancel : I.lo * I.lo⁻¹ = 1 := Rat.mul_inv_cancel I.lo hlone
  have hhicancel : I.hi * I.hi⁻¹ = 1 := Rat.mul_inv_cancel I.hi hhine
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The positive reciprocal kernel is interval-regular on `[1,2]`.

This is a literal rational certificate: an input interval of width at most
`1/(n+1)` is mapped to a reciprocal interval of no greater width.  It uses no
topological space, no completed real line, and no analytic import. -/
def oneOverXOnOneTwo_intervalRegular :
    IntervalRegularOn
      (RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)) := by
  refine
    { evalInterval := fun I _ _ => oneOverXOneTwoEvalInterval I
      inputPrecision := fun n => n + 1
      inputPrecision_pos := by
        intro n
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    change (1 : Rat) <= I.lo /\ I.lo <= I.hi /\ I.hi <= 2 at hI
    rcases hI with ⟨hlo, hord, hhi⟩
    have hlopos : 0 < I.lo := by grind
    have hhipos : 0 < I.hi := by grind
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hprod_ge_one : 1 <= I.lo * I.hi := by
      calc
        (1 : Rat) = 1 * 1 := by native_decide
        _ <= I.lo * 1 := Rat.mul_le_mul_of_nonneg_right hlo (by native_decide)
        _ <= I.lo * I.hi := Rat.mul_le_mul_of_nonneg_left
          (Rat.le_trans hlo hord) (Rat.le_of_lt hlopos)
    have hrecip_le_one : 1 / (I.lo * I.hi) <= 1 := by
      have h := one_div_antitone_of_pos
        (a := (1 : Rat)) (b := I.lo * I.hi) (by native_decide) hprod_ge_one
      calc
        1 / (I.lo * I.hi) <= 1 / (1 : Rat) := h
        _ = 1 := by native_decide
    constructor
    · rw [oneOverXOneTwoEvalInterval_width ⟨hlo, hord, hhi⟩]
      have hrecip_nonneg : 0 <= 1 / (I.lo * I.hi) := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hlopos hhipos))
      exact Rat.mul_nonneg hwidth_nonneg hrecip_nonneg
    · rw [oneOverXOneTwoEvalInterval_width ⟨hlo, hord, hhi⟩]
      calc
        I.width * (1 / (I.lo * I.hi)) <= I.width * 1 :=
          Rat.mul_le_mul_of_nonneg_left hrecip_le_one hwidth_nonneg
        _ = I.width := by grind
        _ <= 1 / (((n + 1 : Nat) : Rat)) := hwidth
  · intro I hI x hx n hxlo hxhi
    change (1 : Rat) <= I.lo /\ I.lo <= I.hi /\ I.hi <= 2 at hI
    rcases hI with ⟨hlo, _hord, _hhi⟩
    change (1 : Rat) <= x /\ x <= 2 at hx
    have hxpos : 0 < x := by grind
    change (oneOverXOneTwoEvalInterval I).ContainsInterval
      ((RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)).compute x hx n)
    rw [RatFun.oneOverXOnPositiveInterval_compute_eq 1 2
      (by native_decide) x hx n]
    unfold oneOverXOneTwoEvalInterval QInterval.ContainsInterval
    constructor
    · exact one_div_antitone_of_pos hxpos hxhi
    · exact one_div_antitone_of_pos (by grind) hxlo

/-- The reciprocal kernel `x ↦ 1/x` on `[1,2]` satisfies the project's
literal epsilon--delta continuity definition. -/
theorem oneOverXOnOneTwo_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn
      (RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)) :=
  oneOverXOnOneTwo_intervalRegular.epsilonDeltaContinuous

/-- One paired update of the alternating harmonic enclosure for `log 2`.

The first component is the upper endpoint and the second the lower endpoint.
At the `i`th update, the negative term has denominator `2*i+2` and the next
positive term has denominator `2*i+3`. -/
def logTwoStep (state : Rat × Rat) (i : Nat) : Rat × Rat :=
  let lo := state.1 - 1 / (2 * (i : Rat) + 2)
  let hi := lo + 1 / (2 * (i : Rat) + 3)
  (hi, lo)

/-- Paired partial-sum state for the logarithmic alternating series. -/
def logTwoState (n : Nat) : Rat × Rat :=
  (List.range n).foldl logTwoStep (1, 0)

/-- Lower endpoint of the `n`th alternating-harmonic enclosure. -/
def logTwoLo (n : Nat) : Rat :=
  (logTwoState n).2

/-- Upper endpoint of the `n`th alternating-harmonic enclosure. -/
def logTwoHi (n : Nat) : Rat :=
  (logTwoState n).1

/-- The rational interval at stage `n` for the alternating-harmonic
presentation of `log 2`. -/
def logTwoCompute (n : Nat) : QInterval :=
  { lo := logTwoLo n, hi := logTwoHi n }

theorem logTwoState_succ (n : Nat) :
    logTwoState (n + 1) = logTwoStep (logTwoState n) n := by
  unfold logTwoState
  rw [List.range_succ, List.foldl_append]
  rfl

theorem logTwo_width_eq (n : Nat) :
    (logTwoCompute n).width = 1 / ((2 * n + 1 : Nat) : Rat) := by
  cases n with
  | zero =>
      native_decide
  | succ n =>
      unfold logTwoCompute logTwoLo logTwoHi
      rw [logTwoState_succ]
      simp [logTwoStep]
      have hden :
          2 * ((n : Rat) + 1) + 1 = 2 * (n : Rat) + 3 := by
        grind
      rw [hden]
      grind [QInterval.width, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem logTwoLo_mono_succ (n : Nat) :
    logTwoLo n <= logTwoLo (n + 1) := by
  unfold logTwoLo
  rw [logTwoState_succ]
  simp [logTwoStep]
  have hterm :
      1 / (2 * (n : Rat) + 2) <=
        (logTwoState n).1 - (logTwoState n).2 := by
    change 1 / (2 * (n : Rat) + 2) <= (logTwoCompute n).width
    rw [logTwo_width_eq]
    have hden :
        ((2 * n + 2 : Nat) : Rat) = 2 * (n : Rat) + 2 := by
      exact_mod_cast (by rfl : 2 * n + 2 = 2 * n + 2)
    rw [← hden]
    exact FTC.one_div_nat_antitone
      (by omega : 0 < 2 * n + 1)
      (by omega : 0 < 2 * n + 2)
      (by omega : 2 * n + 1 <= 2 * n + 2)
  grind [Rat.sub_eq_add_neg]

theorem logTwoHi_anti_succ (n : Nat) :
    logTwoHi (n + 1) <= logTwoHi n := by
  unfold logTwoHi
  rw [logTwoState_succ]
  simp [logTwoStep]
  have hterm :
      1 / (2 * (n : Rat) + 3) <=
        1 / (2 * (n : Rat) + 2) := by
    have hden3 :
        ((2 * n + 3 : Nat) : Rat) = 2 * (n : Rat) + 3 := by
      exact_mod_cast (by rfl : 2 * n + 3 = 2 * n + 3)
    have hden2 :
        ((2 * n + 2 : Nat) : Rat) = 2 * (n : Rat) + 2 := by
      exact_mod_cast (by rfl : 2 * n + 2 = 2 * n + 2)
    rw [← hden3, ← hden2]
    exact FTC.one_div_nat_antitone
      (by omega : 0 < 2 * n + 2)
      (by omega : 0 < 2 * n + 3)
      (by omega : 2 * n + 2 <= 2 * n + 3)
  grind [Rat.sub_eq_add_neg]

theorem logTwoLo_mono {n m : Nat} (hnm : n <= m) :
    logTwoLo n <= logTwoLo m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih => exact Rat.le_trans ih (logTwoLo_mono_succ _)

theorem logTwoHi_anti {n m : Nat} (hnm : n <= m) :
    logTwoHi m <= logTwoHi n := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih => exact Rat.le_trans (logTwoHi_anti_succ _) ih

theorem logTwoCompute_ordered (n : Nat) :
    (logTwoCompute n).lo <= (logTwoCompute n).hi := by
  have hwidth := logTwo_width_eq n
  have hpos : 0 < 1 / ((2 * n + 1 : Nat) : Rat) :=
    one_div_nat_pos (by omega : 0 < 2 * n + 1)
  change logTwoHi n - logTwoLo n = 1 / ((2 * n + 1 : Nat) : Rat) at hwidth
  change logTwoLo n <= logTwoHi n
  grind [Rat.sub_eq_add_neg]

theorem logTwoCompute_nested (n m : Nat) (hnm : n <= m) :
    (logTwoCompute n).lo <= (logTwoCompute m).lo /\
      (logTwoCompute m).lo <= (logTwoCompute m).hi /\
      (logTwoCompute m).hi <= (logTwoCompute n).hi := by
  constructor
  · exact logTwoLo_mono hnm
  · constructor
    · exact logTwoCompute_ordered m
    · exact logTwoHi_anti hnm

theorem logTwoCompute_widths_shrink :
    RealRaw.WidthsShrinkToZero logTwoCompute := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  refine ⟨N, ?_⟩
  intro n hn
  rw [logTwo_width_eq]
  have hsmallN : 1 / (N : Rat) <= eps.val := by
    dsimp [N]
    exact FTC.one_div_den_succ_le_of_pos eps.property
  calc
    1 / ((2 * n + 1 : Nat) : Rat) <= 1 / (N : Rat) :=
      FTC.one_div_nat_antitone hNpos
        (by omega : 0 < 2 * n + 1)
        (by omega : N <= 2 * n + 1)
    _ <= eps.val := hsmallN

theorem logTwoCompute_valid : RealRaw.ValidCompute logTwoCompute := by
  constructor
  · intro n
    rw [logTwo_width_eq]
    exact Rat.le_of_lt (one_div_nat_pos (by omega : 0 < 2 * n + 1))
  · constructor
    · exact logTwoCompute_nested
    · exact logTwoCompute_widths_shrink

/-- A certified raw real for the logarithmic series
`log 2 = 1 - 1/2 + 1/3 - ...`.

Its validity and the displayed `O(1/n)` rate are finite rational proofs.  The
separate theorem identifying this raw value with `∫_1^2 dt/t` is intentionally
not claimed here: it requires the general integral/FTC bridge. -/
def logTwoSeries : RealRaw where
  compute := logTwoCompute
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [logTwo_width_eq, Rat.pow_one]
      exact FTC.one_div_nat_antitone hn
        (by omega : 0 < 2 * n + 1)
        (by omega : n <= 2 * n + 1))

theorem logTwoSeries_valid : logTwoSeries.Valid :=
  logTwoCompute_valid

/-- The displayed rate certificate for the logarithmic series is
`width(logTwoSeries[n]) <= 1/n` for every positive stage. -/
theorem logTwoSeries_width_le_one_div (n : Nat) (hn : 0 < n) :
    (logTwoSeries.compute n).width <= 1 / (n : Rat) := by
  rw [show logTwoSeries.compute n = logTwoCompute n by rfl, logTwo_width_eq]
  exact FTC.one_div_nat_antitone hn
    (by omega : 0 < 2 * n + 1)
    (by omega : n <= 2 * n + 1)

end Logarithm

end ComputableAnalysis
