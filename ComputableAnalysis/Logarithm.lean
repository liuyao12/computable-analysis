import ComputableAnalysis.FTC

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
