import ComputableAnalysis.Apery.DifferentialEquation

/-! The rational companion and the exact separation of its approximants.
Identifying their limit with the independent zeta evaluator remains separate. -/
namespace ComputableAnalysis.Apery
open FormalPowerSeries

/-- A pair recursion makes the rational computation linear in the index. -/
def companionPair : Nat → Rat × Rat
  | 0 => (0, 6)
  | n+1 => let p := companionPair n
    (p.2, (recurrencePolynomial ((n : Rat)+1)*p.2-((n : Rat)+1)^3*p.1)/((n : Rat)+2)^3)

def companion (n : Nat) : Rat := (companionPair n).1

@[simp] theorem companion_next (n : Nat) : companion (n+1) = (companionPair n).2 := rfl
@[simp] theorem companion_zero : companion 0 = 0 := rfl
@[simp] theorem companion_one : companion 1 = 6 := rfl

theorem companion_recurrence (n : Nat) :
    ((n : Rat)+2)^3*companion (n+2) - recurrencePolynomial ((n : Rat)+1)*companion (n+1) +
      ((n : Rat)+1)^3*companion n = 0 := by
  have hn := Rat.natCast_nonneg (a := n)
  have hp : ((n : Rat)+2)^3 ≠ 0 := Rat.ne_of_gt (Rat.pow_pos (by grind))
  have he := Rat.mul_inv_cancel (((n : Rat)+2)^3) hp
  change ((n : Rat)+2)^3*((recurrencePolynomial ((n : Rat)+1)*(companionPair n).2-
    ((n : Rat)+1)^3*(companionPair n).1)/((n : Rat)+2)^3) -
    recurrencePolynomial ((n : Rat)+1)*(companionPair n).2+
    ((n : Rat)+1)^3*(companionPair n).1=0
  simp only [Rat.div_def]
  grind only

/-- The companion solves an inhomogeneous equation, with source `6t`. -/
theorem companion_equation (n : Nat) :
    operator 1 companion n = if n=1 then 6 else 0 := by
  cases n with
  | zero => simp [operator, eulerPower, shiftedEuler, mulX]; grind
  | succ n => cases n with
    | zero => simp [operator, eulerPower, shiftedEuler, mulX, companionPair]; grind
    | succ n =>
      rw [operator_coefficient]
      have h := companion_recurrence n
      have hn : ¬ n+1+1=1 := by omega
      simp only [hn, ite_false]
      grind only

/-- A discrete Wronskian: the approximants cannot stabilize at a rational value. -/
theorem casoratian (n : Nat) :
    ((n : Rat)+1)^3*(number n*companion (n+1)-number (n+1)*companion n) = 6 := by
  induction n with
  | zero => rw [number_zero, number_one, companion_zero, companion_one]; decide +kernel
  | succ n ih =>
    have ha := number_recurrence n
    have hb := companion_recurrence n
    have h1 := congrArg (fun z : Rat => z*companion (n+1)) ha
    have h2 := congrArg (fun z : Rat => z*number (n+1)) hb
    simp only [Rat.natCast_add, Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
    grind only

theorem number_ge_one (n : Nat) : 1 ≤ number n := by
  have all (N : Nat) : 1 ≤ sumBelow (term n) (N+1) := by
    induction N with
    | zero => rw [sumBelow_succ, sumBelow_zero, term_zero]; decide +kernel
    | succ N ih =>
      rw [sumBelow_succ]
      have h : 0 ≤ term n (N+1) := by
        simp only [term, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
        exact rat_square_nonneg_basic _
      grind only
  exact all n

/-- The rational approximants; no identification with zeta is built into the definition. -/
def approximant (n : Nat) : Rat := companion n/number n

theorem approximant_difference (n : Nat) :
    approximant (n+1)-approximant n =
      6/(((n : Rat)+1)^3*number n*number (n+1)) := by
  have ha := number_ge_one n
  have hb := number_ge_one (n+1)
  have hn := Rat.natCast_nonneg (a := n)
  have hA := Rat.mul_inv_cancel (number n) (by grind)
  have hB := Rat.mul_inv_cancel (number (n+1)) (by grind)
  have hN := Rat.mul_inv_cancel (((n : Rat)+1)^3) (Rat.ne_of_gt (Rat.pow_pos (by grind)))
  have h := casoratian n
  unfold approximant
  simp only [Rat.div_def, Rat.inv_mul_rev]
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at h hN
  grind only

/-- Consecutive rational approximants are strictly separated by the recurrence. -/
theorem approximant_increasing (n : Nat) : approximant n < approximant (n+1) := by
  have ha := number_ge_one n
  have hb := number_ge_one (n+1)
  have hn := Rat.natCast_nonneg (a := n)
  have hp : 0 < ((n : Rat)+1)^3*number n*number (n+1) :=
    Rat.mul_pos (Rat.mul_pos (Rat.pow_pos (by grind)) (by grind)) (by grind)
  have hd : 0 < 6/(((n : Rat)+1)^3*number n*number (n+1)) := by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide) (Rat.inv_pos.mpr hp)
  rw [← approximant_difference] at hd
  grind only

end ComputableAnalysis.Apery
