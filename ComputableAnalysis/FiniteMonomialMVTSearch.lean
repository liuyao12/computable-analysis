import ComputableAnalysis.FiniteBisectionIteration
import ComputableAnalysis.Differential
import ComputableAnalysis.FTC

/-!
# Potential-infinity Mean Value searches for monomials

For `x^(n+1)` on `[0,1]`, the secant slope is `1` and the normalized
derivative target is `1/(n+1)`.  This file packages the general bisection
certificate for that target.  It is an interval search, not an assertion that
the generally irrational intermediate point is attained by a rational input.
-/

namespace ComputableAnalysis

def monomialUnitNormalizedDerivativeAverage (n : Nat) : Rat :=
  1 / ((n + 1 : Nat) : Rat)

def monomialUnitDerivativeTarget (n : Nat) : Rat -> Rat :=
  fun x => x ^ n

theorem monomialUnitNormalizedDerivativeAverage_pos (n : Nat) :
    0 < monomialUnitNormalizedDerivativeAverage n := by
  unfold monomialUnitNormalizedDerivativeAverage
  rw [Rat.div_def]
  exact Rat.mul_pos (by native_decide)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos n)))

theorem monomialUnitNormalizedDerivativeAverage_in_unit (n : Nat) :
    0 <= monomialUnitNormalizedDerivativeAverage n /\
      monomialUnitNormalizedDerivativeAverage n <= 1 := by
  constructor
  · exact Rat.le_of_lt (monomialUnitNormalizedDerivativeAverage_pos n)
  · have h := FTC.one_div_nat_antitone
      (n := 1) (m := n + 1)
      (by native_decide) (Nat.succ_pos n) (by omega)
    calc
      monomialUnitNormalizedDerivativeAverage n <= 1 / (1 : Rat) := by
        simpa [monomialUnitNormalizedDerivativeAverage] using h
      _ = 1 := by native_decide

theorem monomialUnit_target_endpoint_bracket (n : Nat) :
    monomialUnitDerivativeTarget n 0 <=
        monomialUnitNormalizedDerivativeAverage n /\
      monomialUnitNormalizedDerivativeAverage n <=
        monomialUnitDerivativeTarget n 1 := by
  have htarget := monomialUnitNormalizedDerivativeAverage_in_unit n
  cases n with
  | zero =>
      constructor <;> native_decide
  | succ n =>
      constructor
      · simp [monomialUnitDerivativeTarget, Rat.pow_succ]
        exact htarget.1
      · have hone : (1 : Rat) ^ (n + 1) = 1 := by
          rw [show n + 1 = Nat.succ n by omega, Rat.pow_succ]
          have hone_all : ∀ k : Nat, (1 : Rat) ^ k = 1 := by
            intro k
            induction k with
            | zero => simp
            | succ k ih =>
                rw [Rat.pow_succ, ih]
                simp
          rw [hone_all]
          grind
        change monomialUnitNormalizedDerivativeAverage (n + 1) <=
          (1 : Rat) ^ (n + 1)
        rw [hone]
        exact htarget.2

theorem monomialUnit_secant_eq_succ_mul_normalizedDerivativeAverage
    (n : Nat) :
    ExactFunction.differenceQuotient
        (fun z => z ^ (n + 1)) 0 (1 - 0) =
      ((n + 1 : Nat) : Rat) *
        monomialUnitNormalizedDerivativeAverage n := by
  unfold ExactFunction.differenceQuotient
    monomialUnitNormalizedDerivativeAverage
  have hne : ((n + 1 : Nat) : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
  have hzero : (0 : Rat) ^ (n + 1) = 0 := by
    rw [show n + 1 = Nat.succ n by omega, Rat.pow_succ]
    simp
  have hone : (1 : Rat) ^ (n + 1) = 1 := by
    rw [show n + 1 = Nat.succ n by omega, Rat.pow_succ]
    have hone_all : ∀ k : Nat, (1 : Rat) ^ k = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Rat.pow_succ, ih]
          simp
    rw [hone_all]
    grind
  change (((0 : Rat) + (1 - 0)) ^ (n + 1) -
    (0 : Rat) ^ (n + 1)) / (1 - 0) = _
  rw [show (0 : Rat) + (1 - 0) = 1 by native_decide, hzero, hone]
  have hunit : (1 : Rat) - 0 = 1 := by native_decide
  rw [hunit]
  rw [Rat.natCast_add]
  have hqne : (n : Rat) + 1 ≠ 0 := by
    exact Rat.ne_of_gt (by
      have hn : 0 <= (n : Rat) := by exact_mod_cast (Nat.zero_le n)
      grind)
  have hqcancel : ((n : Rat) + 1) * ((n : Rat) + 1)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hqne
  rw [show (1 : Rat) / 1 = 1 by native_decide]
  simp only [Rat.div_def, Rat.one_mul]
  change 1 = ((n : Rat) + 1) * ((n : Rat) + 1)⁻¹
  rw [hqcancel]

theorem monomialUnit_mvt_bisection_tolerance_certificate
    (n : Nat) (eps : QPos) :
    let J := monotoneTargetBisectionIterate
      (monomialUnitDerivativeTarget n)
      (monomialUnitNormalizedDerivativeAverage n)
      eps.val.den { lo := 0, hi := 1 }
    J.lo <= J.hi /\
      (monomialUnitDerivativeTarget n J.lo <=
          monomialUnitNormalizedDerivativeAverage n /\
        monomialUnitNormalizedDerivativeAverage n <=
          monomialUnitDerivativeTarget n J.hi) /\
      (J.lo >= 0 /\ J.hi <= 1) /\
      J.width <= eps.val := by
  have htarget := monomialUnit_target_endpoint_bracket n
  simpa using
    (monotoneTargetBisectionIterate_tolerance_certificate
      (f := monomialUnitDerivativeTarget n)
      (I := ({ lo := 0, hi := 1 } : QInterval))
      (monomialUnitNormalizedDerivativeAverage n)
      (by native_decide)
      htarget.1 htarget.2 (by native_decide) eps)

end ComputableAnalysis
