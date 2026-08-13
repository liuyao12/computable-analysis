import ComputableAnalysis.Calculus

/-!
# Monotonicity of rational monomials on the unit interval

This is the reusable order component behind the finite monomial integral and
MVT certificates.  It proves only a rational-input monotonicity statement;
no completed real function or limiting argument is introduced.
-/

namespace ComputableAnalysis

theorem exactRat_monomial_nondecreasing (n : Nat) :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1) := by
  intro x y hx hy hxy stage
  rw [FunctionOnInterval.exactRat_compute (fun x : Rat => x ^ n) 0 1 x hx stage]
  rw [FunctionOnInterval.exactRat_compute (fun x : Rat => x ^ n) 0 1 y hy stage]
  have hx0 : 0 <= x := by simpa [FunctionOnInterval.exactRat] using hx.1
  have hy0 : 0 <= y := by simpa [FunctionOnInterval.exactRat] using hy.1
  have hpow : ∀ k : Nat, x ^ k <= y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hleft : x ^ k * x <= y ^ k * x :=
          Rat.mul_le_mul_of_nonneg_right ih hx0
        have hright : y ^ k * x <= y ^ k * y :=
          Rat.mul_le_mul_of_nonneg_left hxy (Rat.pow_nonneg hy0)
        calc
          x ^ (k + 1) = x ^ k * x := by rw [Rat.pow_succ]
          _ <= y ^ k * x := hleft
          _ <= y ^ k * y := hright
          _ = y ^ (k + 1) := by rw [Rat.pow_succ]
  exact hpow n

end ComputableAnalysis
