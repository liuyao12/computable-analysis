import ComputableAnalysis.PowerSeries
import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic

/-! Factorial coefficients admit a geometric majorant with every positive
ratio. This permits holomorphic exponential charts of arbitrarily large radius. -/
namespace ComputableAnalysis.ModularForms
open RationalMajorant ComplexRaw FunctionTheory RiemannHilbert

/-- Executable rational coefficient budget for any requested geometric ratio. -/
def exponentialBudget (K : Rat) : Rat := factorialSeriesFiniteBound K⁻¹

theorem exponentialBudget_nonnegative (K : Rat) (hK : 0 < K) :
    0 ≤ exponentialBudget K :=
  factorialSeriesFiniteBound_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hK))

private theorem inverse_power_cancel (K : Rat) (hK : 0 < K) (n : Nat) :
    (K⁻¹)^n*K^n=1 := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hc := Rat.inv_mul_cancel K (Rat.ne_of_gt hK)
      grind

theorem exponential_coefficient_bound (K : Rat) (hK : 0 < K) (n : Nat) :
    1 / factorialRat n ≤ exponentialBudget K * K^n := by
  have hi : 0 ≤ K⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hK)
  have hb := factorialTailPartial_le_finiteBound hi n 1
  have ht : factorialTailTerm K⁻¹ n ≤ exponentialBudget K := by
    simpa only [factorialTailPartial, Nat.add_zero, Rat.zero_add, exponentialBudget] using hb
  have hu := inverse_power_cancel K hK n
  have hm := Rat.mul_le_mul_of_nonneg_right ht (Rat.pow_nonneg (n := n) (Rat.le_of_lt hK))
  have he : factorialTailTerm K⁻¹ n * K^n = 1 / factorialRat n := by
    unfold factorialTailTerm
    rw [Rat.div_def, Rat.div_def]
    grind
  rw [he] at hm
  exact hm

/-- The actual exponential coefficients, embedded as represented complex values. -/
def exponentialCoefficients (n : Nat) : ComplexRaw :=
  ofQComplex ⟨1/factorialRat n,0⟩

theorem exponentialCoefficients_valid (n : Nat) : (exponentialCoefficients n).Valid :=
  ofQComplex_valid _

theorem exponentialCoefficients_small (K : Rat) (hK : 0 < K) (n : Nat) :
    Small (exponentialCoefficients n) (exponentialBudget K*K^n) := by
  have hb := exponential_coefficient_bound K hK n
  have hp : 0 ≤ 1/factorialRat n := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (factorialRat_pos n))
  have hr := Rat.mul_nonneg (exponentialBudget_nonnegative K hK) (Rat.pow_nonneg (n := n) (Rat.le_of_lt hK))
  exact ⟨fun _ _ => by change -(exponentialBudget K*K^n) ≤ 1/factorialRat n; grind only,
    fun _ _ => hb, fun _ _ => by change -(exponentialBudget K*K^n) ≤ 0; grind only,
    fun _ _ => hr⟩

end ComputableAnalysis.ModularForms
