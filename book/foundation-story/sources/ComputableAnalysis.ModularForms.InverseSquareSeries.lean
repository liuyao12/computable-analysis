import ComputableAnalysis.ModularForms.ReciprocalSquareTail
import ComputableAnalysis.RiemannHilbert.GeometricSeries

/-! Executable sums of supplied represented terms with inverse-square bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem inverseSquare_block_bound (t : Nat → ComplexRaw) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) (N k : Nat) :
    Small (ScalarSeries.block t N k) ((C:Rat)*reciprocalSquareBlock N k) := by
  induction k with
  | zero => exact Small.zero (by change (0:Rat)≤(C:Rat)*0; simp [Rat.mul_zero])
  | succ k ih =>
    have h := LocalODE.small_add ih (hB (N+k))
    have he : (C:Rat)*reciprocalSquareBlock N k+(C:Rat)*reciprocalSquare (N+k+1)=
        (C:Rat)*reciprocalSquareBlock N (k+1) := by
      rw [reciprocalSquareBlock]; grind only
    rw [he] at h
    exact h

theorem inverseSquare_block_tail (t : Nat → ComplexRaw) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) (N k : Nat) (hN : 0<N) :
    Small (ScalarSeries.block t N k) ((C:Rat)*(N:Rat)⁻¹) :=
  (inverseSquare_block_bound t C hB N k).mono
    (Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) Rat.natCast_nonneg)

theorem inverseSquare_prefix_cauchy (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block t 0 (n+1)) (ScalarSeries.block t 0 (N+1)))
      ((C:Rat)*(((N+1:Nat):Rat))⁻¹) := by
  have he := ScalarSeries.prefix_difference t ht (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr (ScalarSeries.block_valid t ht (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid t ht 0 (n+1)) (ScalarSeries.block_valid t ht 0 (N+1)))
    (equiv_symm he) (inverseSquare_block_tail t C hB (N+1) (n-N) (by omega))

def inverseSquareSeriesValue (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (C : Nat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block t 0 (N+1))
    (fun N => ScalarSeries.block_valid t ht 0 (N+1))
    (fun N => (C:Rat)*(((N+1:Nat):Rat))⁻¹)

theorem inverseSquareSeriesValue_valid (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) :
    (inverseSquareSeriesValue t ht C).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedReciprocalTail_shrinks C)
    (inverseSquare_prefix_cauchy t ht C hB)

theorem inverseSquareSeriesValue_close (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) (N : Nat) :
    Small (sub (inverseSquareSeriesValue t ht C) (ScalarSeries.block t 0 (N+1)))
      ((C:Rat)*(((N+1:Nat):Rat))⁻¹) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (inverseSquare_prefix_cauchy t ht C hB) N

theorem inverseSquareSeriesValue_congr (t u : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hu : ∀ n, (u n).Valid) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1)))
    (hU : ∀ n, Small (u n) ((C:Rat)*reciprocalSquare (n+1)))
    (he : ∀ n, (t n).Equiv (u n)) :
    (inverseSquareSeriesValue t ht C).Equiv (inverseSquareSeriesValue u hu C) := by
  have hp (n : Nat) : 0≤(C:Rat)*(((n+1:Nat):Rat))⁻¹ :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt ((Rat.inv_pos).mpr (by
      exact_mod_cast (show 0<n+1 by omega))))
  exact RepresentedCauchySum.value_congr _ _ _ _ _ _
    (pairedReciprocalTail_shrinks C) (pairedReciprocalTail_shrinks C) hp hp
    (inverseSquare_prefix_cauchy t ht C hB) (inverseSquare_prefix_cauchy u hu C hU)
    (fun N => ScalarSeries.block_congr t u he 0 (N+1))

end ComputableAnalysis.ModularForms
