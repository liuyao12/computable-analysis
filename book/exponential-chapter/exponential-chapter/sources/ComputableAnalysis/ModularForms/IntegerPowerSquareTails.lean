import ComputableAnalysis.ModularForms.IntegerPowerSquarePairs
import ComputableAnalysis.ModularForms.PairedReciprocalSquareTail

/-! Agreement of constructed square tails with different quantitative majorants. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem inverseSquareSeriesValue_congr_bounds (t u : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hu : ∀ n, (u n).Valid) (C D : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1)))
    (hU : ∀ n, Small (u n) ((D:Rat)*reciprocalSquare (n+1)))
    (he : ∀ n, (t n).Equiv (u n)) :
    (inverseSquareSeriesValue t ht C).Equiv (inverseSquareSeriesValue u hu D) := by
  have hp (K n : Nat) : 0≤(K:Rat)*(((n+1:Nat):Rat))⁻¹ :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt ((Rat.inv_pos).mpr (by
      exact_mod_cast (show 0<n+1 by omega))))
  exact RepresentedCauchySum.value_congr _ _ _ _ _ _
    (pairedReciprocalTail_shrinks C) (pairedReciprocalTail_shrinks D) (hp C) (hp D)
    (inverseSquare_prefix_cauchy t ht C hB) (inverseSquare_prefix_cauchy u hu D hU)
    (fun N => ScalarSeries.block_congr t u he 0 (N+1))

theorem pairedIntegerPower_square_tail_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hB : Small z.val (B:Rat)) :
    (pairedIntegerPowerTailValue z hz 2 B).Equiv (pairedReciprocalSquareTailValue z hz B) :=
  inverseSquareSeriesValue_congr_bounds _ _ _ _ (2*32^2) 1024
    (pairedIntegerPowerTailTerm_bound z hz 2 B (by omega) hB)
    (pairedReciprocalSquareTailTerm_bound z hz B hB)
    (fun n => upperPairedIntegerPower_square_agreement z hz (pairedTailShift B n))

end ComputableAnalysis.ModularForms
