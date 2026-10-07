import ComputableAnalysis.ModularForms.IntegerReciprocalPowerRows

/-! Representation invariance of actual reciprocal-power row sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem upperPairedIntegerPower_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) (k n : Nat) :
    (upperPairedIntegerPower z hz k n).val.Equiv (upperPairedIntegerPower w hw k n).val :=
  add_equiv ((integerReciprocalPowerMap (-((n:Nat):Int)) k).eval_congr z w hz hw he)
    ((integerReciprocalPowerMap ((n:Nat):Int) k).eval_congr z w hz hw he)

theorem pairedIntegerPowerTailValue_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (k B : Nat) (hk : 2≤k) (hBz : Small z.val (B:Rat)) (hBw : Small w.val (B:Rat)) :
    (pairedIntegerPowerTailValue z hz k B).Equiv (pairedIntegerPowerTailValue w hw k B) :=
  inverseSquareSeriesValue_congr _ _ _ _ (2*32^k)
    (pairedIntegerPowerTailTerm_bound z hz k B hk hBz)
    (pairedIntegerPowerTailTerm_bound w hw k B hk hBw)
    (fun n => upperPairedIntegerPower_congr z w hz hw he k (pairedTailShift B n))

theorem integerPowerRowAssembly_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (k B : Nat) (hk : 2≤k) (hBz : Small z.val (B:Rat)) (hBw : Small w.val (B:Rat)) :
    (integerPowerRowAssembly z hz k B).Equiv (integerPowerRowAssembly w hw k B) :=
  add_equiv
    (add_equiv ((integerReciprocalPowerMap 0 k).eval_congr z w hz hw he)
      (ScalarSeries.block_congr _ _ (fun n => upperPairedIntegerPower_congr z w hz hw he k (n+1)) 0 (4*B)))
    (pairedIntegerPowerTailValue_congr z w hz hw he k B hk hBz hBw)

theorem integerReciprocalPowerRowSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val)
    (k : Nat) (hk : 2≤k) :
    (integerReciprocalPowerRowSum z hz k hk).val.Equiv (integerReciprocalPowerRowSum w hw k hk).val := by
  let B := pairedDerivativeCutoff z+pairedDerivativeCutoff w
  have hBz : Small z.val (B:Rat) := (pairedDerivativeCutoff_small z).mono (by
    exact_mod_cast (show pairedDerivativeCutoff z≤B by dsimp [B]; omega))
  have hBw : Small w.val (B:Rat) := (pairedDerivativeCutoff_small w).mono (by
    exact_mod_cast (show pairedDerivativeCutoff w≤B by dsimp [B]; omega))
  exact equiv_trans (integerReciprocalPowerRowSum z hz k hk).property
    (integerPowerRowAssembly_valid z hz k B hk hBz) (integerReciprocalPowerRowSum w hw k hk).property
    (integerPowerRowAssembly_cutoff_agreement z hz k (pairedDerivativeCutoff z) B hk (pairedDerivativeCutoff_small z) hBz)
    (equiv_trans (integerPowerRowAssembly_valid z hz k B hk hBz)
      (integerPowerRowAssembly_valid w hw k B hk hBw) (integerReciprocalPowerRowSum w hw k hk).property
      (integerPowerRowAssembly_congr z w hz hw he k B hk hBz hBw)
      (integerPowerRowAssembly_cutoff_agreement w hw k B (pairedDerivativeCutoff w) hk hBw (pairedDerivativeCutoff_small w)))

end ComputableAnalysis.ModularForms
