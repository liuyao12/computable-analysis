import ComputableAnalysis.ModularForms.PairedFullPrefixes

/-! Cutoff independence from common literal prefixes and shrinking errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedFullValue_cutoff (z : Scalar) (hd : PairedSeriesDomain z) (B C : Nat)
    (hB : Small z.val (B:Rat)) (hC : Small z.val (C:Rat)) :
    (pairedFullValue z hd B hB).Equiv (pairedFullValue z hd C hC) := by
  let p := fun N => ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 (4*B+4*C+N+1)
  have hp : ∀ N, (p N).Valid := fun N =>
    ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 _
  let eB := fun N => (((16*B:Nat):Rat))*(((N+4*C+1:Nat):Rat))⁻¹
  let eC := fun N => (((16*C:Nat):Rat))*(((N+4*B+1:Nat):Rat))⁻¹
  have heB : ShrinksToZero eB :=
    SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*B)) (4*C)
  have heC : ShrinksToZero eC :=
    SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*C)) (4*B)
  have hnB (N : Nat) : 0≤eB N :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt ((Rat.inv_pos).mpr (by
      exact_mod_cast (show 0<N+4*C+1 by omega))))
  have hnC (N : Nat) : 0≤eC N :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt ((Rat.inv_pos).mpr (by
      exact_mod_cast (show 0<N+4*B+1 by omega))))
  apply RepresentedCauchySum.unique p hp (fun N => eB N+eC N)
    (RepresentedCauchySum.sum_shrinks eB eC heB heC)
    _ _ (pairedFullValue_valid z hd B hB) (pairedFullValue_valid z hd C hC)
  · intro N
    have h := pairedFullValue_close z hd B hB (N+4*C)
    rw [show 4*B+(N+4*C+1)=4*B+4*C+N+1 by omega] at h
    exact h.mono (by change eB N≤eB N+eC N; have := hnC N; grind only)
  · intro N
    have h := pairedFullValue_close z hd C hC (N+4*B)
    rw [show 4*C+(N+4*B+1)=4*B+4*C+N+1 by omega] at h
    exact h.mono (by change eC N≤eB N+eC N; have := hnB N; grind only)

theorem pairedFullValue_agreement (z w : Scalar) (hd : PairedSeriesDomain z)
    (hw : PairedSeriesDomain w) (B C : Nat) (hz : Small z.val (B:Rat))
    (hwC : Small w.val (C:Rat)) (he : z.val.Equiv w.val) :
    (pairedFullValue z hd B hz).Equiv (pairedFullValue w hw C hwC) := by
  have hwB := Small.congr z.property w.property he hz
  exact equiv_trans (pairedFullValue_valid z hd B hz) (pairedFullValue_valid w hw B hwB)
    (pairedFullValue_valid w hw C hwC) (pairedFullValue_congr z w hd hw B hz hwB he)
    (pairedFullValue_cutoff w hw B C hwB hwC)

end ComputableAnalysis.ModularForms
