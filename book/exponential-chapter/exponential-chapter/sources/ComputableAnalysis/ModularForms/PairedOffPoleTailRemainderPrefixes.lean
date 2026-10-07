import ComputableAnalysis.ModularForms.PairedOffPoleTailTermRemainderBound
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Exact finite remainder sums and tails for the off-pole rational tail series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleTailRemainder_block_bound (B N k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val) N k)
      ((1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquareBlock N k*H*H) := by
  induction k with
  | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero,Rat.zero_mul]; decide +kernel)
  | succ k ih =>
    have h := LocalODE.small_add ih (pairedOffPoleTailTermRemainder_bound B (N+k) a z ha hz H hH hd)
    apply h.mono
    change (1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquareBlock N k*H*H +
      (1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquare (N+k+1)*H*H≤(1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquareBlock N (k+1)*H*H
    rw [reciprocalSquareBlock]
    grind only

theorem pairedOffPoleTailRemainder_block_tail (B N k : Nat) (hN : 0<N) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val) N k)
      ((1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*(N:Rat)⁻¹*H*H) := by
  apply (pairedOffPoleTailRemainder_block_bound B N k a z ha hz H hH hd).mono
  have hbb : 0≤(B:Rat)*(B:Rat)*(B:Rat) := Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) Rat.natCast_nonneg
  have hcoeff : 0≤(1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat)) := by grind only
  have hC : 0≤((1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat)):Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg hcoeff hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) hC
  grind only

theorem pairedOffPoleTailRemainderPrefix_identity (B N k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) :
    (ScalarSeries.block (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val) N k).Equiv
      (SeriesLimitLaws.remainder
        (ScalarSeries.block (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).val) N k)
        (ScalarSeries.block (fun n => ((pairedOffPoleTailTermMap B n).eval a ha).val) N k)
        (ScalarSeries.block (fun n => (pairedOffPoleTailDerivativeTerm B n a ha).val) N k)
        (sub z.val a.val)) := by
  have he := ScalarSeries.block_congr _ _
    (fun n => equiv_symm (pairedOffPoleTailTerm_remainder_identity B n a z ha hz)) N k
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).property) N k)
    (ScalarSeries.block_valid _ (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) N k)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (ScalarSeries.block_valid _ (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).property) N k)
      (ScalarSeries.block_valid _ (fun n => ((pairedOffPoleTailTermMap B n).eval a ha).property) N k)
      (ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailDerivativeTerm B n a ha).property) N k)
      (sub_valid z.property a.property)) he
    (finiteRemainderSum _ _ _
      (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).property)
      (fun n => ((pairedOffPoleTailTermMap B n).eval a ha).property)
      (fun n => (pairedOffPoleTailDerivativeTerm B n a ha).property)
      _ (sub_valid z.property a.property) N k)

end ComputableAnalysis.ModularForms
