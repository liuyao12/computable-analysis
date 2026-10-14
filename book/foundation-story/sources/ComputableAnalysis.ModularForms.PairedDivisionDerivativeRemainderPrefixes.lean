import ComputableAnalysis.ModularForms.PairedDivisionDerivativeRemainderBound
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Exact finite remainder sums and tails for the division derivative series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedDivisionDerivativeRemainder_block_bound (N k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedDivisionDerivativeRemainder a z ha hz n).val) N k)
      (61440*reciprocalSquareBlock N k*H*H) := by
  induction k with
  | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero,Rat.zero_mul]; decide +kernel)
  | succ k ih =>
    have h := LocalODE.small_add ih (pairedDivisionDerivativeRemainder_bound a z ha hz H hH hd (N+k))
    apply h.mono
    change 61440*reciprocalSquareBlock N k*H*H +
      61440*reciprocalSquare (N+k+1)*H*H≤61440*reciprocalSquareBlock N (k+1)*H*H
    rw [reciprocalSquareBlock]
    grind only

theorem pairedDivisionDerivativeRemainder_block_tail (N k : Nat) (hN : 0<N) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => (pairedDivisionDerivativeRemainder a z ha hz n).val) N k)
      (61440*(N:Rat)⁻¹*H*H) := by
  apply (pairedDivisionDerivativeRemainder_block_bound N k a z ha hz H hH hd).mono
  have hC : 0≤(61440:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) hC
  grind only

theorem pairedDivisionDerivativeRemainderPrefix_identity (N k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) :
    (ScalarSeries.block (fun n => (pairedDivisionDerivativeRemainder a z ha hz n).val) N k).Equiv
      (SeriesLimitLaws.remainder
        (ScalarSeries.block (fun n => ((pairedDivisionDerivativeTermMap n).eval z hz).val) N k)
        (ScalarSeries.block (fun n => ((pairedDivisionDerivativeTermMap n).eval a ha).val) N k)
        (ScalarSeries.block (fun n => (pairedDivisionSecondDerivativeTerm a ha n).val) N k)
        (sub z.val a.val)) := by
  have he := ScalarSeries.block_congr _ _
    (fun n => equiv_symm (pairedDivisionDerivativeTermMap_remainder a z ha hz n)) N k
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (pairedDivisionDerivativeRemainder a z ha hz n).property) N k)
    (ScalarSeries.block_valid _ (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) N k)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (ScalarSeries.block_valid _ (fun n => ((pairedDivisionDerivativeTermMap n).eval z hz).property) N k)
      (ScalarSeries.block_valid _ (fun n => ((pairedDivisionDerivativeTermMap n).eval a ha).property) N k)
      (ScalarSeries.block_valid _ (fun n => (pairedDivisionSecondDerivativeTerm a ha n).property) N k)
      (sub_valid z.property a.property)) he
    (finiteRemainderSum _ _ _
      (fun n => ((pairedDivisionDerivativeTermMap n).eval z hz).property)
      (fun n => ((pairedDivisionDerivativeTermMap n).eval a ha).property)
      (fun n => (pairedDivisionSecondDerivativeTerm a ha n).property)
      _ (sub_valid z.property a.property) N k)

end ComputableAnalysis.ModularForms
