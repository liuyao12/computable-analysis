import ComputableAnalysis.ModularForms.WideLambertFifthRemainderSum
import ComputableAnalysis.ModularForms.WideLambertFifthValue
import ComputableAnalysis.ModularForms.WideLambertFifthSlope
import ComputableAnalysis.ModularForms.ScalarBlockRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The constructed wider value has the constructed slope as its actual first-order term. -/
theorem wideLambertFifthValue_remainder_bound (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (wideLambertFifthValue z hz).val (wideLambertFifthValue a ha).val
      (wideLambertFifthSlopeValue a ha).val (sub z.val a.val)) (135168*H^2) := by
  let f (n : Nat) : Scalar := ⟨weightedLambertTerm z (1/64) 5 n,
    weightedLambertTerm_valid z (1/64) 5 (by decide +kernel) (by decide +kernel) hz n⟩
  let g (n : Nat) : Scalar := ⟨weightedLambertTerm a (1/64) 5 n,
    weightedLambertTerm_valid a (1/64) 5 (by decide +kernel) (by decide +kernel) ha n⟩
  let d := wideLambertFifthSlopeTerm a ha
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let P (N : Nat) := SeriesLimitLaws.remainder (ScalarSeries.block (fun n => (f n).val) 0 N)
    (ScalarSeries.block (fun n => (g n).val) 0 N) (ScalarSeries.block (fun n => (d n).val) 0 N) v.val
  have pv (N : Nat) : (P N).Valid := SeriesLimitLaws.remainder_valid _ _ _ _
    (ScalarSeries.block_valid _ (fun n => (f n).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (g n).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (d n).property) 0 N) v.property
  let E (N : Nat) := 8*((1:Rat)/8)^N+8*((1:Rat)/8)^N+2*(2048*((1:Rat)/4)^N)*H
  have es : ShrinksToZero E := by
    have hs := SeriesLimitLaws.shrinks_scale _ wideLambertFifthSlopeValue_tail_shrinks (2*H)
      (Rat.mul_nonneg (by decide +kernel) hH)
    have hh := RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ wideLambertFifthValue_tail_shrinks wideLambertFifthValue_tail_shrinks) hs
    have he : (fun N => (8*((1:Rat)/8)^N+8*((1:Rat)/8)^N)+(2*H)*(2048*((1:Rat)/4)^N))=E := by
      funext N
      dsimp [E]
      grind only
    rw [he] at hh
    exact hh
  apply SeriesLimitLaws.small_of_prefix_bound _
    (SeriesLimitLaws.remainder_valid _ _ _ _ (wideLambertFifthValue z hz).property
      (wideLambertFifthValue a ha).property (wideLambertFifthSlopeValue a ha).property v.property)
    P pv (135168*H^2) E es
  · intro N
    exact SeriesLimitLaws.remainder_close _ _ _ _ _ _ _
      (wideLambertFifthValue z hz).property (wideLambertFifthValue a ha).property (wideLambertFifthSlopeValue a ha).property
      (ScalarSeries.block_valid _ (fun n => (f n).property) 0 N)
      (ScalarSeries.block_valid _ (fun n => (g n).property) 0 N)
      (ScalarSeries.block_valid _ (fun n => (d n).property) 0 N) v.property
      (8*((1:Rat)/8)^N) (8*((1:Rat)/8)^N) (2048*((1:Rat)/4)^N) H
      (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))) hH
      (wideLambertFifthValue_close_prefix z hz N) (wideLambertFifthValue_close_prefix a ha N)
      (wideLambertFifthSlopeValue_close_prefix a ha N) hd
  · intro N
    have he := scalar_block_remainder f g d v N
    exact Small.congr
      (ScalarSeries.block_valid _ (fun n => (wideLambertFifthTermRemainder a z ha hz n).property) 0 N)
      (pv N) (equiv_symm he) (wideLambertFifthRemainder_block_bound a z ha hz H hH hd N)
end ComputableAnalysis.ModularForms
