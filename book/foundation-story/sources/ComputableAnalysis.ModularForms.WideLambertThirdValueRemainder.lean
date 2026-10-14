import ComputableAnalysis.ModularForms.WideLambertThirdRemainderSum
import ComputableAnalysis.ModularForms.WideLambertThirdValue
import ComputableAnalysis.ModularForms.WideLambertThirdSlope
import ComputableAnalysis.ModularForms.ScalarBlockRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The constructed wider value has the constructed slope as its actual first-order term. -/
theorem wideLambertThirdValue_remainder_bound (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (wideLambertThirdValue z hz).val (wideLambertThirdValue a ha).val
      (wideLambertThirdSlopeValue a ha).val (sub z.val a.val)) (135168*H^2) := by
  let f (n : Nat) : Scalar := ⟨weightedLambertTerm z (1/64) 3 n,
    weightedLambertTerm_valid z (1/64) 3 (by decide +kernel) (by decide +kernel) hz n⟩
  let g (n : Nat) : Scalar := ⟨weightedLambertTerm a (1/64) 3 n,
    weightedLambertTerm_valid a (1/64) 3 (by decide +kernel) (by decide +kernel) ha n⟩
  let d := wideLambertThirdSlopeTerm a ha
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let P (N : Nat) := SeriesLimitLaws.remainder (ScalarSeries.block (fun n => (f n).val) 0 N)
    (ScalarSeries.block (fun n => (g n).val) 0 N) (ScalarSeries.block (fun n => (d n).val) 0 N) v.val
  have pv (N : Nat) : (P N).Valid := SeriesLimitLaws.remainder_valid _ _ _ _
    (ScalarSeries.block_valid _ (fun n => (f n).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (g n).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (d n).property) 0 N) v.property
  let E (N : Nat) := ((1:Rat)/2)*((1:Rat)/4)^N+((1:Rat)/2)*((1:Rat)/4)^N+2*(128*((1:Rat)/2)^N)*H
  have es : ShrinksToZero E := by
    have hs := SeriesLimitLaws.shrinks_scale _ wideLambertThirdSlopeValue_tail_shrinks (2*H)
      (Rat.mul_nonneg (by decide +kernel) hH)
    have hh := RepresentedCauchySum.sum_shrinks _ _
      (RepresentedCauchySum.sum_shrinks _ _ wideLambertThirdValue_tail_shrinks wideLambertThirdValue_tail_shrinks) hs
    have he : (fun N => (((1:Rat)/2)*((1:Rat)/4)^N+((1:Rat)/2)*((1:Rat)/4)^N)+(2*H)*(128*((1:Rat)/2)^N))=E := by
      funext N
      dsimp [E]
      grind only
    rw [he] at hh
    exact hh
  apply SeriesLimitLaws.small_of_prefix_bound _
    (SeriesLimitLaws.remainder_valid _ _ _ _ (wideLambertThirdValue z hz).property
      (wideLambertThirdValue a ha).property (wideLambertThirdSlopeValue a ha).property v.property)
    P pv (135168*H^2) E es
  · intro N
    exact SeriesLimitLaws.remainder_close _ _ _ _ _ _ _
      (wideLambertThirdValue z hz).property (wideLambertThirdValue a ha).property (wideLambertThirdSlopeValue a ha).property
      (ScalarSeries.block_valid _ (fun n => (f n).property) 0 N)
      (ScalarSeries.block_valid _ (fun n => (g n).property) 0 N)
      (ScalarSeries.block_valid _ (fun n => (d n).property) 0 N) v.property
      (((1:Rat)/2)*((1:Rat)/4)^N) (((1:Rat)/2)*((1:Rat)/4)^N) (128*((1:Rat)/2)^N) H
      (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))) hH
      (wideLambertThirdValue_close_prefix z hz N) (wideLambertThirdValue_close_prefix a ha N)
      (wideLambertThirdSlopeValue_close_prefix a ha N) hd
  · intro N
    have he := scalar_block_remainder f g d v N
    exact Small.congr
      (ScalarSeries.block_valid _ (fun n => (wideLambertThirdTermRemainder a z ha hz n).property) 0 N)
      (pv N) (equiv_symm he) (wideLambertThirdRemainder_block_bound a z ha hz H hH hd N)
end ComputableAnalysis.ModularForms
