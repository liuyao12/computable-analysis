import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeRemainderBound
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! The actual infinite first-derivative tail is holomorphic, with constructed second derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleTailDerivativeRemainder_prefix_bound (B k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => DomainFunctions.remainder
      (pairedOffPoleTailDerivativeTermMap B n) a ha
      (pairedOffPoleTailSecondDerivativeTerm B n a ha) z hz) 0 k)
      (2*(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*H*H) := by
  have block_bound (t : Nat → ComplexRaw) (C : Rat)
      (ht : ∀ n, Small (t n) (C*reciprocalSquare (n+1))) (k : Nat) :
      Small (ScalarSeries.block t 0 k) (C*reciprocalSquareBlock 0 k) := by
    induction k with
    | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero]; decide +kernel)
    | succ k ih =>
      have hsum := LocalODE.small_add ih (ht k)
      simpa only [ScalarSeries.block.eq_2,Nat.zero_add] using hsum.mono
        (show C*reciprocalSquareBlock 0 k+C*reciprocalSquare (k+1)≤C*reciprocalSquareBlock 0 (k+1) by
          rw [reciprocalSquareBlock]; simp only [Nat.zero_add]; grind only)
  have hb (k : Nat) :
      Small (ScalarSeries.block (fun n => DomainFunctions.remainder
        (pairedOffPoleTailDerivativeTermMap B n) a ha
        (pairedOffPoleTailSecondDerivativeTerm B n a ha) z hz) 0 k)
        ((pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*reciprocalSquareBlock 0 k*H*H) := by
    have h := block_bound
      (fun n => DomainFunctions.remainder (pairedOffPoleTailDerivativeTermMap B n) a ha
        (pairedOffPoleTailSecondDerivativeTerm B n a ha) z hz)
      ((pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*H*H)
      (fun n => (pairedOffPoleTailDerivativeTerm_remainder_bound B n a z ha hz H hH hd).mono
        (by grind only)) k
    exact h.mono (by grind only)
  apply (hb k).mono
  have hC : 0≤(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg hH) hH
  have h := Rat.mul_le_mul_of_nonneg_left (inverseSquareBlock_zero_bound k) hC
  grind only

theorem pairedOffPoleTailDerivative_sum_remainder_bound (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder
      (pairedOffPoleTailDerivativeValue B z hz).val
      (pairedOffPoleTailDerivativeValue B a ha).val
      (pairedOffPoleTailSecondDerivativeValue B a ha).val (sub z.val a.val))
      (2*(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*H*H) := by
  let f := fun n => (pairedOffPoleTailDerivativeTerm B n z hz).val
  let g := fun n => (pairedOffPoleTailDerivativeTerm B n a ha).val
  let d := fun n => (pairedOffPoleTailSecondDerivativeTerm B n a ha).val
  have vf : ∀ n, (f n).Valid := fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property
  have vg : ∀ n, (g n).Valid := fun n => (pairedOffPoleTailDerivativeTerm B n a ha).property
  have vd : ∀ n, (d n).Valid := fun n => (pairedOffPoleTailSecondDerivativeTerm B n a ha).property
  let p := fun N => SeriesLimitLaws.remainder (ScalarSeries.block f 0 (N+1))
    (ScalarSeries.block g 0 (N+1)) (ScalarSeries.block d 0 (N+1)) (sub z.val a.val)
  have vp : ∀ N, (p N).Valid := fun N => SeriesLimitLaws.remainder_valid _ _ _ _
    (ScalarSeries.block_valid f vf 0 (N+1)) (ScalarSeries.block_valid g vg 0 (N+1))
    (ScalarSeries.block_valid d vd 0 (N+1)) (sub_valid z.property a.property)
  let e := fun N => (pairedOffPoleTailDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹
  let v := fun N => (pairedOffPoleTailSecondDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹
  let s := fun N => e N+e N+(2*H)*v N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _
      (pairedReciprocalTail_shrinks (pairedOffPoleTailDerivativeConstant B))
      (pairedReciprocalTail_shrinks (pairedOffPoleTailDerivativeConstant B)))
    (SeriesLimitLaws.shrinks_scale _
      (pairedReciprocalTail_shrinks (pairedOffPoleTailSecondDerivativeConstant B))
      (2*H) (Rat.mul_nonneg (by decide +kernel) hH))
  apply SeriesLimitLaws.small_of_prefix_bound _
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedOffPoleTailDerivativeValue B z hz).property
      (pairedOffPoleTailDerivativeValue B a ha).property
      (pairedOffPoleTailSecondDerivativeValue B a ha).property (sub_valid z.property a.property))
    p vp _ s hs
  · intro N
    have hv : 0≤v N := Rat.mul_nonneg Rat.natCast_nonneg
      (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
    have hb := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _
      (pairedOffPoleTailDerivativeValue B z hz).property
      (pairedOffPoleTailDerivativeValue B a ha).property
      (pairedOffPoleTailSecondDerivativeValue B a ha).property
      (ScalarSeries.block_valid f vf 0 (N+1)) (ScalarSeries.block_valid g vg 0 (N+1))
      (ScalarSeries.block_valid d vd 0 (N+1)) (sub_valid z.property a.property)
      (e N) (e N) (v N) H hv hH
      (pairedOffPoleTailDerivativeValue_close B z hz N)
      (pairedOffPoleTailDerivativeValue_close B a ha N)
      (pairedOffPoleTailSecondDerivativeValue_close B a ha N) hd
    exact hb.mono (by dsimp only [s]; grind only)
  · intro N
    have he := finiteRemainderSum f g d vf vg vd _ (sub_valid z.property a.property) 0 (N+1)
    exact Small.congr
      (ScalarSeries.block_valid _ (fun n => SeriesLimitLaws.remainder_valid _ _ _ _
        (vf n) (vg n) (vd n) (sub_valid z.property a.property)) 0 (N+1))
      (vp N) he (pairedOffPoleTailDerivativeRemainder_prefix_bound B (N+1) a z ha hz H hH hd)

def pairedOffPoleTailDerivativeMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedOffPoleTailDerivativeMap B).domain a) :
    HasDerivativeAt (pairedOffPoleTailDerivativeMap B) a ha
      (pairedOffPoleTailSecondDerivativeValue B a ha) where
  delta eps := divideRadius eps ⟨2*(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)+1,by
    have hc : 0≤(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat) := Rat.natCast_nonneg
    grind only⟩
  estimate eps H z hz hH hd := by
    have hb := pairedOffPoleTailDerivative_sum_remainder_bound B a z ha hz H.val (Rat.le_of_lt H.property) hd
    apply hb.mono
    have hc : 0≤(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat) := Rat.natCast_nonneg
    have hden : 0≤2*(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)+1 := by grind only
    have hm := Rat.mul_le_mul_of_nonneg_left hH hden
    rw [divideRadius_identity eps ⟨2*(pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)+1,by grind only⟩] at hm
    have hH0 := Rat.le_of_lt H.property
    have hquad := Rat.mul_le_mul_of_nonneg_right hm hH0
    have hH2 := Rat.mul_nonneg hH0 hH0
    grind only

noncomputable def pairedOffPoleTailDerivativeMap_holomorphic (B : Nat) :
    Holomorphic (pairedOffPoleTailDerivativeMap B) where
  openDomain := ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
  derivative := pairedOffPoleTailSecondDerivativeValue B
  atPoint := pairedOffPoleTailDerivativeMap_hasDerivativeAt B
  derivative_congr z w hz hw he := pairedOffPoleTailSecondDerivativeValue_congr B z w hz hw he
  continuousDerivative := pairedOffPoleTailSecondDerivativeMap_continuous B

end ComputableAnalysis.ModularForms
