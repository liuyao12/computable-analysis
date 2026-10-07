import ComputableAnalysis.ModularForms.PairedRegularDivisionDerivativeDifference

/-! Continuous derivative and holomorphic actual regular division. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem divisionDerivativeSquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem divisionDerivativeSquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [divisionDerivativeSquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedRegularDivisionDerivativePrefix_difference_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (k : Nat) :
    Small (sub (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 k)
      (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm a ha n).val) 0 k)) (4608*H) := by
  have hb (k : Nat) :
      Small (sub (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm a ha n).val) 0 k))
        (2304*reciprocalSquareBlock 0 k*H) := by
    induction k with
    | zero =>
      have hs := Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
        (equiv_symm (add_neg_equiv zero (ofQComplex_valid _))) (Small.zero (show (0:Rat)≤0 by decide))
      exact hs.mono (by change (0:Rat)≤2304*0*H; simp only [Rat.mul_zero,Rat.zero_mul]; decide)
    | succ k ih =>
      have ht := pairedRegularDivisionDerivativeTerm_difference_bound a z ha hz H hH hd k
      have h := (LocalODE.small_add ih ht).mono
        (show 2304*reciprocalSquareBlock 0 k*H+2304*reciprocalSquare (k+1)*H≤
          2304*reciprocalSquareBlock 0 (k+1)*H by rw [reciprocalSquareBlock]; simp only [Nat.zero_add]; grind only)
      have he := SeriesLimitLaws.addition_difference
        (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm a ha n).val) 0 k)
        (pairedRegularDivisionDerivativeTerm z hz k).val (pairedRegularDivisionDerivativeTerm a ha k).val
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 k)
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 k)
        (pairedRegularDivisionDerivativeTerm z hz k).property (pairedRegularDivisionDerivativeTerm a ha k).property
      simp only [ScalarSeries.block.eq_2,Nat.zero_add]
      exact Small.congr
        (add_valid (sub_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 k)
          (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 k))
          (sub_valid (pairedRegularDivisionDerivativeTerm z hz k).property (pairedRegularDivisionDerivativeTerm a ha k).property))
        (sub_valid
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 k)
            (pairedRegularDivisionDerivativeTerm z hz k).property)
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 k)
            (pairedRegularDivisionDerivativeTerm a ha k).property))
        (equiv_symm he) h
  apply (hb k).mono
  have hc := Rat.mul_le_mul_of_nonneg_left (divisionDerivativeSquareBlock_zero_bound k)
    (Rat.mul_nonneg (show (0:Rat)≤2304 by decide) hH)
  grind only

theorem pairedRegularDivisionDerivativeValue_difference_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedRegularDivisionDerivativeValue z hz) (pairedRegularDivisionDerivativeValue a ha)) (4608*H) := by
  let p := fun N => sub
    (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 (N+1))
    (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm a ha n).val) 0 (N+1))
  have hp (N : Nat) : (p N).Valid := sub_valid
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 (N+1))
  let d := fun N => ((64:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz) (pairedRegularDivisionDerivativeValue_valid a ha))
    p hp (4608*H) (fun N => d N+d N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 64) (pairedReciprocalTail_shrinks 64))
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      (pairedRegularDivisionDerivativeValue_valid z hz) (pairedRegularDivisionDerivativeValue_valid a ha)
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 (N+1))
      (d N) (d N) (pairedRegularDivisionDerivativeValue_close z hz N) (pairedRegularDivisionDerivativeValue_close a ha N)
  · intro N
    exact pairedRegularDivisionDerivativePrefix_difference_bound a z ha hz H hH hd (N+1)

def pairedRegularDivisionDerivative_continuous :
    ContinuousOn pairedRegularDivisionMap.domain pairedRegularDivisionDerivative where
  delta _ _ eps := divideRadius eps ⟨4608,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := pairedRegularDivisionDerivativeValue_difference_bound a z ha hz
      (divideRadius eps ⟨4608,by decide +kernel⟩).val
      (Rat.le_of_lt (divideRadius eps ⟨4608,by decide +kernel⟩).property) hd
    rw [divideRadius_identity eps ⟨4608,by decide +kernel⟩] at h
    exact h

def pairedRegularDivisionMap_holomorphic : Holomorphic pairedRegularDivisionMap where
  openDomain := ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  derivative := pairedRegularDivisionDerivative
  atPoint := pairedRegularDivisionMap_hasDerivativeAt
  derivative_congr := pairedRegularDivisionDerivative_congr
  continuousDerivative := pairedRegularDivisionDerivative_continuous

end ComputableAnalysis.ModularForms
