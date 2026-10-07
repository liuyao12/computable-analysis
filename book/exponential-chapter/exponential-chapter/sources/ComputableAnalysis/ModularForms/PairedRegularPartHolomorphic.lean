import ComputableAnalysis.ModularForms.PairedRegularPartDerivative

/-! Continuous derivative and holomorphic extension of the regular part through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedSmallDiskDerivativeTerm_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedSmallDiskDerivativeTerm z hz n).val (pairedSmallDiskDerivativeTerm a ha n).val)
      (131072*reciprocalSquare (n+1)*H) := by
  let M := 16*(1/((n+1:Nat):Rat))
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hM : 0≤M := by
    dsimp [M]; rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  have hb (plus : Bool) :
      Small (sub (ReciprocalDifference.derivative (smallDiskShift z n plus) (smallDiskShift_nonzero z hz n plus)).val
        (ReciprocalDifference.derivative (smallDiskShift a n plus) (smallDiskShift_nonzero a ha n plus)).val)
        (16*M*M*M*H) := by
    have hs := Small.congr (sub_valid z.property a.property)
      (sub_valid (smallDiskShift z n plus).property (smallDiskShift a n plus).property)
      (equiv_symm (smallDiskShift_displacement n plus a z)) hd
    exact pairedUniformReciprocalDerivative_difference _ _ _ _ M H hM hH
      (smallDiskShiftInverse_bound a ha n plus) (smallDiskShiftInverse_bound z hz n plus) hs
  have hs := (LocalODE.small_add (hb false) (hb true)).mono
    (show (16:Rat)*M*M*M*H+16*M*M*M*H≤32*M*M*M*H by grind only)
  have he := SeriesLimitLaws.addition_difference
    (ReciprocalDifference.derivative (smallDiskShift z n false) (smallDiskShift_nonzero z hz n false)).val
    (ReciprocalDifference.derivative (smallDiskShift a n false) (smallDiskShift_nonzero a ha n false)).val
    (ReciprocalDifference.derivative (smallDiskShift z n true) (smallDiskShift_nonzero z hz n true)).val
    (ReciprocalDifference.derivative (smallDiskShift a n true) (smallDiskShift_nonzero a ha n true)).val
    (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property
    (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property
  have hv := Small.congr
    (add_valid (sub_valid (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property)
      (sub_valid (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property))
    (sub_valid (pairedSmallDiskDerivativeTerm z hz n).property (pairedSmallDiskDerivativeTerm a ha n).property)
    (equiv_symm he) hs
  apply hv.mono
  have hc : 0≤(131072:Rat)*H := Rat.mul_nonneg (by decide) hH
  calc
    _ = (131072*H)*(((n+1:Nat):Rat)⁻¹*((n+1:Nat):Rat)⁻¹*((n+1:Nat):Rat)⁻¹) := by
      dsimp [M]; rw [Rat.div_def,Rat.one_mul]; grind only
    _ ≤ (131072*H)*reciprocalSquare (n+1) :=
      Rat.mul_le_mul_of_nonneg_left (pairedDerivative_inverseCube_le_square (n+1) (by omega)) hc
    _ = _ := by grind only

private theorem smallDiskContinuitySquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem smallDiskContinuitySquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [smallDiskContinuitySquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedSmallDiskDerivativePrefix_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (k : Nat) :
    Small (sub (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm z hz n).val) 0 k)
      (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a ha n).val) 0 k)) (262144*H) := by
  have hb (k : Nat) :
      Small (sub (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a ha n).val) 0 k))
        (131072*reciprocalSquareBlock 0 k*H) := by
    induction k with
    | zero =>
      have hs := Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
        (equiv_symm (add_neg_equiv zero (ofQComplex_valid _))) (Small.zero (show (0:Rat)≤0 by decide))
      exact hs.mono (by change (0:Rat)≤131072*0*H; simp only [Rat.mul_zero,Rat.zero_mul]; decide)
    | succ k ih =>
      have ht := pairedSmallDiskDerivativeTerm_difference_bound a z ha hz H hH hd k
      have h := (LocalODE.small_add ih ht).mono
        (show 131072*reciprocalSquareBlock 0 k*H+131072*reciprocalSquare (k+1)*H≤
          131072*reciprocalSquareBlock 0 (k+1)*H by rw [reciprocalSquareBlock]; simp only [Nat.zero_add]; grind only)
      have he := SeriesLimitLaws.addition_difference
        (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a ha n).val) 0 k)
        (pairedSmallDiskDerivativeTerm z hz k).val (pairedSmallDiskDerivativeTerm a ha k).val
        (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 0 k)
        (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a ha n).property) 0 k)
        (pairedSmallDiskDerivativeTerm z hz k).property (pairedSmallDiskDerivativeTerm a ha k).property
      simp only [ScalarSeries.block.eq_2,Nat.zero_add]
      exact Small.congr
        (add_valid (sub_valid (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 0 k)
          (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a ha n).property) 0 k))
          (sub_valid (pairedSmallDiskDerivativeTerm z hz k).property (pairedSmallDiskDerivativeTerm a ha k).property))
        (sub_valid
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 0 k)
            (pairedSmallDiskDerivativeTerm z hz k).property)
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a ha n).property) 0 k)
            (pairedSmallDiskDerivativeTerm a ha k).property))
        (equiv_symm he) h
  apply (hb k).mono
  have hc := Rat.mul_le_mul_of_nonneg_left (smallDiskContinuitySquareBlock_zero_bound k)
    (Rat.mul_nonneg (show (0:Rat)≤131072 by decide) hH)
  grind only

theorem pairedSmallDiskDerivativeValue_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedSmallDiskDerivativeValue z hz) (pairedSmallDiskDerivativeValue a ha)) (262144*H) := by
  let p := fun N => sub
    (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm z hz n).val) 0 (N+1))
    (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a ha n).val) 0 (N+1))
  have hp (N : Nat) : (p N).Valid := sub_valid
    (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 0 (N+1))
    (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a ha n).property) 0 (N+1))
  let d := fun N => ((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (pairedSmallDiskDerivativeValue_valid z hz) (pairedSmallDiskDerivativeValue_valid a ha))
    p hp (262144*H) (fun N => d N+d N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 1024) (pairedReciprocalTail_shrinks 1024))
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      (pairedSmallDiskDerivativeValue_valid z hz) (pairedSmallDiskDerivativeValue_valid a ha)
      (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a ha n).property) 0 (N+1))
      (d N) (d N) (pairedSmallDiskDerivativeValue_close z hz N) (pairedSmallDiskDerivativeValue_close a ha N)
  · intro N
    exact pairedSmallDiskDerivativePrefix_difference_bound a z ha hz H hH hd (N+1)

def pairedRegularPartDerivative_continuous :
    ContinuousOn pairedRegularPartMap.domain pairedRegularPartDerivative where
  delta _ _ eps := divideRadius eps ⟨262144,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := pairedSmallDiskDerivativeValue_difference_bound a z
      (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ z hz)
      (divideRadius eps ⟨262144,by decide +kernel⟩).val
      (Rat.le_of_lt (divideRadius eps ⟨262144,by decide +kernel⟩).property) hd
    rw [divideRadius_identity eps ⟨262144,by decide +kernel⟩] at h
    exact h

def pairedRegularPartMap_holomorphic : DomainFunctions.Holomorphic pairedRegularPartMap where
  openDomain := ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  derivative := pairedRegularPartDerivative
  atPoint := pairedRegularPartMap_hasDerivativeAt
  derivative_congr := pairedRegularPartDerivative_congr
  continuousDerivative := pairedRegularPartDerivative_continuous

end ComputableAnalysis.ModularForms
