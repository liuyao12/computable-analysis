import ComputableAnalysis.ModularForms.PairedRegularDivisionDifference
import ComputableAnalysis.ModularForms.LatticeBasisCauchy163

/-! Continuous actual regular-division sums through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularDivisionTerm_difference_square_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedRegularDivisionTerm z hz n).val (pairedRegularDivisionTerm a ha n).val)
      (128*reciprocalSquare (n+1)*H) := by
  apply (pairedRegularDivisionTerm_difference_bound a z ha hz H hH hd n).mono
  have hr := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have h := Rat.mul_le_mul_of_nonneg_left hr
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤128 by decide) hH) hc)
  grind only

private theorem divisionContinuitySquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem divisionContinuitySquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [divisionContinuitySquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedRegularDivisionPrefix_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (k : Nat) :
    Small (sub (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 k)
      (ScalarSeries.block (fun n => (pairedRegularDivisionTerm a ha n).val) 0 k)) (256*H) := by
  have hb (k : Nat) :
      Small (sub (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedRegularDivisionTerm a ha n).val) 0 k))
        (128*reciprocalSquareBlock 0 k*H) := by
    induction k with
    | zero =>
      have hs := Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
        (equiv_symm (add_neg_equiv zero (ofQComplex_valid _))) (Small.zero (show (0:Rat)≤0 by decide))
      exact hs.mono (by change (0:Rat)≤128*0*H; simp only [Rat.mul_zero,Rat.zero_mul]; decide)
    | succ k ih =>
      have ht := pairedRegularDivisionTerm_difference_square_bound a z ha hz H hH hd k
      have h := (LocalODE.small_add ih ht).mono
        (show 128*reciprocalSquareBlock 0 k*H+128*reciprocalSquare (k+1)*H≤
          128*reciprocalSquareBlock 0 (k+1)*H by rw [reciprocalSquareBlock]; simp only [Nat.zero_add]; grind only)
      have he := SeriesLimitLaws.addition_difference
        (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedRegularDivisionTerm a ha n).val) 0 k)
        (pairedRegularDivisionTerm z hz k).val (pairedRegularDivisionTerm a ha k).val
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 k)
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm a ha n).property) 0 k)
        (pairedRegularDivisionTerm z hz k).property (pairedRegularDivisionTerm a ha k).property
      simp only [ScalarSeries.block.eq_2,Nat.zero_add]
      exact Small.congr
        (add_valid (sub_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 k)
          (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm a ha n).property) 0 k))
          (sub_valid (pairedRegularDivisionTerm z hz k).property (pairedRegularDivisionTerm a ha k).property))
        (sub_valid
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 k)
            (pairedRegularDivisionTerm z hz k).property)
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm a ha n).property) 0 k)
            (pairedRegularDivisionTerm a ha k).property))
        (equiv_symm he) h
  apply (hb k).mono
  have hc := Rat.mul_le_mul_of_nonneg_left (divisionContinuitySquareBlock_zero_bound k)
    (Rat.mul_nonneg (show (0:Rat)≤128 by decide) hH)
  grind only

theorem pairedRegularDivisionValue_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedRegularDivisionValue z hz) (pairedRegularDivisionValue a ha)) (256*H) := by
  let p := fun N => sub
    (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 (N+1))
    (ScalarSeries.block (fun n => (pairedRegularDivisionTerm a ha n).val) 0 (N+1))
  have hp (N : Nat) : (p N).Valid := sub_valid
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 (N+1))
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm a ha n).property) 0 (N+1))
  let d := fun N => ((8:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (pairedRegularDivisionValue_valid z hz) (pairedRegularDivisionValue_valid a ha))
    p hp (256*H) (fun N => d N+d N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 8) (pairedReciprocalTail_shrinks 8))
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      (pairedRegularDivisionValue_valid z hz) (pairedRegularDivisionValue_valid a ha)
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm a ha n).property) 0 (N+1))
      (d N) (d N) (pairedRegularDivisionValue_close z hz N) (pairedRegularDivisionValue_close a ha N)
  · intro N
    exact pairedRegularDivisionPrefix_difference_bound a z ha hz H hH hd (N+1)

def pairedRegularDivisionMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval z hz := ⟨pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz),
    pairedRegularDivisionValue_valid z (LocalODE.interior_bound _ z hz)⟩
  domain_congr z w he := by
    constructor
    · rintro ⟨r,hr,hrq,hs⟩; exact ⟨r,hr,hrq,Small.congr z.property w.property he hs⟩
    · rintro ⟨r,hr,hrq,hs⟩; exact ⟨r,hr,hrq,Small.congr w.property z.property (equiv_symm he) hs⟩
  eval_congr z w hz hw he := pairedRegularDivisionValue_congr z w
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw) he

def pairedRegularDivisionMap_continuous : ContinuousOn pairedRegularDivisionMap.domain pairedRegularDivisionMap.eval where
  delta _ _ eps := divideRadius eps ⟨256,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := pairedRegularDivisionValue_difference_bound a z
      (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ z hz)
      (divideRadius eps ⟨256,by decide +kernel⟩).val
      (Rat.le_of_lt (divideRadius eps ⟨256,by decide +kernel⟩).property) hd
    rw [divideRadius_identity eps ⟨256,by decide +kernel⟩] at h
    exact h

end ComputableAnalysis.ModularForms
