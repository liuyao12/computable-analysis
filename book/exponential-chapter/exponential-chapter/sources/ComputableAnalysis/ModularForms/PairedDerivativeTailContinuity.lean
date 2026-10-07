import ComputableAnalysis.ModularForms.PairedDerivativeDifference

/-! Uniform Lipschitz bounds and continuity for the actual reciprocal derivative tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem derivativeSquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem derivativeSquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [derivativeSquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedDerivativeTailPrefix_difference_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (k : Nat) :
    Small (sub (ScalarSeries.block (fun n => (pairedDerivativeTailTerm z hz B n).val) 0 k)
      (ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 k)) (262144*H) := by
  have hb (k : Nat) :
      Small (sub (ScalarSeries.block (fun n => (pairedDerivativeTailTerm z hz B n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 k))
        (131072*reciprocalSquareBlock 0 k*H) := by
    induction k with
    | zero =>
      have hs := Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
        (equiv_symm (add_neg_equiv zero (ofQComplex_valid _))) (Small.zero (show (0:Rat)≤0 by decide))
      exact hs.mono (by change (0:Rat)≤131072*0*H; simp only [Rat.mul_zero,Rat.zero_mul]; decide)
    | succ k ih =>
      have ht := pairedDerivativeTailTerm_difference_bound a z ha hz B hA hZ H hH hd k
      have h := (LocalODE.small_add ih ht).mono
        (show 131072*reciprocalSquareBlock 0 k*H+131072*reciprocalSquare (k+1)*H≤
          131072*reciprocalSquareBlock 0 (k+1)*H by rw [reciprocalSquareBlock]; simp only [Nat.zero_add]; grind only)
      have he := SeriesLimitLaws.addition_difference
        (ScalarSeries.block (fun n => (pairedDerivativeTailTerm z hz B n).val) 0 k)
        (ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 k)
        (pairedDerivativeTailTerm z hz B k).val (pairedDerivativeTailTerm a ha B k).val
        (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 k)
        (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 k)
        (pairedDerivativeTailTerm z hz B k).property (pairedDerivativeTailTerm a ha B k).property
      simp only [ScalarSeries.block.eq_2,Nat.zero_add]
      exact Small.congr
        (add_valid (sub_valid (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 k)
          (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 k))
          (sub_valid (pairedDerivativeTailTerm z hz B k).property (pairedDerivativeTailTerm a ha B k).property))
        (sub_valid
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 k)
            (pairedDerivativeTailTerm z hz B k).property)
          (add_valid (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 k)
            (pairedDerivativeTailTerm a ha B k).property))
        (equiv_symm he) h
  apply (hb k).mono
  have hc := Rat.mul_le_mul_of_nonneg_left (derivativeSquareBlock_zero_bound k)
    (Rat.mul_nonneg (show (0:Rat)≤131072 by decide) hH)
  grind only

theorem pairedDerivativeTailValue_difference_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedDerivativeTailValue z hz B) (pairedDerivativeTailValue a ha B)) (262144*H) := by
  let p := fun N => sub
    (ScalarSeries.block (fun n => (pairedDerivativeTailTerm z hz B n).val) 0 (N+1))
    (ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 (N+1))
  have hp (N : Nat) : (p N).Valid := sub_valid
    (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 (N+1))
    (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 (N+1))
  let d := fun N => ((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (pairedDerivativeTailValue_valid z hz B hZ) (pairedDerivativeTailValue_valid a ha B hA))
    p hp (262144*H) (fun N => d N+d N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 1024) (pairedReciprocalTail_shrinks 1024))
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      (pairedDerivativeTailValue_valid z hz B hZ) (pairedDerivativeTailValue_valid a ha B hA)
      (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 (N+1))
      (d N) (d N) (pairedDerivativeTailValue_close z hz B hZ N) (pairedDerivativeTailValue_close a ha B hA N)
  · intro N
    exact pairedDerivativeTailPrefix_difference_bound a z ha hz B hA hZ H hH hd (N+1)

def pairedTailDiskDerivative_continuous (B : Nat) :
    ContinuousOn (pairedTailDiskMap B).domain (pairedTailDiskDerivative B) where
  delta _ _ eps := divideRadius eps ⟨262144,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := pairedDerivativeTailValue_difference_bound a z ha.1 hz.1 B ha.2 hz.2
      (divideRadius eps ⟨262144,by decide +kernel⟩).val
      (Rat.le_of_lt (divideRadius eps ⟨262144,by decide +kernel⟩).property) hd
    rw [divideRadius_identity eps ⟨262144,by decide +kernel⟩] at h
    exact h

end ComputableAnalysis.ModularForms
