import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! The actual remainder limit equals the remainder of the actual function and derivative tails. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedMapTailPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (B N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedReciprocalTermMap (4*B+n)).eval z hz).val) 0 N

theorem pairedMapTailPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (B N : Nat) :
    (pairedMapTailPrefix z hz B N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedReciprocalTermMap (4*B+n)).eval z hz).property) 0 N

theorem pairedMapTailPrefix_agreement (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    (pairedMapTailPrefix z hz B N).Equiv
      (ScalarSeries.block (fun n => (pairedTailTerm z B hB n).val) 0 N) := by
  apply ScalarSeries.block_congr
  intro n
  have h := equiv_trans ((pairedReciprocalTermMap (4*B+n)).eval z hz).property
    (upperPairedLatticeTerm z hz (4*B+n)).property
    (pairedFullTerm z (upperPairedSeriesDomain z hz) (4*B+n)).property
    (pairedReciprocalTermMap_eval_agreement (4*B+n) z hz)
    (upperPairedLatticeTerm_agreement z hz (4*B+n))
  rw [pairedFullTerm_tail z (upperPairedSeriesDomain z hz) B hB n] at h
  exact h

theorem pairedMapTailPrefix_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedTailValue z B hB) (pairedMapTailPrefix z hz B (N+1)))
      (((16*B:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  Small.congr (sub_valid (pairedTailValue_valid z B hB)
      (ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hB n).property) 0 (N+1)))
    (sub_valid (pairedTailValue_valid z B hB) (pairedMapTailPrefix_valid z hz B (N+1)))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedTailValue_valid z B hB))
      (equiv_symm (pairedMapTailPrefix_agreement z hz B hB (N+1))))
    (pairedTailValue_close z B hB N)

theorem pairedTailRemainder_identity (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedTailRemainder B a z ha hz).Equiv
      (SeriesLimitLaws.remainder (pairedTailValue z B hZ) (pairedTailValue a B hA)
        (pairedDerivativeTailValue a ha B) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 _
  let e := fun N => ((16*B:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  let d := fun N => ((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have he : ShrinksToZero e := pairedReciprocalTail_shrinks (16*B)
  have hdRate : ShrinksToZero d := pairedReciprocalTail_shrinks 1024
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ he he)
    (SeriesLimitLaws.shrinks_scale d hdRate (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  let T := fun N => pairedTailRemainderRate H N+s N
  have hT : ShrinksToZero T := RepresentedCauchySum.sum_shrinks _ _ (pairedTailRemainderRate_shrinks H) hs
  have vF := pairedTailValue_valid z B hZ
  have vG := pairedTailValue_valid a B hA
  have vD := pairedDerivativeTailValue_valid a ha B hA
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp T hT _ _ (pairedTailRemainder_valid B a z ha hz hA hZ) vR
  · intro N
    exact (pairedTailRemainder_close B a z ha hz hA hZ H hH hd N).mono
      (by change pairedTailRemainderRate H N≤pairedTailRemainderRate H N+s N; have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 (N+1)
    have vdp := ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm a ha B n).property) 0 (N+1)
    have h := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (pairedMapTailPrefix_valid z hz B (N+1)) (pairedMapTailPrefix_valid a ha B (N+1)) vdp vX
      (e N) (e N) (d N) H (dn N) hH (pairedMapTailPrefix_close z hz B hZ N)
      (pairedMapTailPrefix_close a ha B hA N) (pairedDerivativeTailValue_close a ha B hA N) hd
    have hi := pairedTailRemainderPrefix_identity B (N+1) a z ha hz
    have vq := SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedMapTailPrefix_valid z hz B (N+1)) (pairedMapTailPrefix_valid a ha B (N+1)) vdp vX
    have h1 := Small.congr (sub_valid vR vq) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm hi)) h
    exact h1.mono (by
      change e N+e N+2*d N*H≤pairedTailRemainderRate H N+(e N+e N+(2*H)*d N)
      have := pairedTailRemainderRate_nonnegative H hH N
      grind only)

end ComputableAnalysis.ModularForms
