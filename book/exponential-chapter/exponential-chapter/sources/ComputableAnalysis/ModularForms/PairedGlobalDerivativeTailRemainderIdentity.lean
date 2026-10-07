import ComputableAnalysis.ModularForms.PairedGlobalDerivativeTailPrefixes
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTail

/-! Exact analytic remainder agreement for the global derivative tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedGlobalDerivativeTailRemainder_identity (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedGlobalRemainderTailValue a z ha hz B H).Equiv
      (SeriesLimitLaws.remainder
        (pairedDerivativeTailValue z hz B)
        (pairedDerivativeTailValue a ha B)
        (pairedGlobalSecondDerivativeTailValue a ha B) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (pairedGlobalRemainderTailTerm a z ha hz B) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) 0 (N+1)
  let e := fun N => (1024:Rat)*((N+1:Nat):Rat)⁻¹
  let d := fun N => (65536:Rat)*((N+1:Nat):Rat)⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 1024) (pairedReciprocalTail_shrinks 1024))
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 65536) (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  have rn (N : Nat) : 0≤pairedGlobalRemainderTailRate H N := by
    unfold pairedGlobalRemainderTailRate
    have hi : (0:Rat)≤((N+1:Nat):Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega)))
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hi) hH) hH
  have vF := pairedDerivativeTailValue_valid z hz B hBz
  have vG := pairedDerivativeTailValue_valid a ha B hBa
  have vD := pairedGlobalSecondDerivativeTailValue_valid a ha B hBa
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp (fun N => pairedGlobalRemainderTailRate H N+s N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedGlobalRemainderTailRate_shrinks H) hs)
    _ _ (pairedGlobalRemainderTailValue_valid a z ha hz B hBa hBz H hH hd) vR
  · intro N
    exact (pairedGlobalRemainderTailValue_close a z ha hz B hBa hBz H hH hd N).mono
      (by have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTailTerm a ha B n).val) 0 (N+1)
    have vdp : dp.Valid := ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTailTerm a ha B n).property) 0 (N+1)
    have hb := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (pairedGlobalDerivativeTailMapPrefix_valid z hz B N) (pairedGlobalDerivativeTailMapPrefix_valid a ha B N) vdp vX
      (e N) (e N) (d N) H (dn N) hH (pairedGlobalDerivativeTailMapPrefix_close z hz B hBz N)
      (pairedGlobalDerivativeTailMapPrefix_close a ha B hBa N) (pairedGlobalSecondDerivativeTailValue_close a ha B hBa N) hd
    have he := pairedGlobalDerivativeRemainderTailPrefix_identity B 0 (N+1) a z ha hz
    have vp := SeriesLimitLaws.remainder_valid _ _ _ _ (pairedGlobalDerivativeTailMapPrefix_valid z hz B N)
      (pairedGlobalDerivativeTailMapPrefix_valid a ha B N) vdp vX
    exact (Small.congr (sub_valid vR vp) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm he)) hb).mono
      (by have := rn N; dsimp [s]; grind only)

theorem pairedGlobalDerivativeTail_sum_remainder_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder
      (pairedDerivativeTailValue z hz B)
      (pairedDerivativeTailValue a ha B)
      (pairedGlobalSecondDerivativeTailValue a ha B) (sub z.val a.val)) (25165824*H*H) :=
  Small.congr (pairedGlobalRemainderTailValue_valid a z ha hz B hBa hBz H hH hd)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedDerivativeTailValue_valid z hz B hBz)
      (pairedDerivativeTailValue_valid a ha B hBa)
      (pairedGlobalSecondDerivativeTailValue_valid a ha B hBa) (sub_valid z.property a.property))
    (pairedGlobalDerivativeTailRemainder_identity a z ha hz B hBa hBz H hH hd)
    (pairedGlobalRemainderTailValue_bound a z ha hz B hBa hBz H hH hd)

end ComputableAnalysis.ModularForms
