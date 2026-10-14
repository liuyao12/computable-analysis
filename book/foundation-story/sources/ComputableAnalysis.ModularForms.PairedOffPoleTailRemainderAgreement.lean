import ComputableAnalysis.ModularForms.PairedOffPoleTailRemainderLimit

/-! Exact actual infinite-tail remainder agreement on the full interior disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def offPoleTailMapPrefix (B : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) (N : Nat) : ComplexRaw :=
  (pairedOffPoleTailPrefixMap B (N+1)).eval z hz |>.val

theorem offPoleTailMapPrefix_valid (B : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) (N : Nat) :
    (offPoleTailMapPrefix B z hz N).Valid := ((pairedOffPoleTailPrefixMap B (N+1)).eval z hz).property

theorem offPoleTailMapPrefix_close (B : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) (N : Nat) :
    Small (sub (pairedTailValue z B (LocalODE.interior_bound _ z hz)) (offPoleTailMapPrefix B z hz N))
      (((16*B:Nat):Rat)*((N+1:Nat):Rat)⁻¹) := pairedTailValue_close z B (LocalODE.interior_bound _ z hz) N

theorem pairedOffPoleTailRemainder_identity (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedOffPoleTailRemainderValue B a z ha hz H).Equiv
      (SeriesLimitLaws.remainder
        (pairedTailValue z B (LocalODE.interior_bound _ z hz))
        (pairedTailValue a B (LocalODE.interior_bound _ a ha))
        ((pairedOffPoleTailDerivativeValue B a ha).val) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).property) 0 (N+1)
  let e := fun N => ((16*B:Nat):Rat)*((N+1:Nat):Rat)⁻¹
  let d := fun N => (pairedOffPoleTailDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks (16*B)) (pairedReciprocalTail_shrinks (16*B)))
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks (pairedOffPoleTailDerivativeConstant B)) (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  have rn (N : Nat) : 0≤pairedOffPoleTailRemainderRate B H N := by
    unfold pairedOffPoleTailRemainderRate
    have hi : (0:Rat)≤((N+1:Nat):Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega)))
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (pairedOffPoleTailRemainderCoefficient_nonneg B) hi) hH) hH
  have vF := pairedTailValue_valid z B (LocalODE.interior_bound _ z hz)
  have vG := pairedTailValue_valid a B (LocalODE.interior_bound _ a ha)
  have vD := (pairedOffPoleTailDerivativeValue B a ha).property
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp (fun N => pairedOffPoleTailRemainderRate B H N+s N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedOffPoleTailRemainderRate_shrinks B H) hs)
    _ _ (pairedOffPoleTailRemainderValue_valid B a z ha hz H hH hd) vR
  · intro N
    exact (pairedOffPoleTailRemainderValue_close B a z ha hz H hH hd N).mono
      (by have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedOffPoleTailDerivativeTerm B n a ha).val) 0 (N+1)
    have vdp : dp.Valid := ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailDerivativeTerm B n a ha).property) 0 (N+1)
    have hb := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (offPoleTailMapPrefix_valid B z hz N) (offPoleTailMapPrefix_valid B a ha N) vdp vX
      (e N) (e N) (d N) H (dn N) hH (offPoleTailMapPrefix_close B z hz N)
      (offPoleTailMapPrefix_close B a ha N) (pairedOffPoleTailDerivativeValue_close B a ha N) hd
    have he := pairedOffPoleTailRemainderPrefix_identity B 0 (N+1) a z ha hz
    have vp := SeriesLimitLaws.remainder_valid _ _ _ _ (offPoleTailMapPrefix_valid B z hz N)
      (offPoleTailMapPrefix_valid B a ha N) vdp vX
    exact (Small.congr (sub_valid vR vp) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm he)) hb).mono
      (by have := rn N; dsimp [s]; grind only)

theorem pairedOffPoleTail_sum_remainder_bound (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder
      (pairedTailValue z B (LocalODE.interior_bound _ z hz))
      (pairedTailValue a B (LocalODE.interior_bound _ a ha))
      ((pairedOffPoleTailDerivativeValue B a ha).val) (sub z.val a.val)) (2*pairedOffPoleTailRemainderCoefficient B*H*H) :=
  Small.congr (pairedOffPoleTailRemainderValue_valid B a z ha hz H hH hd)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedTailValue_valid z B (LocalODE.interior_bound _ z hz))
      (pairedTailValue_valid a B (LocalODE.interior_bound _ a ha))
      ((pairedOffPoleTailDerivativeValue B a ha).property) (sub_valid z.property a.property))
    (pairedOffPoleTailRemainder_identity B a z ha hz H hH hd)
    (pairedOffPoleTailRemainderValue_bound B a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
