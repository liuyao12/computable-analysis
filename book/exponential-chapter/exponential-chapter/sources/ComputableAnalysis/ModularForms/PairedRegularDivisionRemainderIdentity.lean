import ComputableAnalysis.ModularForms.PairedRegularDivisionRemainderLimit

/-! Exact remainder agreement for the actual infinite regular-division sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedDivisionMapPrefix (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedRegularDivisionTermMap n).eval z hz).val) 0 (N+1)

theorem pairedDivisionMapPrefix_valid (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    (pairedDivisionMapPrefix z hz N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedRegularDivisionTermMap n).eval z hz).property) 0 (N+1)

theorem pairedDivisionMapPrefix_close (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    Small (sub (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz)) (pairedDivisionMapPrefix z hz N))
      (8*((N+1:Nat):Rat)⁻¹) := by
  let hq := LocalODE.interior_bound _ z hz
  have he := ScalarSeries.block_congr _ _ (fun n => pairedRegularDivisionTermMap_eval n z hz) 0 (N+1)
  exact Small.congr
    (sub_valid (pairedRegularDivisionValue_valid z hq)
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hq n).property) 0 (N+1)))
    (sub_valid (pairedRegularDivisionValue_valid z hq) (pairedDivisionMapPrefix_valid z hz N))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedRegularDivisionValue_valid z hq)) (equiv_symm he))
    (pairedRegularDivisionValue_close z hq N)

theorem pairedRegularDivisionRemainder_identity (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedRegularDivisionRemainderValue a z ha hz H).Equiv
      (SeriesLimitLaws.remainder
        (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz))
        (pairedRegularDivisionValue a (LocalODE.interior_bound _ a ha))
        (pairedRegularDivisionDerivativeValue a ha) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (pairedRegularDivisionRemainderTerm a z ha hz) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) 0 (N+1)
  let e := fun N => (8:Rat)*((N+1:Nat):Rat)⁻¹
  let d := fun N => (64:Rat)*((N+1:Nat):Rat)⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 8) (pairedReciprocalTail_shrinks 8))
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 64) (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  have rn (N : Nat) : 0≤pairedRegularDivisionRemainderRate H N := by
    unfold pairedRegularDivisionRemainderRate
    have hi : (0:Rat)≤((N+1:Nat):Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega)))
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hi) hH) hH
  have vF := pairedRegularDivisionValue_valid z (LocalODE.interior_bound _ z hz)
  have vG := pairedRegularDivisionValue_valid a (LocalODE.interior_bound _ a ha)
  have vD := pairedRegularDivisionDerivativeValue_valid a ha
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp (fun N => pairedRegularDivisionRemainderRate H N+s N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedRegularDivisionRemainderRate_shrinks H) hs)
    _ _ (pairedRegularDivisionRemainderValue_valid a z ha hz H hH hd) vR
  · intro N
    exact (pairedRegularDivisionRemainderValue_close a z ha hz H hH hd N).mono
      (by have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm a ha n).val) 0 (N+1)
    have vdp : dp.Valid := ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm a ha n).property) 0 (N+1)
    have hb := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (pairedDivisionMapPrefix_valid z hz N) (pairedDivisionMapPrefix_valid a ha N) vdp vX
      (e N) (e N) (d N) H (dn N) hH (pairedDivisionMapPrefix_close z hz N)
      (pairedDivisionMapPrefix_close a ha N) (pairedRegularDivisionDerivativeValue_close a ha N) hd
    have he := pairedRegularDivisionRemainderPrefix_identity 0 (N+1) a z ha hz
    have vp := SeriesLimitLaws.remainder_valid _ _ _ _ (pairedDivisionMapPrefix_valid z hz N)
      (pairedDivisionMapPrefix_valid a ha N) vdp vX
    exact (Small.congr (sub_valid vR vp) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm he)) hb).mono
      (by have := rn N; dsimp [s]; grind only)

theorem pairedRegularDivision_sum_remainder_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder
      (pairedRegularDivisionValue z (LocalODE.interior_bound _ z hz))
      (pairedRegularDivisionValue a (LocalODE.interior_bound _ a ha))
      (pairedRegularDivisionDerivativeValue a ha) (sub z.val a.val)) (4608*H*H) :=
  Small.congr (pairedRegularDivisionRemainderValue_valid a z ha hz H hH hd)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedRegularDivisionValue_valid z (LocalODE.interior_bound _ z hz))
      (pairedRegularDivisionValue_valid a (LocalODE.interior_bound _ a ha))
      (pairedRegularDivisionDerivativeValue_valid a ha) (sub_valid z.property a.property))
    (pairedRegularDivisionRemainder_identity a z ha hz H hH hd)
    (pairedRegularDivisionRemainderValue_bound a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
