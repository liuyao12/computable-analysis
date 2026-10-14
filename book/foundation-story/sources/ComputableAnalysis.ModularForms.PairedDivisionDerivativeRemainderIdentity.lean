import ComputableAnalysis.ModularForms.PairedDivisionDerivativeRemainderLimit

/-! Exact remainder agreement for the actual infinite regular-division sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedDerivativeMapPrefix (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedDivisionDerivativeTermMap n).eval z hz).val) 0 (N+1)

theorem pairedDerivativeMapPrefix_valid (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    (pairedDerivativeMapPrefix z hz N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedDivisionDerivativeTermMap n).eval z hz).property) 0 (N+1)

theorem pairedDerivativeMapPrefix_close (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    Small (sub (pairedRegularDivisionDerivativeValue z hz) (pairedDerivativeMapPrefix z hz N))
      (64*((N+1:Nat):Rat)⁻¹) := by
  let hq := LocalODE.interior_bound _ z hz
  have he := ScalarSeries.block_congr _ _ (fun n => pairedDivisionDerivativeTermMap_eval n z hz) 0 (N+1)
  exact Small.congr
    (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz)
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1)))
    (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz) (pairedDerivativeMapPrefix_valid z hz N))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedRegularDivisionDerivativeValue_valid z hz)) (equiv_symm he))
    (pairedRegularDivisionDerivativeValue_close z hz N)

theorem pairedDivisionDerivativeRemainder_identity (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedDivisionDerivativeRemainderValue a z ha hz H).Equiv
      (SeriesLimitLaws.remainder
        (pairedRegularDivisionDerivativeValue z hz)
        (pairedRegularDivisionDerivativeValue a ha)
        (pairedDivisionSecondDerivativeValue a ha) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (pairedDivisionDerivativeRemainderTerm a z ha hz) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) 0 (N+1)
  let e := fun N => (64:Rat)*((N+1:Nat):Rat)⁻¹
  let d := fun N => (1152:Rat)*((N+1:Nat):Rat)⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (pairedReciprocalTail_shrinks 64) (pairedReciprocalTail_shrinks 64))
    (SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 1152) (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  have rn (N : Nat) : 0≤pairedDivisionDerivativeRemainderRate H N := by
    unfold pairedDivisionDerivativeRemainderRate
    have hi : (0:Rat)≤((N+1:Nat):Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega)))
    exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hi) hH) hH
  have vF := pairedRegularDivisionDerivativeValue_valid z hz
  have vG := pairedRegularDivisionDerivativeValue_valid a ha
  have vD := pairedDivisionSecondDerivativeValue_valid a ha
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp (fun N => pairedDivisionDerivativeRemainderRate H N+s N)
    (RepresentedCauchySum.sum_shrinks _ _ (pairedDivisionDerivativeRemainderRate_shrinks H) hs)
    _ _ (pairedDivisionDerivativeRemainderValue_valid a z ha hz H hH hd) vR
  · intro N
    exact (pairedDivisionDerivativeRemainderValue_close a z ha hz H hH hd N).mono
      (by have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedDivisionSecondDerivativeTerm a ha n).val) 0 (N+1)
    have vdp : dp.Valid := ScalarSeries.block_valid _ (fun n => (pairedDivisionSecondDerivativeTerm a ha n).property) 0 (N+1)
    have hb := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (pairedDerivativeMapPrefix_valid z hz N) (pairedDerivativeMapPrefix_valid a ha N) vdp vX
      (e N) (e N) (d N) H (dn N) hH (pairedDerivativeMapPrefix_close z hz N)
      (pairedDerivativeMapPrefix_close a ha N) (pairedDivisionSecondDerivativeValue_close a ha N) hd
    have he := pairedDivisionDerivativeRemainderPrefix_identity 0 (N+1) a z ha hz
    have vp := SeriesLimitLaws.remainder_valid _ _ _ _ (pairedDerivativeMapPrefix_valid z hz N)
      (pairedDerivativeMapPrefix_valid a ha N) vdp vX
    exact (Small.congr (sub_valid vR vp) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm he)) hb).mono
      (by have := rn N; dsimp [s]; grind only)

theorem pairedDivisionDerivative_sum_remainder_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder
      (pairedRegularDivisionDerivativeValue z hz)
      (pairedRegularDivisionDerivativeValue a ha)
      (pairedDivisionSecondDerivativeValue a ha) (sub z.val a.val)) (122880*H*H) :=
  Small.congr (pairedDivisionDerivativeRemainderValue_valid a z ha hz H hH hd)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedRegularDivisionDerivativeValue_valid z hz)
      (pairedRegularDivisionDerivativeValue_valid a ha)
      (pairedDivisionSecondDerivativeValue_valid a ha) (sub_valid z.property a.property))
    (pairedDivisionDerivativeRemainder_identity a z ha hz H hH hd)
    (pairedDivisionDerivativeRemainderValue_bound a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
