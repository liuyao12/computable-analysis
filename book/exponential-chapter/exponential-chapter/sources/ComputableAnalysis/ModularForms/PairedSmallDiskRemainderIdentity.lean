import ComputableAnalysis.ModularForms.PairedSmallDiskRemainderAgreement
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Exact infinite-sum remainder identity for the regular part through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedSmallDiskMapPrefix (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedSmallDiskTermMap n).eval z hz).val) 0 N

theorem pairedSmallDiskMapPrefix_valid (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    (pairedSmallDiskMapPrefix z hz N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedSmallDiskTermMap n).eval z hz).property) 0 N

theorem pairedSmallDiskMapPrefix_agreement (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    (pairedSmallDiskMapPrefix z hz N).Equiv
      (ScalarSeries.block (fun n => (pairedFullTerm z
        (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
          (LocalODE.interior_bound _ z hz)) n).val) 0 N) :=
  ScalarSeries.block_congr _ _ (fun n => pairedSmallDiskTermMap_eval n z hz) 0 N

theorem pairedSmallDiskMapPrefix_close (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    Small (sub (pairedRegularPart z (LocalODE.interior_bound _ z hz))
      (pairedSmallDiskMapPrefix z hz (N+5)))
      (((16:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  let hq := LocalODE.interior_bound (1/4) z hz
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hq
  have h1 : Small z.val ((1:Nat):Rat) := hq.mono (by decide +kernel)
  have he := pairedSeriesValue_agrees z hd 1 h1
  have hi := pairedSmallDiskMapPrefix_agreement z hz (N+5)
  have h := pairedFullValue_close z hd 1 h1 N
  rw [show 4*1+(N+1)=N+5 by omega] at h
  exact Small.congr
    (sub_valid (pairedFullValue_valid z hd 1 h1)
      (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 (N+5)))
    (sub_valid (pairedRegularPart_valid z hq) (pairedSmallDiskMapPrefix_valid z hz (N+5)))
    (FunctionTheory.sub_congr (equiv_symm he) (equiv_symm hi)) h

theorem pairedSmallDiskRemainderPrefix_identity (N : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) :
    (ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 N).Equiv
      (SeriesLimitLaws.remainder (pairedSmallDiskMapPrefix z hz N) (pairedSmallDiskMapPrefix a ha N)
        (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a
          (LocalODE.interior_bound _ a ha) n).val) 0 N) (sub z.val a.val)) :=
  finiteRemainderSum _ _ _
    (fun n => ((pairedSmallDiskTermMap n).eval z hz).property)
    (fun n => ((pairedSmallDiskTermMap n).eval a ha).property)
    (fun n => (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n).property)
    _ (sub_valid z.property a.property) 0 N

theorem pairedSmallDiskRemainder_identity (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedSmallDiskRemainder a z ha hz).Equiv
      (SeriesLimitLaws.remainder (pairedRegularPart z (LocalODE.interior_bound _ z hz)) (pairedRegularPart a (LocalODE.interior_bound _ a ha))
        (pairedSmallDiskDerivativeValue a (LocalODE.interior_bound _ a ha)) (sub z.val a.val)) := by
  let p := fun N => ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (N+5)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 _
  let e := fun N => ((16:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  let d := fun N => ((1024:Nat):Rat)*(((N+4+1:Nat):Rat))⁻¹
  let s := fun N => e N+e N+(2*H)*d N
  have he : ShrinksToZero e := pairedReciprocalTail_shrinks 16
  have hdRate : ShrinksToZero d := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks 1024) 4
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ he he)
    (SeriesLimitLaws.shrinks_scale d hdRate (2*H) (Rat.mul_nonneg (by decide) hH))
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+4+1 by omega))))
  have sn (N : Nat) : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  let T := fun N => pairedSmallDiskRemainderRate H (N+4)+s N
  have hT : ShrinksToZero T := RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_shift _ (pairedSmallDiskRemainderRate_shrinks H) 4) hs
  have vF := pairedRegularPart_valid z (LocalODE.interior_bound _ z hz)
  have vG := pairedRegularPart_valid a (LocalODE.interior_bound _ a ha)
  have vD := pairedSmallDiskDerivativeValue_valid a (LocalODE.interior_bound _ a ha)
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p hp T hT _ _ (pairedSmallDiskRemainder_valid a z ha hz) vR
  · intro N
    exact (pairedSmallDiskRemainder_close a z ha hz H hH hd (N+4)).mono
      (by change pairedSmallDiskRemainderRate H (N+4)≤pairedSmallDiskRemainderRate H (N+4)+s N; have := sn N; grind only)
  · intro N
    let dp := ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n).val) 0 (N+5)
    have vdp := ScalarSeries.block_valid _ (fun n => (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n).property) 0 (N+5)
    have h := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (pairedSmallDiskMapPrefix_valid z hz (N+5)) (pairedSmallDiskMapPrefix_valid a ha (N+5)) vdp vX
      (e N) (e N) (d N) H (dn N) hH (pairedSmallDiskMapPrefix_close z hz N)
      (pairedSmallDiskMapPrefix_close a ha N) (pairedSmallDiskDerivativeValue_close a (LocalODE.interior_bound _ a ha) (N+4)) hd
    have hi := pairedSmallDiskRemainderPrefix_identity (N+5) a z ha hz
    have vq := SeriesLimitLaws.remainder_valid _ _ _ _
      (pairedSmallDiskMapPrefix_valid z hz (N+5)) (pairedSmallDiskMapPrefix_valid a ha (N+5)) vdp vX
    have h1 := Small.congr (sub_valid vR vq) (sub_valid vR (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm hi)) h
    exact h1.mono (by
      change e N+e N+2*d N*H≤pairedSmallDiskRemainderRate H (N+4)+(e N+e N+(2*H)*d N)
      have := pairedSmallDiskRemainderRate_nonnegative H hH (N+4)
      grind only)

end ComputableAnalysis.ModularForms
