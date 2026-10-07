import ComputableAnalysis.ModularForms.RepresentedPrefixFactors
import ComputableAnalysis.ModularForms.UpperPositiveRowsFourier
import ComputableAnalysis.ModularForms.UpperPositiveRowsSumPrefixes

/-! Actual positive lattice-row sums equal weighted Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Exact Fourier formula for the sum of all positive weight-4 lattice rows. -/
theorem upperPositiveWeightFourRowsSum_lambert (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 32*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) :
    (upperPositiveWeightFourRowsSum z hz).Equiv
      (scaleRat (8/3) (mul (LocalODE.power geometricPiScalar.val 4)
        (weightedLambertSum (nome.eval z hz) r 3 hr (by grind only) hq))) := by
  have hg : 4*r*(2:Rat)^3≤(1:Rat)/2 := by
    have hp : (2:Rat)^3=8 := by decide +kernel
    rw [hp]
    grind only
  let q := nome.eval z hz
  let F : Scalar := ⟨upperPositiveWeightFourRowsSum z hz,upperPositiveWeightFourRowsSum_valid z hz⟩
  let G : Scalar := ⟨nomeMomentOuterSum q r 3 hr hg hq,nomeMomentOuterSum_valid q r 3 hr hg hq⟩
  let P : Scalar := ⟨LocalODE.power geometricPiScalar.val 4,LocalODE.power_valid _ geometricPiScalar.property 4⟩
  let A : Scalar := ⟨scaleRat (8/3) P.val,scaleRat_valid P.property⟩
  let p := fun N => (⟨upperPositiveLatticeRowsLimitPrefix z hz 4 (by omega) (N+2),
    upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) (N+2)⟩ : Scalar)
  let u := nomeMomentOuterTerm q r 3
  have hu := nomeMomentOuterTerm_valid q r 3 hr hg hq
  let t := fun N => (⟨ScalarSeries.block u 0 (N+2),ScalarSeries.block_valid u hu 0 (N+2)⟩ : Scalar)
  have hpq N : (p N).val.Equiv (mul A.val (t N).val) := by
    have hrow n : (upperPositiveLatticeRowSum z hz 4 (by omega) n).val.Equiv (mul A.val (u n)) := by
      have hf := upperPositiveLatticeRowSum_quartic_nomePower z hz r hr hlocal hq n
      exact equiv_trans (upperPositiveLatticeRowSum z hz 4 (by omega) n).property
        (scaleRat_valid (mul_valid P.property (hu n))) (mul_valid A.property (hu n)) hf
        (representedScale_mul_factor P ⟨u n,hu n⟩ (8/3))
    have hb := ScalarSeries.block_congr
      (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) n).val)
      (fun n => mul A.val (u n)) hrow 0 (N+2)
    exact equiv_trans (p N).property
      (ScalarSeries.block_valid _ (fun n => mul_valid A.property (hu n)) 0 (N+2))
      (mul_valid A.property (t N).property) hb (representedPrefix_mul_left u hu A (N+2))
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have he := rationalInverseSquareRate_shrinks _ hC
  have hf := SeriesLimitLaws.shrinks_shift _ (nomeMomentOuterSum_tail_shrinks r 3 hr hg) 2
  have hf0 N : 0≤4*(4*r)*(2*r)^(N+2) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (by decide) hr))
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr))
  have hFG := representedFactor_limit_comparison F G A p t
    (fun N => upperWeightFourTailConstant z hz*(((N+1:Nat):Rat))⁻¹)
    (fun N => 4*(4*r)*(2*r)^(N+2)) he hf hf0
    (upperPositiveWeightFourRowsSum_close_prefix z hz)
    (fun N => nomeMomentOuterSum_close q r 3 hr hg hq (N+2)) hpq
  let W : Scalar := ⟨weightedLambertSum q r 3 hr (nomeMomentGuard_lambertLocal r 3 hr hg) hq,
    weightedLambertSum_valid q r 3 hr (nomeMomentGuard_lambertLocal r 3 hr hg) hq
      (nomeMomentGuard_lambertRatio r 3 hr hg)⟩
  have hGW : G.val.Equiv W.val := nomeMomentOuterSum_eq_weightedLambertSum q r 3 hr hg hq
  have hAW := mul_equiv A.property A.property G.property W.property (equiv_refl A.val A.property) hGW
  have hfinal := equiv_symm (representedScale_mul_factor P W (8/3))
  exact equiv_trans F.property (mul_valid A.property G.property)
    (scaleRat_valid (mul_valid P.property W.property)) hFG
    (equiv_trans (mul_valid A.property G.property) (mul_valid A.property W.property)
      (scaleRat_valid (mul_valid P.property W.property)) hAW hfinal)

/-- Exact Fourier formula for the sum of all positive weight-6 lattice rows. -/
theorem upperPositiveWeightSixRowsSum_lambert (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 128*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) :
    (upperPositiveWeightSixRowsSum z hz).Equiv
      (scaleRat (-8/15) (mul (LocalODE.power geometricPiScalar.val 6)
        (weightedLambertSum (nome.eval z hz) r 5 hr (by grind only) hq))) := by
  have hg : 4*r*(2:Rat)^5≤(1:Rat)/2 := by
    have hp : (2:Rat)^5=32 := by decide +kernel
    rw [hp]
    grind only
  let q := nome.eval z hz
  let F : Scalar := ⟨upperPositiveWeightSixRowsSum z hz,upperPositiveWeightSixRowsSum_valid z hz⟩
  let G : Scalar := ⟨nomeMomentOuterSum q r 5 hr hg hq,nomeMomentOuterSum_valid q r 5 hr hg hq⟩
  let P : Scalar := ⟨LocalODE.power geometricPiScalar.val 6,LocalODE.power_valid _ geometricPiScalar.property 6⟩
  let A : Scalar := ⟨scaleRat (-8/15) P.val,scaleRat_valid P.property⟩
  let p := fun N => (⟨upperPositiveLatticeRowsLimitPrefix z hz 6 (by omega) (N+2),
    upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) (N+2)⟩ : Scalar)
  let u := nomeMomentOuterTerm q r 5
  have hu := nomeMomentOuterTerm_valid q r 5 hr hg hq
  let t := fun N => (⟨ScalarSeries.block u 0 (N+2),ScalarSeries.block_valid u hu 0 (N+2)⟩ : Scalar)
  have hpq N : (p N).val.Equiv (mul A.val (t N).val) := by
    have hrow n : (upperPositiveLatticeRowSum z hz 6 (by omega) n).val.Equiv (mul A.val (u n)) := by
      have hf := upperPositiveLatticeRowSum_sextic_nomePower z hz r hr hlocal hq n
      exact equiv_trans (upperPositiveLatticeRowSum z hz 6 (by omega) n).property
        (scaleRat_valid (mul_valid P.property (hu n))) (mul_valid A.property (hu n)) hf
        (representedScale_mul_factor P ⟨u n,hu n⟩ (-8/15))
    have hb := ScalarSeries.block_congr
      (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) n).val)
      (fun n => mul A.val (u n)) hrow 0 (N+2)
    exact equiv_trans (p N).property
      (ScalarSeries.block_valid _ (fun n => mul_valid A.property (hu n)) 0 (N+2))
      (mul_valid A.property (t N).property) hb (representedPrefix_mul_left u hu A (N+2))
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have he := rationalInverseSquareRate_shrinks _ hC
  have hf := SeriesLimitLaws.shrinks_shift _ (nomeMomentOuterSum_tail_shrinks r 5 hr hg) 2
  have hf0 N : 0≤4*(4*r)*(2*r)^(N+2) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (by decide) hr))
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr))
  have hFG := representedFactor_limit_comparison F G A p t
    (fun N => upperWeightSixTailConstant z hz*(((N+1:Nat):Rat))⁻¹)
    (fun N => 4*(4*r)*(2*r)^(N+2)) he hf hf0
    (upperPositiveWeightSixRowsSum_close_prefix z hz)
    (fun N => nomeMomentOuterSum_close q r 5 hr hg hq (N+2)) hpq
  let W : Scalar := ⟨weightedLambertSum q r 5 hr (nomeMomentGuard_lambertLocal r 5 hr hg) hq,
    weightedLambertSum_valid q r 5 hr (nomeMomentGuard_lambertLocal r 5 hr hg) hq
      (nomeMomentGuard_lambertRatio r 5 hr hg)⟩
  have hGW : G.val.Equiv W.val := nomeMomentOuterSum_eq_weightedLambertSum q r 5 hr hg hq
  have hAW := mul_equiv A.property A.property G.property W.property (equiv_refl A.val A.property) hGW
  have hfinal := equiv_symm (representedScale_mul_factor P W (-8/15))
  exact equiv_trans F.property (mul_valid A.property G.property)
    (scaleRat_valid (mul_valid P.property W.property)) hFG
    (equiv_trans (mul_valid A.property G.property) (mul_valid A.property W.property)
      (scaleRat_valid (mul_valid P.property W.property)) hAW hfinal)

end ComputableAnalysis.ModularForms
