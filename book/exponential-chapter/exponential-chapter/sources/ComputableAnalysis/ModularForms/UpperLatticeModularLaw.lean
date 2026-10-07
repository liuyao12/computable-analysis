import ComputableAnalysis.ModularForms.UpperPointWeightLaw
import ComputableAnalysis.ModularForms.CMOrbitDenominatorBounds163

/-! Infinite modular weight identities for the constructed lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163 ComplexRaw LocalODE

private theorem index_ge (g : SL2Z) (n : Nat) : n≤basisPrefixIndex g n := by
  have hp : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
  have hm := Nat.mul_le_mul_right (n+1) hp
  unfold basisPrefixIndex
  omega

private theorem index_shrinks (g : SL2Z) (e : Nat → Rat) (he : ShrinksToZero e) :
    ShrinksToZero (fun n => e (basisPrefixIndex g n)) := by
  intro eps
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N,fun n hn => hN _ (Nat.le_trans hn (index_ge g n))⟩

private theorem rateFour_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    0≤upperWeightFourTailRate z hz n := by
  unfold upperWeightFourTailRate upperWeightFourTailConstant reciprocalSquare
  have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz))))
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))

theorem upperWeightFourLatticeSum_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperWeightFourLatticeSum (fractionalLinear g z hz) (fractionalLinear_mem g z hz)).Equiv
      (mul (power (integerAffine g.c g.d z.val) 4) (upperWeightFourLatticeSum z hz)) := by
  let w := fractionalLinear g z hz
  let hw := fractionalLinear_mem g z hz
  let h := latticeIndexMatrix g
  let c := power (integerAffine g.c g.d z.val) 4
  have hc : c.Valid := power_valid _ (integerAffine_valid _ _ z.property) 4
  let M := boxCoordinateBound (c.compute 0)
  have hM : 0≤M := boxCoordinateBound_nonneg _
  have hcM : Small c M := small_from_box c hc 0
  let p := fun n => upperWeightFourPrefix w hw (basisPrefixIndex h n)
  have hp : ∀ n, (p n).Valid := fun n => upperWeightFourPrefix_valid w hw _
  let e := fun n => upperWeightFourTailRate w hw (basisPrefixIndex h n)
  let f := fun n => (2*M)*upperBasisWeightFourError z hz h n
  have he : ShrinksToZero e := index_shrinks h _ (upperWeightFourTailRate_shrinks w hw)
  have hf : ShrinksToZero f := SeriesLimitLaws.shrinks_scale _
    (upperBasisWeightFourError_shrinks z hz h) (2*M) (Rat.mul_nonneg (by decide) hM)
  have he0 (n : Nat) : 0≤e n := rateFour_nonnegative w hw _
  have hE0 (n : Nat) : 0≤upperBasisWeightFourError z hz h n :=
    Rat.add_nonneg (rateFour_nonnegative z hz _) (Rat.add_nonneg
      (rateFour_nonnegative z hz n) (rateFour_nonnegative z hz n))
  have hf0 (n : Nat) : 0≤f n := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (hE0 n)
  apply RepresentedCauchySum.unique p hp (fun n => e n+f n)
    (RepresentedCauchySum.sum_shrinks e f he hf) _ _
    (upperWeightFourLatticeSum_valid w hw) (mul_valid hc (upperWeightFourLatticeSum_valid z hz))
  · intro n
    exact (upperWeightFourLatticeSum_close_prefix w hw (basisPrefixIndex h n)).mono (by
      have hh := hf0 n
      change e n≤e n+f n
      grind only)
  · intro n
    have hb := representedFactor_difference_small c (upperWeightFourLatticeSum z hz)
      (upperBasisReindexedPrefix z hz h 4 n) hc (upperWeightFourLatticeSum_valid z hz)
      (upperBasisReindexedPrefix_valid z hz h 4 n) M (upperBasisWeightFourError z hz h n)
      hM (hE0 n) hcM (upperWeightFourLatticeSum_close_reindexed z hz h n)
    have ht := Small.congr
      (sub_valid (mul_valid hc (upperWeightFourLatticeSum_valid z hz))
        (mul_valid hc (upperBasisReindexedPrefix_valid z hz h 4 n)))
      (sub_valid (mul_valid hc (upperWeightFourLatticeSum_valid z hz)) (hp n))
      (FunctionTheory.sub_congr (equiv_refl _ (mul_valid hc (upperWeightFourLatticeSum_valid z hz)))
        (equiv_symm (upperWeightFourPrefix_action g z hz n))) hb
    exact ht.mono (by
      have hh := he0 n
      change f n≤e n+f n
      grind only)

private theorem rateSix_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    0≤upperWeightSixTailRate z hz n := by
  unfold upperWeightSixTailRate upperWeightSixTailConstant reciprocalSquare
  have hp : 0<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz))))
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp)))

theorem upperWeightSixLatticeSum_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperWeightSixLatticeSum (fractionalLinear g z hz) (fractionalLinear_mem g z hz)).Equiv
      (mul (power (integerAffine g.c g.d z.val) 6) (upperWeightSixLatticeSum z hz)) := by
  let w := fractionalLinear g z hz
  let hw := fractionalLinear_mem g z hz
  let h := latticeIndexMatrix g
  let c := power (integerAffine g.c g.d z.val) 6
  have hc : c.Valid := power_valid _ (integerAffine_valid _ _ z.property) 6
  let M := boxCoordinateBound (c.compute 0)
  have hM : 0≤M := boxCoordinateBound_nonneg _
  have hcM : Small c M := small_from_box c hc 0
  let p := fun n => upperWeightSixPrefix w hw (basisPrefixIndex h n)
  have hp : ∀ n, (p n).Valid := fun n => upperWeightSixPrefix_valid w hw _
  let e := fun n => upperWeightSixTailRate w hw (basisPrefixIndex h n)
  let f := fun n => (2*M)*upperBasisWeightSixError z hz h n
  have he : ShrinksToZero e := index_shrinks h _ (upperWeightSixTailRate_shrinks w hw)
  have hf : ShrinksToZero f := SeriesLimitLaws.shrinks_scale _
    (upperBasisWeightSixError_shrinks z hz h) (2*M) (Rat.mul_nonneg (by decide) hM)
  have he0 (n : Nat) : 0≤e n := rateSix_nonnegative w hw _
  have hE0 (n : Nat) : 0≤upperBasisWeightSixError z hz h n :=
    Rat.add_nonneg (rateSix_nonnegative z hz _) (Rat.add_nonneg
      (rateSix_nonnegative z hz n) (rateSix_nonnegative z hz n))
  have hf0 (n : Nat) : 0≤f n := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (hE0 n)
  apply RepresentedCauchySum.unique p hp (fun n => e n+f n)
    (RepresentedCauchySum.sum_shrinks e f he hf) _ _
    (upperWeightSixLatticeSum_valid w hw) (mul_valid hc (upperWeightSixLatticeSum_valid z hz))
  · intro n
    exact (upperWeightSixLatticeSum_close_prefix w hw (basisPrefixIndex h n)).mono (by
      have hh := hf0 n
      change e n≤e n+f n
      grind only)
  · intro n
    have hb := representedFactor_difference_small c (upperWeightSixLatticeSum z hz)
      (upperBasisReindexedPrefix z hz h 6 n) hc (upperWeightSixLatticeSum_valid z hz)
      (upperBasisReindexedPrefix_valid z hz h 6 n) M (upperBasisWeightSixError z hz h n)
      hM (hE0 n) hcM (upperWeightSixLatticeSum_close_reindexed z hz h n)
    have ht := Small.congr
      (sub_valid (mul_valid hc (upperWeightSixLatticeSum_valid z hz))
        (mul_valid hc (upperBasisReindexedPrefix_valid z hz h 6 n)))
      (sub_valid (mul_valid hc (upperWeightSixLatticeSum_valid z hz)) (hp n))
      (FunctionTheory.sub_congr (equiv_refl _ (mul_valid hc (upperWeightSixLatticeSum_valid z hz)))
        (equiv_symm (upperWeightSixPrefix_action g z hz n))) hb
    exact ht.mono (by
      have hh := he0 n
      change f n≤e n+f n
      grind only)

end ComputableAnalysis.ModularForms
