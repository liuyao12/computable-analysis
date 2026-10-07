import ComputableAnalysis.ModularForms.HorizontalWeightSixPrefixes

/-! Exact geometric-pi normalization of the actual horizontal weight-six lattice row. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual horizontal row is the negative constructed inverse-sixth coefficient. -/
theorem upperHorizontalWeightSixSum_coefficient (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightSixSum z hz).Equiv (neg pairedCenterQuarticSum) := by
  let p := fun N => (upperLatticeFiniteRow z hz 6 (N+1) 0).val
  have vp N : (p N).Valid := (upperLatticeFiniteRow z hz 6 (N+1) 0).property
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have hN N : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
  have hB0 N : 0≤8*((N+1:Nat):Rat)⁻¹ :=
    Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr (hN N)))
  have hE0 N : 0≤upperWeightSixTailRate z hz N :=
    Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos (hN N) (hN N))))
  have he := RepresentedCauchySum.sum_shrinks _ _ (upperWeightSixTailRate_shrinks z hz)
    (pairedReciprocalTail_shrinks 8)
  apply RepresentedCauchySum.unique p vp
    (fun N => upperWeightSixTailRate z hz N+8*((N+1:Nat):Rat)⁻¹) he
    (upperHorizontalWeightSixSum z hz) (neg pairedCenterQuarticSum)
    (upperHorizontalWeightSixSum_valid z hz) (neg_valid pairedCenterQuarticSum_valid)
  · intro N
    apply (upperHorizontalWeightSixSum_close_prefix z hz N).mono
    have h := hB0 N
    grind only
  · intro N
    let q := ScalarSeries.block pairedCenterQuarticTerm 0 (N+1)
    have vq : q.Valid := ScalarSeries.block_valid _ pairedCenterQuarticTerm_valid 0 (N+1)
    have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vp N) (hright := neg_valid vq)
      (upperHorizontalWeightSix_finite_coefficient z hz (N+1))
    have heq : (neg (sub pairedCenterQuarticSum q)).Equiv (sub (neg pairedCenterQuarticSum) (p N)) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (sub_valid pairedCenterQuarticSum_valid vq))
        (hright := sub_valid (neg_valid pairedCenterQuarticSum_valid) (vp N))
      let B := ComplexRawQuotient.ofRaw pairedCenterQuarticSum pairedCenterQuarticSum_valid
      let Q := ComplexRawQuotient.ofRaw q vq
      let P := ComplexRawQuotient.ofRaw (p N) (vp N)
      change P= -Q at hp
      change -(B-Q)= -B-P
      generalize B=b,Q=q,P=p at hp ⊢
      grind only
    have h := Small.congr (neg_valid (sub_valid pairedCenterQuarticSum_valid vq))
      (sub_valid (neg_valid pairedCenterQuarticSum_valid) (vp N)) heq
      (SeriesLimitLaws.small_neg (pairedCenterQuarticSum_close N))
    apply h.mono
    have h := hE0 N
    grind only

/-- The actual horizontal weight-six row equals its geometric-pi normalization
at every valid represented upper-half-plane input. -/
theorem upperHorizontalWeightSixSum_pi_sixth (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightSixSum z hz).Equiv
      (scaleRat (2/945) (LocalODE.power geometricPiScalar.val 6)) := by
  have h1 := neg_equiv pairedCenterQuarticSum_pi_sixth
  have h2 : (neg (scaleRat (-2/945) (LocalODE.power geometricPiScalar.val 6))).Equiv
      (scaleRat (2/945) (LocalODE.power geometricPiScalar.val 6)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6)))
      (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6))
    change -(ComplexRawQuotient.scaleRat (-2/945)
      (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 6) (LocalODE.power_valid _ geometricPiScalar.property 6)))=
      ComplexRawQuotient.scaleRat (2/945)
        (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 6) (LocalODE.power_valid _ geometricPiScalar.property 6))
    rw [ComplexRawQuotient.neg_scaleRat,show -(-2/945:Rat)=2/945 by decide +kernel]
  exact equiv_trans (upperHorizontalWeightSixSum_valid z hz) (neg_valid pairedCenterQuarticSum_valid)
    (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6)) (upperHorizontalWeightSixSum_coefficient z hz)
    (equiv_trans (neg_valid pairedCenterQuarticSum_valid)
      (neg_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6)))
      (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6)) h1 h2)

end ComputableAnalysis.ModularForms
