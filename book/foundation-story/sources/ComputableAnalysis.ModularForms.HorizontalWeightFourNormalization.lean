import ComputableAnalysis.ModularForms.HorizontalWeightFourPrefixes

/-! Exact geometric-pi normalization of the actual horizontal weight-four lattice row. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual horizontal row is the negative constructed inverse-fourth coefficient. -/
theorem upperHorizontalWeightFourSum_coefficient (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightFourSum z hz).Equiv (neg pairedCenterQuadraticSum) := by
  let p := fun N => (upperLatticeFiniteRow z hz 4 (N+1) 0).val
  have vp N : (p N).Valid := (upperLatticeFiniteRow z hz 4 (N+1) 0).property
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have hN N : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
  have hB0 N : 0≤4*((N+1:Nat):Rat)⁻¹ :=
    Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr (hN N)))
  have hE0 N : 0≤upperWeightFourTailRate z hz N :=
    Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos (hN N) (hN N))))
  have he := RepresentedCauchySum.sum_shrinks _ _ (upperWeightFourTailRate_shrinks z hz)
    (pairedReciprocalTail_shrinks 4)
  apply RepresentedCauchySum.unique p vp
    (fun N => upperWeightFourTailRate z hz N+4*((N+1:Nat):Rat)⁻¹) he
    (upperHorizontalWeightFourSum z hz) (neg pairedCenterQuadraticSum)
    (upperHorizontalWeightFourSum_valid z hz) (neg_valid pairedCenterQuadraticSum_valid)
  · intro N
    apply (upperHorizontalWeightFourSum_close_prefix z hz N).mono
    have h := hB0 N
    grind only
  · intro N
    let q := ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1)
    have vq : q.Valid := ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1)
    have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vp N) (hright := neg_valid vq)
      (upperHorizontalWeightFour_finite_coefficient z hz (N+1))
    have heq : (neg (sub pairedCenterQuadraticSum q)).Equiv (sub (neg pairedCenterQuadraticSum) (p N)) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (sub_valid pairedCenterQuadraticSum_valid vq))
        (hright := sub_valid (neg_valid pairedCenterQuadraticSum_valid) (vp N))
      let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
      let Q := ComplexRawQuotient.ofRaw q vq
      let P := ComplexRawQuotient.ofRaw (p N) (vp N)
      change P= -Q at hp
      change -(B-Q)= -B-P
      generalize B=b,Q=q,P=p at hp ⊢
      grind only
    have h := Small.congr (neg_valid (sub_valid pairedCenterQuadraticSum_valid vq))
      (sub_valid (neg_valid pairedCenterQuadraticSum_valid) (vp N)) heq
      (SeriesLimitLaws.small_neg (pairedCenterQuadraticSum_close N))
    apply h.mono
    have h := hE0 N
    grind only

/-- The actual horizontal weight-four row equals its geometric-pi normalization
at every valid represented upper-half-plane input. -/
theorem upperHorizontalWeightFourSum_pi_fourth (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightFourSum z hz).Equiv
      (scaleRat (1/45) (LocalODE.power geometricPiScalar.val 4)) := by
  have h1 := neg_equiv pairedCenterQuadraticSum_pi_fourth
  have h2 : (neg (scaleRat (-1/45) (LocalODE.power geometricPiScalar.val 4))).Equiv
      (scaleRat (1/45) (LocalODE.power geometricPiScalar.val 4)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)))
      (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4))
    change -(ComplexRawQuotient.scaleRat (-1/45)
      (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4)))=
      ComplexRawQuotient.scaleRat (1/45)
        (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4))
    rw [ComplexRawQuotient.neg_scaleRat,show -(-1/45:Rat)=1/45 by decide +kernel]
  exact equiv_trans (upperHorizontalWeightFourSum_valid z hz) (neg_valid pairedCenterQuadraticSum_valid)
    (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)) (upperHorizontalWeightFourSum_coefficient z hz)
    (equiv_trans (neg_valid pairedCenterQuadraticSum_valid)
      (neg_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)))
      (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)) h1 h2)

end ComputableAnalysis.ModularForms
