import ComputableAnalysis.ModularForms.UpperDerivativeLimits

/-! Independence of the neighborhood schedule used for derivative limits. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory

theorem localDerivativeWeightFourTailRate_nonnegative (a : Scalar)
    (ha : InUpperHalfPlane a.val) (n : Nat) : 0≤localDerivativeWeightFourTailRate a ha n := by
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos n
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hC := latticeRegionReciprocalConstant_nonnegative _ _ _
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha)
  unfold localDerivativeWeightFourTailRate regionalDerivativeFourTailConstant reciprocalSquare
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hC))) hi

theorem neighborhoodDerivativeWeightFourSum_center_independent
    (a b : Scalar) (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hza : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val)
    (hzb : Small (ComplexRaw.sub z.val b.val) (upperRadius b hb).val) :
    (neighborhoodDerivativeWeightFourSum a ha z hz).Equiv
      (neighborhoodDerivativeWeightFourSum b hb z hz) := by
  apply RepresentedCauchySum.value_congr
    (fun n => derivativeWeightFourTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock_valid z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock_valid z hz 0 (n+1))
    (localDerivativeWeightFourTailRate a ha) (localDerivativeWeightFourTailRate b hb)
    (localDerivativeWeightFourTailRate_shrinks a ha) (localDerivativeWeightFourTailRate_shrinks b hb)
    (localDerivativeWeightFourTailRate_nonnegative a ha) (localDerivativeWeightFourTailRate_nonnegative b hb)
    (derivativeWeightFourPrefix_local_cauchy a ha z hz hza)
    (derivativeWeightFourPrefix_local_cauchy b hb z hz hzb)
  intro n
  exact ComplexRaw.equiv_refl _ (derivativeWeightFourTailBlock_valid z hz 0 (n+1))

theorem localDerivativeWeightSixTailRate_nonnegative (a : Scalar)
    (ha : InUpperHalfPlane a.val) (n : Nat) : 0≤localDerivativeWeightSixTailRate a ha n := by
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos n
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hC := latticeRegionReciprocalConstant_nonnegative _ _ _
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha)
  unfold localDerivativeWeightSixTailRate regionalDerivativeSixTailConstant reciprocalSquare
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hC))) hi

theorem neighborhoodDerivativeWeightSixSum_center_independent
    (a b : Scalar) (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hza : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val)
    (hzb : Small (ComplexRaw.sub z.val b.val) (upperRadius b hb).val) :
    (neighborhoodDerivativeWeightSixSum a ha z hz).Equiv
      (neighborhoodDerivativeWeightSixSum b hb z hz) := by
  apply RepresentedCauchySum.value_congr
    (fun n => derivativeWeightSixTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock_valid z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock_valid z hz 0 (n+1))
    (localDerivativeWeightSixTailRate a ha) (localDerivativeWeightSixTailRate b hb)
    (localDerivativeWeightSixTailRate_shrinks a ha) (localDerivativeWeightSixTailRate_shrinks b hb)
    (localDerivativeWeightSixTailRate_nonnegative a ha) (localDerivativeWeightSixTailRate_nonnegative b hb)
    (derivativeWeightSixPrefix_local_cauchy a ha z hz hza)
    (derivativeWeightSixPrefix_local_cauchy b hb z hz hzb)
  intro n
  exact ComplexRaw.equiv_refl _ (derivativeWeightSixTailBlock_valid z hz 0 (n+1))

theorem upperSelf_near (z : Scalar) (hz : InUpperHalfPlane z.val) :
    Small (ComplexRaw.sub z.val z.val) (upperRadius z hz).val := by
  have he : (ComplexRaw.sub z.val z.val).Equiv ComplexRaw.zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.sub_valid z.property z.property)
      (hright := ComplexRaw.ofQComplex_valid _)
    change ComplexRawQuotient.ofRaw z.val z.property +
      -ComplexRawQuotient.ofRaw z.val z.property = 0
    grind only
  exact Small.congr (ComplexRaw.ofQComplex_valid _) (ComplexRaw.sub_valid z.property z.property)
    (ComplexRaw.equiv_symm he) (Small.zero (Rat.le_of_lt (upperRadius z hz).property))

def derivativeWeightFourSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  neighborhoodDerivativeWeightFourSum z hz z hz

theorem derivativeWeightFourSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (derivativeWeightFourSum z hz).Valid :=
  neighborhoodDerivativeWeightFourSum_valid z hz z hz (upperSelf_near z hz)

theorem derivativeWeightFourSum_neighborhood_agreement
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) :
    (derivativeWeightFourSum z hz).Equiv (neighborhoodDerivativeWeightFourSum a ha z hz) :=
  neighborhoodDerivativeWeightFourSum_center_independent z a hz ha z hz (upperSelf_near z hz) hs

def derivativeWeightSixSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  neighborhoodDerivativeWeightSixSum z hz z hz

theorem derivativeWeightSixSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (derivativeWeightSixSum z hz).Valid :=
  neighborhoodDerivativeWeightSixSum_valid z hz z hz (upperSelf_near z hz)

theorem derivativeWeightSixSum_neighborhood_agreement
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) :
    (derivativeWeightSixSum z hz).Equiv (neighborhoodDerivativeWeightSixSum a ha z hz) :=
  neighborhoodDerivativeWeightSixSum_center_independent z a hz ha z hz (upperSelf_near z hz) hs

end ComputableAnalysis.ModularForms
