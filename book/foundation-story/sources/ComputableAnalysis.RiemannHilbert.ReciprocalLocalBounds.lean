import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Explicit rational neighborhoods avoiding zero and local bounds for the
constructed reciprocal. The neighboring reciprocal is first constructed
locally; its agreement with the public search evaluator follows from uniqueness. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalLocalBounds
open ComplexRaw FunctionTheory NonzeroBoxSearch LocalODE RepresentedReciprocal

def bound (a : Scalar) (ha : Nonzero a) : Rat :=
  boxCoordinateBound ((inverse a ha).val.compute 0)+1

theorem bound_pos (a : Scalar) (ha : Nonzero a) : 0 < bound a ha := by
  have h := boxCoordinateBound_nonneg ((inverse a ha).val.compute 0)
  unfold bound
  grind

theorem inverse_small (a : Scalar) (ha : Nonzero a) :
    Small (inverse a ha).val (bound a ha) :=
  (small_from_box (inverse a ha).val (inverse a ha).property 0).mono (by unfold bound; grind)

def radius (a : Scalar) (ha : Nonzero a) : QPos :=
  ⟨1/(16*bound a ha), by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) (bound_pos a ha)))⟩

theorem radius_identity (a : Scalar) (ha : Nonzero a) :
    16*bound a ha*(radius a ha).val=1 := by
  change 16*bound a ha*(1/(16*bound a ha))=1
  rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt
    (Rat.mul_pos (by decide +kernel) (bound_pos a ha)))]

def normalized (a : Scalar) (ha : Nonzero a) (z : Scalar) : Scalar :=
  ⟨mul (inverse a ha).val z.val, mul_valid (inverse a ha).property z.property⟩

theorem residual (a : Scalar) (ha : Nonzero a) (z : Scalar) :
    (sub (ofQComplex QComplex.one) (normalized a ha z).val).Equiv
      (neg (mul (inverse a ha).val (sub z.val a.val))) := by
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (inverse a ha).property a.property) (hright := ofQComplex_valid _)
    (inverse_mul a ha)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (ofQComplex_valid _) (normalized a ha z).property)
    (hright := neg_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let R := ComplexRawQuotient.ofRaw (inverse a ha).val (inverse a ha).property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change R*A=1 at hu
  change (1 : ScalarAlgebra.Value) + -(R*Z) = -(R*(Z + -A))
  grind

theorem residual_small (a : Scalar) (ha : Nonzero a) (z : Scalar)
    (hza : Small (sub z.val a.val) (radius a ha).val) :
    Small (sub (ofQComplex QComplex.one) (normalized a ha z).val) ((1 : Rat)/8) := by
  have hs := SeriesLimitLaws.small_neg (Small.mul
    (inverse a ha).property (sub_valid z.property a.property)
    (Rat.le_of_lt (bound_pos a ha)) (Rat.le_of_lt (radius a ha).property)
    (inverse_small a ha) hza)
  have hid := radius_identity a ha
  have hb : 2*bound a ha*(radius a ha).val ≤ (1 : Rat)/8 := by grind
  exact Small.congr
    (neg_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property)))
    (sub_valid (ofQComplex_valid _) (normalized a ha z).property)
    (equiv_symm (residual a ha z)) (hs.mono hb)

def candidate (a : Scalar) (ha : Nonzero a) (z : Scalar)
    (hza : Small (sub z.val a.val) (radius a ha).val) : Scalar :=
  let r := ScalarNeumannInverse.value (normalized a ha z) (residual_small a ha z hza)
  ⟨mul (inverse a ha).val r.val, mul_valid (inverse a ha).property r.property⟩

theorem candidate_inverse (a : Scalar) (ha : Nonzero a) (z : Scalar)
    (hza : Small (sub z.val a.val) (radius a ha).val) :
    (mul z.val (candidate a ha z hza).val).Equiv (ofQComplex QComplex.one) := by
  let s := normalized a ha z
  let r := ScalarNeumannInverse.value s (residual_small a ha z hza)
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid s.property r.property) (hright := ofQComplex_valid _)
    (ScalarNeumannInverse.mul_value s (residual_small a ha z hza))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property (candidate a ha z hza).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (inverse a ha).val (inverse a ha).property
  let S := ComplexRawQuotient.ofRaw r.val r.property
  change (R*Z)*S=1 at hu
  change Z*(R*S)=(1 : ScalarAlgebra.Value)
  grind

theorem inside (a : Scalar) (ha : Nonzero a) (z : Scalar)
    (hza : Small (sub z.val a.val) (radius a ha).val) : Nonzero z :=
  nonzero_of_inverse z (candidate a ha z hza) (candidate_inverse a ha z hza)

theorem candidate_small (a : Scalar) (ha : Nonzero a) (z : Scalar)
    (hza : Small (sub z.val a.val) (radius a ha).val) :
    Small (candidate a ha z hza).val (8*bound a ha) := by
  have hs := Small.mul (inverse a ha).property
    (ScalarNeumannInverse.value (normalized a ha z) (residual_small a ha z hza)).property
    (Rat.le_of_lt (bound_pos a ha)) (by decide +kernel)
    (inverse_small a ha) (ScalarNeumannInverse.value_bound _ _)
  have he : 2*bound a ha*4=8*bound a ha := by grind
  rw [he] at hs
  exact hs

theorem inverse_bound (a : Scalar) (ha : Nonzero a) (z : Scalar) (hz : Nonzero z)
    (hza : Small (sub z.val a.val) (radius a ha).val) :
    Small (inverse z hz).val (8*bound a ha) :=
  Small.congr (candidate a ha z hza).property (inverse z hz).property
    (equiv_symm (inverse_unique z hz _ (candidate_inverse a ha z hza)))
    (candidate_small a ha z hza)

end ComputableAnalysis.RiemannHilbert.ReciprocalLocalBounds
