import ComputableAnalysis.ModularForms.FractionalLinear

/-! Exact comparison laws for the represented fractional-linear evaluator. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- The quotient evaluator is the unique valid solution of its denominator equation. -/
theorem fractionalLinear_unique (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (w : Scalar) (hw : (mul (integerAffine g.c g.d z.val) w.val).Equiv
      (integerAffine g.a g.b z.val)) : (fractionalLinear g z hz).val.Equiv w.val := by
  apply RepresentedReciprocal.mul_cancel
    ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩
    (denominator_nonzero g z hz) (fractionalLinear g z hz) w
  exact equiv_trans
    (mul_valid (integerAffine_valid _ _ z.property) (fractionalLinear g z hz).property)
    (integerAffine_valid _ _ z.property)
    (mul_valid (integerAffine_valid _ _ z.property) w.property)
    (fractionalLinear_cancel g z hz) (equiv_symm hw)

theorem integerAffine_one (b : Int) (z : Scalar) :
    (integerAffine 1 b z.val).Equiv (translate (b : Rat) z.val) := by
  apply translate_equiv
  exact scaleRat_one_equiv _ z.property

theorem integerAffine_zero (b : Int) (z : Scalar) :
    (integerAffine 0 b z.val).Equiv (ofQComplex ⟨(b : Rat), 0⟩) := by
  have h := scaleRat_zeroScalar_equiv z.val z.property
  have ht := translate_equiv (b : Rat) h
  apply equiv_trans (integerAffine_valid _ _ z.property)
    (translate_valid _ (ofQComplex_valid _)) (ofQComplex_valid _) ht
  exact zero_add_equiv _ (ofQComplex_valid _)

/-- The identity matrix acts as the identity on every represented upper-half-plane point. -/
theorem fractionalLinear_identity (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear SL2Z.identity z hz).val.Equiv z.val := by
  apply fractionalLinear_unique SL2Z.identity z hz z
  have hd : (integerAffine 0 1 z.val).Equiv (ofQComplex QComplex.one) :=
    integerAffine_zero 1 z
  have hn := integerAffine_one 0 z
  have ht : (translate 0 z.val).Equiv z.val := add_zero_equiv _ z.property
  have hm := mul_equiv (integerAffine_valid 0 1 z.property) (ofQComplex_valid _)
    z.property z.property hd (equiv_refl _ z.property)
  exact equiv_trans (mul_valid (integerAffine_valid _ _ z.property) z.property)
    (mul_valid (ofQComplex_valid _) z.property) (integerAffine_valid _ _ z.property)
    hm (equiv_trans (mul_valid (ofQComplex_valid _) z.property) z.property
      (integerAffine_valid _ _ z.property) (one_mul_equiv _ z.property)
      (equiv_symm (equiv_trans (integerAffine_valid _ _ z.property)
        (translate_valid 0 z.property) z.property hn ht)))

/-- The standard generator `T` agrees with translation by one. -/
theorem fractionalLinear_T (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear SL2Z.T z hz).val.Equiv (translate 1 z.val) := by
  let w : Scalar := ⟨translate 1 z.val, translate_valid 1 z.property⟩
  apply fractionalLinear_unique SL2Z.T z hz w
  have hd : (integerAffine 0 1 z.val).Equiv (ofQComplex QComplex.one) :=
    integerAffine_zero 1 z
  have hn := integerAffine_one 1 z
  have hm := mul_equiv (integerAffine_valid 0 1 z.property) (ofQComplex_valid _)
    w.property w.property hd (equiv_refl _ w.property)
  exact equiv_trans (mul_valid (integerAffine_valid _ _ z.property) w.property)
    (mul_valid (ofQComplex_valid _) w.property) (integerAffine_valid _ _ z.property)
    hm (equiv_trans (mul_valid (ofQComplex_valid _) w.property) w.property
      (integerAffine_valid _ _ z.property) (one_mul_equiv _ w.property) (equiv_symm hn))

theorem fractionalLinear_T_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    InUpperHalfPlane (fractionalLinear SL2Z.T z hz).val :=
  (upperHalfPlane_congr (fractionalLinear SL2Z.T z hz).property
    (translate_valid 1 z.property) (fractionalLinear_T z hz)).mpr (translate_mem 1 hz)

/-- The standard generator `S` satisfies the exact equation `z * S(z) = -1`. -/
theorem fractionalLinear_S_equation (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul z.val (fractionalLinear SL2Z.S z hz).val).Equiv
      (ofQComplex ⟨-1, 0⟩) := by
  have hd := integerAffine_one 0 z
  have ht : (translate 0 z.val).Equiv z.val := add_zero_equiv _ z.property
  have he := equiv_trans (integerAffine_valid 1 0 z.property)
    (translate_valid 0 z.property) z.property hd ht
  have hm := mul_equiv z.property (integerAffine_valid 1 0 z.property)
    (fractionalLinear SL2Z.S z hz).property (fractionalLinear SL2Z.S z hz).property
    (equiv_symm he) (equiv_refl _ (fractionalLinear SL2Z.S z hz).property)
  exact equiv_trans (mul_valid z.property (fractionalLinear SL2Z.S z hz).property)
    (mul_valid (integerAffine_valid 1 0 z.property) (fractionalLinear SL2Z.S z hz).property)
    (ofQComplex_valid _) hm
    (equiv_trans (mul_valid (integerAffine_valid 1 0 z.property)
      (fractionalLinear SL2Z.S z hz).property) (integerAffine_valid 0 (-1) z.property)
      (ofQComplex_valid _) (fractionalLinear_cancel SL2Z.S z hz) (integerAffine_zero (-1) z))

end ComputableAnalysis.ModularForms
