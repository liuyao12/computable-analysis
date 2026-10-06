import ComputableAnalysis.ModularForms.RealComplexBridge

/-! Upper-half-plane preservation of the actual represented matrix evaluator. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

 theorem positive_inverse_positive (x : RealRaw) (hx : x.Valid) (N : Nat)
    (hp : 0 < (x.compute N).lo) : (RealRaw.positiveInv x N).Pos := by
  refine ⟨N, ?_⟩
  have ho := RealRaw.interval_order_of_valid x hx N
  have hh : 0 < (x.compute N).hi := by grind only
  change 0 < (RealRaw.positiveInvCompute x N N).lo
  simp only [RealRaw.positiveInvCompute, Nat.lt_irrefl, if_false, QInterval.inv]
  rw [if_pos hp, Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr hh

/-- Every integer determinant-one transformation preserves the represented upper half-plane. -/
theorem fractionalLinear_mem (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    InUpperHalfPlane (fractionalLinear g z hz).val := by
  let d : Scalar := ⟨integerAffine g.c g.d z.val, integerAffine_valid _ _ z.property⟩
  let n : Scalar := ⟨integerAffine g.a g.b z.val, integerAffine_valid _ _ z.property⟩
  let norm : Scalar := ⟨mul d.val (conj d.val), mul_valid d.property (conj_valid _ d.property)⟩
  let s := norm.val.realPart
  have hsv : s.Valid := realPart_valid norm.property
  obtain ⟨N,hN⟩ := norm_product_real_positive d (denominator_nonzero g z hz)
  let r := RealRaw.positiveInv s N
  have hrv : r.Valid := RealRaw.positiveInv_valid hsv hN
  let u : Scalar := ⟨mul n.val (conj d.val), mul_valid n.property (conj_valid _ d.property)⟩
  let w : Scalar := ⟨mul u.val (ofRealRaw r), mul_valid u.property (ofRealRaw_valid r hrv)⟩
  have hnorm := equiv_real_embedding norm (norm_product_imag_zero d)
  have hunit := RealRaw.positiveInv_mul_self_equiv_one hsv hN
  have hemb := real_embedding_mul s r hsv hrv
  have hrunit := ofRealRaw_equiv_of_equiv (x := RealRaw.mul s r) (y := RealRaw.one) (RealRaw.mul_valid hsv hrv)
    (RealRaw.ofRat_valid 1) hunit
  have hcmp : (fractionalLinear g z hz).val.Equiv w.val := by
    apply fractionalLinear_unique g z hz w
    have hnq := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := norm.property) (hright := ofRealRaw_valid s hsv) hnorm
    have heq := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := mul_valid (ofRealRaw_valid s hsv) (ofRealRaw_valid r hrv))
      (hright := ofRealRaw_valid (RealRaw.mul s r) (RealRaw.mul_valid hsv hrv)) hemb
    have huq := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ofRealRaw_valid (RealRaw.mul s r) (RealRaw.mul_valid hsv hrv))
      (hright := ofRealRaw_valid RealRaw.one (RealRaw.ofRat_valid 1)) hrunit
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid d.property w.property) (hright := n.property)
    let D := ComplexRawQuotient.ofRaw d.val d.property
    let C := ComplexRawQuotient.ofRaw (conj d.val) (conj_valid _ d.property)
    let A := ComplexRawQuotient.ofRaw n.val n.property
    let B := ComplexRawQuotient.ofRaw (ofRealRaw s) (ofRealRaw_valid s hsv)
    let R := ComplexRawQuotient.ofRaw (ofRealRaw r) (ofRealRaw_valid r hrv)
    change D*C=B at hnq
    have hu : B*R=1 := heq.trans huq
    change D*((A*C)*R)=A
    grind
  have hwp := mul_real_imag_positive u r hrv
    (numerator_conjugate_imag_positive g z hz) (positive_inverse_positive s hsv N hN)
  exact (upperHalfPlane_congr (fractionalLinear g z hz).property w.property hcmp).mpr hwp

end ComputableAnalysis.ModularForms
