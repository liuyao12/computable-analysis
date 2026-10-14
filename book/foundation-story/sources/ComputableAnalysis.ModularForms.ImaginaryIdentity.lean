import ComputableAnalysis.ModularForms.ActionLaws

/-! The determinant imaginary-part identity at arbitrary valid represented
complex inputs. A common rational point is used only inside the finite proof. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

theorem integerAffine_contains (a b : Int) (z : ComplexRaw) (k : Nat) (p : QComplex)
    (hp : (z.compute k).lo ≤ p ∧ p ≤ (z.compute k).hi) :
    ((integerAffine a b z).compute k).lo ≤ SL2Z.affine a b p ∧
      SL2Z.affine a b p ≤ ((integerAffine a b z).compute k).hi := by
  have hs := QBox.scaleRat_contains (r := (a : Rat)) hp.1 hp.2
  have ha := QBox.add_contains
    (C := { lo := ⟨(b : Rat), 0⟩, hi := ⟨(b : Rat), 0⟩ })
    (y := ⟨(b : Rat), 0⟩) hs.1 hs.2
    (QComplex.le_refl (⟨(b : Rat), 0⟩ : QComplex)) (QComplex.le_refl _)
  simpa only [integerAffine, translate, add, scaleRat, ofQComplex,
    SL2Z.affine, QComplex.add, QComplex.scaleRat, Rat.add_zero] using ha

theorem conjugate_contains (z : ComplexRaw) (k : Nat) (p : QComplex)
    (hp : (z.compute k).lo ≤ p ∧ p ≤ (z.compute k).hi) :
    ((conj z).compute k).lo ≤ QComplex.conj p ∧
      QComplex.conj p ≤ ((conj z).compute k).hi := by
  exact ⟨⟨hp.1.1, Rat.neg_le_neg hp.2.2⟩, ⟨hp.2.1, Rat.neg_le_neg hp.1.2⟩⟩

/-- The determinant-one numerator identity holds exactly on all represented inputs. -/
theorem represented_numerator_conjugate_imag (g : SL2Z) (z : Scalar) :
    (mul (integerAffine g.a g.b z.val)
      (conj (integerAffine g.c g.d z.val))).imagPart.Equiv z.val.imagPart := by
  intro k
  let p := (z.val.compute k).lo
  have hp : (z.val.compute k).lo ≤ p ∧ p ≤ (z.val.compute k).hi :=
    ⟨QComplex.le_refl _, valid_ordered z.property k⟩
  have hn := integerAffine_contains g.a g.b z.val k p hp
  have hd := integerAffine_contains g.c g.d z.val k p hp
  have hc := conjugate_contains (integerAffine g.c g.d z.val) k _ hd
  have hm := QBox.mul_contains hn.1 hn.2 hc.1 hc.2
  have he := SL2Z.numerator_conjugate_imag g p
  have hlo := hm.1.2
  have hhi := hm.2.2
  rw [he] at hlo hhi
  apply (RealRaw.compareAt_overlap_iff _ _ k k).mpr
  change
    ((mul (integerAffine g.a g.b z.val) (conj (integerAffine g.c g.d z.val))).compute k).lo.im ≤
      (z.val.compute k).hi.im ∧
    (z.val.compute k).lo.im ≤
      ((mul (integerAffine g.a g.b z.val) (conj (integerAffine g.c g.d z.val))).compute k).hi.im
  exact ⟨Rat.le_trans hlo hp.2.2, Rat.le_trans hp.1.2 hhi⟩

/-- The numerator-conjugate expression has strictly positive imaginary part
at every valid represented upper-half-plane point. -/
theorem numerator_conjugate_imag_positive (g : SL2Z) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    (mul (integerAffine g.a g.b z.val)
      (conj (integerAffine g.c g.d z.val))).imagPart.Pos := by
  apply positive_of_equiv (imagPart_valid z.property)
    (imagPart_valid (mul_valid (integerAffine_valid _ _ z.property)
      (conj_valid _ (integerAffine_valid _ _ z.property))))
    (RealRaw.equiv_symm (represented_numerator_conjugate_imag g z)) hz

/-- A nonzero represented complex value has strictly positive squared norm.
The real coordinate of its product with its conjugate supplies the norm value. -/
theorem norm_product_real_positive (z : Scalar) (hz : NonzeroBoxSearch.Nonzero z) :
    (mul z.val (conj z.val)).realPart.Pos := by
  obtain ⟨N, hN⟩ := NonzeroBoxSearch.exists_separated z hz
  let margin := NonzeroBoxSearch.margin (z.val.compute N)
  have hp : 0 < margin := NonzeroBoxSearch.margin_pos _ hN
  have hs : 0 < margin*margin := Rat.mul_pos hp hp
  let eps : QPos := ⟨margin*margin/2, by grind only⟩
  have hv := realPart_valid (mul_valid z.property (conj_valid _ z.property))
  obtain ⟨K,hK⟩ := hv.2.2 eps
  let M := max N K
  let p := (z.val.compute M).center
  have hmem := QBox.center_mem (valid_ordered z.property M)
  have hc := conjugate_contains z.val M p hmem
  have hm := QBox.mul_contains hmem.1 hmem.2 hc.1 hc.2
  have he : (QComplex.mul p (QComplex.conj p)).re = QComplex.normSq p := by
    simp only [QComplex.mul, QComplex.conj, QComplex.normSq]
    grind
  have hi := hm.2.1
  rw [he] at hi
  have hb := NonzeroBoxSearch.center_normSq_lower z N M (Nat.le_max_left _ _) hN
  have hw := hK M (Nat.le_max_right _ _)
  refine ⟨M, ?_⟩
  change 0 < ((mul z.val (conj z.val)).compute M).lo.re
  change ((mul z.val (conj z.val)).compute M).hi.re -
    ((mul z.val (conj z.val)).compute M).lo.re ≤ margin*margin/2 at hw
  change margin*margin ≤ QComplex.normSq p at hb
  change QComplex.normSq p ≤ ((mul z.val (conj z.val)).compute M).hi.re at hi
  grind only

/-- The squared-norm product has zero imaginary value, despite interval dependency. -/
theorem norm_product_imag_zero (z : Scalar) :
    (mul z.val (conj z.val)).imagPart.Equiv (RealRaw.ofRat 0) := by
  intro k
  let p := (z.val.compute k).center
  have hp := QBox.center_mem (valid_ordered z.property k)
  have hc := conjugate_contains z.val k p hp
  have hm := QBox.mul_contains hp.1 hp.2 hc.1 hc.2
  have he : (QComplex.mul p (QComplex.conj p)).im = 0 := by
    simp only [QComplex.mul, QComplex.conj]
    grind
  have hlo := hm.1.2
  have hhi := hm.2.2
  rw [he] at hlo hhi
  exact (RealRaw.compareAt_overlap_iff _ _ k k).mpr ⟨hlo,hhi⟩

end ComputableAnalysis.ModularForms
