import ComputableAnalysis.ModularForms.NomeLinearDiscriminantCancellation

/-! Certified leading term of the actual normalized Fourier discriminant. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- The actual normalized discriminant begins with the actual nome,
with a certified quadratic coordinate error. -/
theorem nomeModularDiscriminant_linear_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hg : 128*r≤(1:Rat)/2) (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (sub (nomeModularDiscriminant q r hr hg hq).val q.val) (9000*r*r) := by
  let e4 := nomeEisensteinFour q r hr hg hq
  let e6 := nomeEisensteinSix q r hr hg hq
  let p : Scalar := ⟨add one (scaleRat 240 q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  let t : Scalar := ⟨add one (scaleRat (-504) q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  let u : Scalar := ⟨sub (LocalODE.power e4.val 3) (LocalODE.power p.val 3),
    sub_valid (LocalODE.power_valid _ e4.property 3) (LocalODE.power_valid _ p.property 3)⟩
  let v : Scalar := ⟨sub (LocalODE.power e6.val 2) (LocalODE.power t.val 2),
    sub_valid (LocalODE.power_valid _ e6.property 2) (LocalODE.power_valid _ t.property 2)⟩
  let num := nomeDiscriminantNumerator q r hr hg hq
  let residual : Scalar := ⟨sub num.val (scaleRat 1728 q.val),sub_valid num.property (scaleRat_valid q.property)⟩
  have hr2 : 0≤r*r := Rat.mul_nonneg hr hr
  have hu := represented_cube_difference_bound e4 p 2 (130560*r*r) (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hr)
    (nomeEisensteinFour_small_disk_bound q r hr hg hq hsmall)
    (nomeEisensteinFour_linear_polynomial_bound q r hr hq hsmall)
    (nomeEisensteinFour_linear_bound q r hr hg hq)
  have hv := represented_square_difference_bound e6 t 2 (1048320*r*r) (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hr)
    (nomeEisensteinSix_small_disk_bound q r hr hg hq hsmall)
    (nomeEisensteinSix_linear_polynomial_bound q r hr hq hsmall)
    (nomeEisensteinSix_linear_bound q r hr hg hq)
  have hpoly := nomeLinearDiscriminantResidual_bound q r hr hq hsmall
  have hsum := LocalODE.small_add (SeriesLimitLaws.small_sub hu hv) hpoly
  let sum : Scalar := ⟨add (sub u.val v.val) (nomeLinearDiscriminantResidual q).val,
    add_valid (sub_valid u.property v.property) (nomeLinearDiscriminantResidual q).property⟩
  have he : sum.val.Equiv residual.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sum.property) (hright := residual.property)
    let E := ComplexRawQuotient.ofRaw (LocalODE.power e4.val 3) (LocalODE.power_valid _ e4.property 3)
    let F := ComplexRawQuotient.ofRaw (LocalODE.power e6.val 2) (LocalODE.power_valid _ e6.property 2)
    let P := ComplexRawQuotient.ofRaw (LocalODE.power p.val 3) (LocalODE.power_valid _ p.property 3)
    let T := ComplexRawQuotient.ofRaw (LocalODE.power t.val 2) (LocalODE.power_valid _ t.property 2)
    let Q := ComplexRawQuotient.scaleRat 1728 (ComplexRawQuotient.ofRaw q.val q.property)
    change ((E-P)-(F-T))+((P-T)-Q)=(E-F)-Q
    grind only
  have hb := Small.congr sum.property residual.property he hsum
  have hrate : (12*(130560*r*r)*2*2+4*(1048320*r*r)*2)+163276*r*r=14816716*r*r := by grind only
  rw [hrate] at hb
  have hs := LocalODE.small_scale (show (0:Rat)≤1/1728 by decide +kernel) hb
  have hscale : (scaleRat (1/1728) residual.val).Equiv (sub (nomeModularDiscriminant q r hr hg hq).val q.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := scaleRat_valid residual.property)
      (hright := sub_valid (nomeModularDiscriminant q r hr hg hq).property q.property)
    let N := ComplexRawQuotient.ofRaw num.val num.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change ComplexRawQuotient.scaleRat (1/1728) (N-ComplexRawQuotient.scaleRat 1728 Q)=
      ComplexRawQuotient.scaleRat (1/1728) N-Q
    change ComplexRawQuotient.scaleRat (1/1728) (N+ -(ComplexRawQuotient.scaleRat 1728 Q))=
      ComplexRawQuotient.scaleRat (1/1728) N+ -Q
    rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_scaleRat,
      ComplexRawQuotient.scaleRat_scaleRat,show (1/1728:Rat)*(-1728)= -1 by decide +kernel,
      ←ComplexRawQuotient.neg_eq_scaleRat_neg_one]
  have h := Small.congr (scaleRat_valid residual.property)
    (sub_valid (nomeModularDiscriminant q r hr hg hq).property q.property) hscale hs
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right (show (14816716:Rat)/1728≤9000 by decide +kernel) hr2
  grind only

end ComputableAnalysis.ModularForms
