import ComputableAnalysis.ModularForms.NomeEisensteinSmallDiskBounds

/-! Exact linear-polynomial cancellation underlying the discriminant leading term. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions
set_option maxRecDepth 8192

private theorem negative_scale_small (c : Rat) (x : Scalar) (B : Rat) (hc : 0≤c) (hx : Small x.val B) :
    Small (scaleRat (-c) x.val) (c*B) := by
  have he : (neg (scaleRat c x.val)).Equiv (scaleRat (-c) x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid x.property)) (hright := scaleRat_valid x.property)
    change -(ComplexRawQuotient.scaleRat c (ComplexRawQuotient.ofRaw x.val x.property))=
      ComplexRawQuotient.scaleRat (-c) (ComplexRawQuotient.ofRaw x.val x.property)
    exact ComplexRawQuotient.neg_scaleRat c _
  exact Small.congr (neg_valid (scaleRat_valid x.property)) (scaleRat_valid x.property) he
    (SeriesLimitLaws.small_neg (LocalODE.small_scale hc hx))

private theorem sc240 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 240 x=(240:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 240 x
  change ComplexRawQuotient.scaleRat 240 x=(240:ScalarAlgebra.Value)*x at h
  exact h

private theorem sc504 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 504 x=(504:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 504 x
  change ComplexRawQuotient.scaleRat 504 x=(504:ScalarAlgebra.Value)*x at h
  exact h

private theorem sc1728 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 1728 x=(1728:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 1728 x
  change ComplexRawQuotient.scaleRat 1728 x=(1728:ScalarAlgebra.Value)*x at h
  exact h

private theorem sc3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 3 x
  change ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x at h
  exact h

private theorem polynomial_algebra (Q : ScalarAlgebra.Value) :
    (1+ComplexRawQuotient.scaleRat 240 Q)^3-(1+ComplexRawQuotient.scaleRat (-504) Q)^2-
      ComplexRawQuotient.scaleRat 1728 Q=
      ComplexRawQuotient.scaleRat (-81216) (Q^2)+ComplexRawQuotient.scaleRat 13824000 (Q^3) := by
  have hA (X : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat (-81216) X=
      ComplexRawQuotient.scaleRat 3 (ComplexRawQuotient.scaleRat 240 (ComplexRawQuotient.scaleRat 240 X))-
        ComplexRawQuotient.scaleRat 504 (ComplexRawQuotient.scaleRat 504 X) := by
    change ComplexRawQuotient.scaleRat (-81216) X=
      ComplexRawQuotient.scaleRat 3 (ComplexRawQuotient.scaleRat 240 (ComplexRawQuotient.scaleRat 240 X))+
        -(ComplexRawQuotient.scaleRat 504 (ComplexRawQuotient.scaleRat 504 X))
    rw [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.scaleRat_scaleRat,
      ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.add_scaleRat]
    rw [show (3:Rat)*240*240+ -(504*504)= -81216 by decide +kernel]
  have hB (X : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 13824000 X=
      ComplexRawQuotient.scaleRat 240 (ComplexRawQuotient.scaleRat 240 (ComplexRawQuotient.scaleRat 240 X)) := by
    rw [ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.scaleRat_scaleRat]
    rw [show (240:Rat)*240*240=13824000 by decide +kernel]
  rw [hA,hB,←ComplexRawQuotient.neg_scaleRat 504]
  simp only [sc240,sc504,sc1728,sc3]
  grind only

def nomeLinearDiscriminantResidual (q : Scalar) : Scalar :=
  let p : Scalar := ⟨add one (scaleRat 240 q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  let t : Scalar := ⟨add one (scaleRat (-504) q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  ⟨sub (sub (LocalODE.power p.val 3) (LocalODE.power t.val 2)) (scaleRat 1728 q.val),
    sub_valid (sub_valid (LocalODE.power_valid _ p.property 3) (LocalODE.power_valid _ t.property 2)) (scaleRat_valid q.property)⟩

/-- Exact cancellation of the constant and linear terms in the discriminant polynomials. -/
theorem nomeLinearDiscriminantResidual_polynomial (q : Scalar) :
    (nomeLinearDiscriminantResidual q).val.Equiv
      (add (scaleRat (-81216) (LocalODE.power q.val 2)) (scaleRat 13824000 (LocalODE.power q.val 3))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (nomeLinearDiscriminantResidual q).property)
    (hright := add_valid (scaleRat_valid (LocalODE.power_valid _ q.property 2))
      (scaleRat_valid (LocalODE.power_valid _ q.property 3)))
  let p : Scalar := ⟨add one (scaleRat 240 q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  let t : Scalar := ⟨add one (scaleRat (-504) q.val),add_valid (ofQComplex_valid _) (scaleRat_valid q.property)⟩
  change (ComplexRawQuotient.ofRaw (LocalODE.power p.val 3) (LocalODE.power_valid _ p.property 3)-
    ComplexRawQuotient.ofRaw (LocalODE.power t.val 2) (LocalODE.power_valid _ t.property 2))-
    ComplexRawQuotient.scaleRat 1728 (ComplexRawQuotient.ofRaw q.val q.property)=
    ComplexRawQuotient.scaleRat (-81216) (ComplexRawQuotient.ofRaw (LocalODE.power q.val 2) (LocalODE.power_valid _ q.property 2))+
    ComplexRawQuotient.scaleRat 13824000 (ComplexRawQuotient.ofRaw (LocalODE.power q.val 3) (LocalODE.power_valid _ q.property 3))
  rw [ScalarAlgebra.ofRaw_power _ p.property,ScalarAlgebra.ofRaw_power _ t.property,
    ScalarAlgebra.ofRaw_power _ q.property,ScalarAlgebra.ofRaw_power _ q.property]
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change (1+ComplexRawQuotient.scaleRat 240 Q)^3-(1+ComplexRawQuotient.scaleRat (-504) Q)^2-
    ComplexRawQuotient.scaleRat 1728 Q=
    ComplexRawQuotient.scaleRat (-81216) (Q^2)+ComplexRawQuotient.scaleRat 13824000 (Q^3)
  exact polynomial_algebra Q

/-- A quadratic bound for the actual linear-polynomial discriminant remainder. -/
theorem nomeLinearDiscriminantResidual_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) :
    Small (nomeLinearDiscriminantResidual q).val (163276*r*r) := by
  let q2 := scalarProduct q q
  let q3 := scalarProduct q2 q
  have hq2 := Small.mul q.property q.property hr hr hq hq
  have hR2 : 0≤2*r*r := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hr
  have hq3 := Small.mul q2.property q.property hR2 hr hq2 hq
  have hs2 := negative_scale_small 81216 q2 (2*r*r) (by decide +kernel) hq2
  have hs3 := LocalODE.small_scale (show (0:Rat)≤13824000 by decide +kernel) hq3
  have h := LocalODE.small_add hs2 hs3
  have he : (add (scaleRat (-81216) q2.val) (scaleRat 13824000 q3.val)).Equiv
      (nomeLinearDiscriminantResidual q).val := by
    have hp := nomeLinearDiscriminantResidual_polynomial q
    have hpow : (add (scaleRat (-81216) q2.val) (scaleRat 13824000 q3.val)).Equiv
      (add (scaleRat (-81216) (LocalODE.power q.val 2)) (scaleRat 13824000 (LocalODE.power q.val 3))) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (scaleRat_valid q2.property) (scaleRat_valid q3.property))
        (hright := add_valid (scaleRat_valid (LocalODE.power_valid _ q.property 2)) (scaleRat_valid (LocalODE.power_valid _ q.property 3)))
      let Q := ComplexRawQuotient.ofRaw q.val q.property
      change ComplexRawQuotient.scaleRat (-81216) (Q*Q)+ComplexRawQuotient.scaleRat 13824000 ((Q*Q)*Q)=
        ComplexRawQuotient.scaleRat (-81216) (ComplexRawQuotient.ofRaw (LocalODE.power q.val 2) (LocalODE.power_valid _ q.property 2))+
        ComplexRawQuotient.scaleRat 13824000 (ComplexRawQuotient.ofRaw (LocalODE.power q.val 3) (LocalODE.power_valid _ q.property 3))
      rw [ScalarAlgebra.ofRaw_power _ q.property,ScalarAlgebra.ofRaw_power _ q.property]
      have h2 : Q^2=Q*Q := by grind only
      have h3 : Q^3=(Q*Q)*Q := by grind only
      rw [h2,h3]
    exact equiv_trans (add_valid (scaleRat_valid q2.property) (scaleRat_valid q3.property))
      (add_valid (scaleRat_valid (LocalODE.power_valid _ q.property 2)) (scaleRat_valid (LocalODE.power_valid _ q.property 3)))
      (nomeLinearDiscriminantResidual q).property hpow (equiv_symm hp)
  have hb := Small.congr (add_valid (scaleRat_valid q2.property) (scaleRat_valid q3.property))
    (nomeLinearDiscriminantResidual q).property he h
  apply hb.mono
  have hm := Rat.mul_le_mul_of_nonneg_left hsmall hR2
  have hrate : 81216*(2*r*r)+13824000*(2*(2*r*r)*r)=162432*r*r+55296000*r*r*r := by grind only
  rw [hrate]
  grind only

end ComputableAnalysis.ModularForms
