import ComputableAnalysis.ModularForms.LatticeJInvariant

/-! Modular invariance of the actual j evaluator at justified domain points. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

theorem latticeJMap_action_mem (g : SL2Z) (z : Scalar) (hz : latticeJMap.domain z) :
    latticeJMap.domain (fractionalLinear g z hz.1) := by
  let w := fractionalLinear g z hz.1
  have hw := fractionalLinear_mem g z hz.1
  let D := latticeDiscriminantMap.eval z hz.1
  let E := latticeDiscriminantMap.eval w hw
  let d : Scalar := ⟨integerAffine g.c g.d z.val,integerAffine_valid _ _ z.property⟩
  have hdn : NonzeroBoxSearch.Nonzero d := denominator_nonzero g z hz.1
  let r := RepresentedReciprocal.inverse d hdn
  let q := RepresentedReciprocal.inverse D hz.2
  let invE : Scalar := ⟨mul (LocalODE.power r.val 12) q.val,
    mul_valid (LocalODE.power_valid r.val r.property 12) q.property⟩
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := E.property)
    (hright := mul_valid (LocalODE.power_valid d.val d.property 12) D.property)
    (latticeDiscriminantMap_action g z hz.1)
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid d.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse d hdn)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid D.property q.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse D hz.2)
  have hprod : (mul E.val invE.val).Equiv (ofQComplex QComplex.one) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid E.property invE.property) (hright := ofQComplex_valid _)
    let DV := ComplexRawQuotient.ofRaw D.val D.property
    let EV := ComplexRawQuotient.ofRaw E.val E.property
    let FV := ComplexRawQuotient.ofRaw d.val d.property
    let RV := ComplexRawQuotient.ofRaw r.val r.property
    let QV := ComplexRawQuotient.ofRaw q.val q.property
    change EV=ComplexRawQuotient.ofRaw (LocalODE.power d.val 12) (LocalODE.power_valid d.val d.property 12)*DV at hd
    rw [ScalarAlgebra.ofRaw_power] at hd
    change EV=FV^12*DV at hd
    change FV*RV=1 at hr
    change DV*QV=1 at hq
    change EV*(ComplexRawQuotient.ofRaw (LocalODE.power r.val 12) (LocalODE.power_valid r.val r.property 12)*QV)=1
    rw [ScalarAlgebra.ofRaw_power]
    change EV*(RV^12*QV)=1
    grind only
  exact ⟨hw,RepresentedReciprocal.nonzero_of_inverse E invE hprod⟩

theorem latticeJMap_action (g : SL2Z) (z : Scalar) (hz : latticeJMap.domain z)
    (hw : latticeJMap.domain (fractionalLinear g z hz.1)) :
    (latticeJMap.eval (fractionalLinear g z hz.1) hw).val.Equiv (latticeJMap.eval z hz).val := by
  let w := fractionalLinear g z hz.1
  let D := latticeDiscriminantMap.eval z hz.1
  let E := latticeDiscriminantMap.eval w hw.1
  let N := latticeG2CubeMap.eval z hz.1
  let M := latticeG2CubeMap.eval w hw.1
  let R := RepresentedReciprocal.inverse D hz.2
  let S := RepresentedReciprocal.inverse E hw.2
  let F := LocalODE.power (integerAffine g.c g.d z.val) 12
  have hF : F.Valid := LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 12
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := E.property) (hright := mul_valid hF D.property) (latticeDiscriminantMap_action g z hz.1)
  have hn := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := M.property) (hright := mul_valid hF N.property) (latticeG2CubeMap_action g z hz.1)
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid D.property R.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse D hz.2)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid E.property S.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse E hw.2)
  let DV := ComplexRawQuotient.ofRaw D.val D.property
  let EV := ComplexRawQuotient.ofRaw E.val E.property
  let NV := ComplexRawQuotient.ofRaw N.val N.property
  let MV := ComplexRawQuotient.ofRaw M.val M.property
  let RV := ComplexRawQuotient.ofRaw R.val R.property
  let SV := ComplexRawQuotient.ofRaw S.val S.property
  let FV := ComplexRawQuotient.ofRaw F hF
  change EV=FV*DV at hd
  change MV=FV*NV at hn
  change DV*RV=1 at hr
  change EV*SV=1 at hs
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeJMap.eval w hw).property) (hright := (latticeJMap.eval z hz).property)
  change SV*(ComplexRawQuotient.ofQComplex ⟨1728,0⟩*MV)=
    RV*(ComplexRawQuotient.ofQComplex ⟨1728,0⟩*NV)
  grind only

theorem latticeJMap_invariant (g : SL2Z) (z : Scalar) (hz : latticeJMap.domain z) :
    (latticeJMap.eval (fractionalLinear g z hz.1) (latticeJMap_action_mem g z hz)).val.Equiv
      (latticeJMap.eval z hz).val :=
  latticeJMap_action g z hz (latticeJMap_action_mem g z hz)

end ComputableAnalysis.ModularForms
