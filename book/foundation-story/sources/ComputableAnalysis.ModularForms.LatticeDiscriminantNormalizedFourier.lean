import ComputableAnalysis.ModularForms.LatticeInvariantsNormalizedFourier

/-! Exact Fourier normalization of the actual lattice discriminant. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def nomeDiscriminantNumerator (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) : Scalar :=
  let e4 := nomeEisensteinFour q r hr hg hq
  let e6 := nomeEisensteinSix q r hr hg hq
  ⟨sub (LocalODE.power e4.val 3) (LocalODE.power e6.val 2),
    sub_valid (LocalODE.power_valid _ e4.property 3) (LocalODE.power_valid _ e6.property 2)⟩

def nomeModularDiscriminant (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) : Scalar :=
  let d := nomeDiscriminantNumerator q r hr hg hq
  ⟨scaleRat (1/1728) d.val,scaleRat_valid d.property⟩

private theorem scale_sub (r : Rat) (x y : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat r (x-y)=ComplexRawQuotient.scaleRat r x-ComplexRawQuotient.scaleRat r y := by
  change ComplexRawQuotient.scaleRat r (x+ -y)=ComplexRawQuotient.scaleRat r x+ -(ComplexRawQuotient.scaleRat r y)
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one y,
    ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.neg_scaleRat]
  rw [show r*(-1)= -r by grind only]

private theorem discriminant_algebra (P E F : ScalarAlgebra.Value) :
    ((ComplexRawQuotient.scaleRat (4/3) ((P^4)*E))*(ComplexRawQuotient.scaleRat (4/3) ((P^4)*E)))*
      (ComplexRawQuotient.scaleRat (4/3) ((P^4)*E))-
      ComplexRawQuotient.scaleRat 27 ((ComplexRawQuotient.scaleRat (8/27) ((P^6)*F))*
        (ComplexRawQuotient.scaleRat (8/27) ((P^6)*F)))=
      ComplexRawQuotient.scaleRat (64/27) ((P^12)*(E^3-F^2)) := by
  rw [ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.scaleRat_mul_scaleRat,
    ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat]
  rw [show ((4/3:Rat)*(4/3))*(4/3)=64/27 by decide +kernel,
    show (27:Rat)*((8/27)*(8/27))=64/27 by decide +kernel]
  have hE : (((P^4)*E)*((P^4)*E))*((P^4)*E)=(P^12)*(E^3) := by grind only
  have hF : ((P^6)*F)*((P^6)*F)=(P^12)*(F^2) := by grind only
  rw [hE,hF,←scale_sub]
  have h : (P^12)*(E^3)-(P^12)*(F^2)=(P^12)*(E^3-F^2) := by grind only
  rw [h]

/-- Exact Fourier expression for the actual lattice discriminant, with both constants normalized. -/
theorem latticeDiscriminantMap_normalized_fourier_numerator (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (latticeDiscriminantMap.eval z hz).val.Equiv
      (scaleRat (64/27) (mul (LocalODE.power geometricPiScalar.val 12)
        (nomeDiscriminantNumerator (nome.eval z hz) r hr hg hq).val)) := by
  let g2 := latticeG2Map.eval z hz
  let g3 := latticeG3Map.eval z hz
  let e4 := nomeEisensteinFour (nome.eval z hz) r hr hg hq
  let e6 := nomeEisensteinSix (nome.eval z hz) r hr hg hq
  have h2 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := g2.property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 4) e4.property))
    (latticeG2Map_normalized_fourier z hz r hr hg hq)
  have h3 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := g3.property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 6) e6.property))
    (latticeG3Map_normalized_fourier z hz r hr hg hq)
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofQComplex_valid _) (scalarProduct g3 g3).property)
    (hright := scaleRat_valid (scalarProduct g3 g3).property)
    (rationalReal_mul_scale 27 (scalarProduct g3 g3))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeDiscriminantMap.eval z hz).property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 12)
      (nomeDiscriminantNumerator (nome.eval z hz) r hr hg hq).property))
  let A := ComplexRawQuotient.ofRaw g2.val g2.property
  let B := ComplexRawQuotient.ofRaw g3.val g3.property
  let E := ComplexRawQuotient.ofRaw e4.val e4.property
  let F := ComplexRawQuotient.ofRaw e6.val e6.property
  let P := ComplexRawQuotient.ofRaw geometricPiScalar.val geometricPiScalar.property
  change A=ComplexRawQuotient.scaleRat (4/3)
    (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4)*E) at h2
  change B=ComplexRawQuotient.scaleRat (8/27)
    (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 6) (LocalODE.power_valid _ geometricPiScalar.property 6)*F) at h3
  rw [ScalarAlgebra.ofRaw_power] at h2 h3
  change ComplexRawQuotient.ofQComplex ⟨27,0⟩*(B*B)=ComplexRawQuotient.scaleRat 27 (B*B) at hc
  change (A*A)*A+ -(ComplexRawQuotient.ofQComplex ⟨27,0⟩*(B*B))=
    ComplexRawQuotient.scaleRat (64/27)
      (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 12) (LocalODE.power_valid _ geometricPiScalar.property 12)*
        (ComplexRawQuotient.ofRaw (LocalODE.power e4.val 3) (LocalODE.power_valid _ e4.property 3)-
          ComplexRawQuotient.ofRaw (LocalODE.power e6.val 2) (LocalODE.power_valid _ e6.property 2)))
  rw [hc,ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power]
  change (A*A)*A-ComplexRawQuotient.scaleRat 27 (B*B)=
    ComplexRawQuotient.scaleRat (64/27) ((P^12)*(E^3-F^2))
  rw [h2,h3]
  exact discriminant_algebra P E F

/-- The actual lattice discriminant equals the normalized Fourier discriminant times the geometric-pi factor. -/
theorem latticeDiscriminantMap_normalized_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (latticeDiscriminantMap.eval z hz).val.Equiv
      (scaleRat 4096 (mul (LocalODE.power geometricPiScalar.val 12)
        (nomeModularDiscriminant (nome.eval z hz) r hr hg hq).val)) := by
  let p : Scalar := ⟨LocalODE.power geometricPiScalar.val 12,LocalODE.power_valid _ geometricPiScalar.property 12⟩
  let d := nomeDiscriminantNumerator (nome.eval z hz) r hr hg hq
  have he : (scaleRat (64/27) (mul p.val d.val)).Equiv
      (scaleRat 4096 (mul p.val (scaleRat (1/1728) d.val))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (mul_valid p.property d.property))
      (hright := scaleRat_valid (mul_valid p.property (scaleRat_valid d.property)))
    let P := ComplexRawQuotient.ofRaw p.val p.property
    let D := ComplexRawQuotient.ofRaw d.val d.property
    change ComplexRawQuotient.scaleRat (64/27) (P*D)=
      ComplexRawQuotient.scaleRat 4096 (P*ComplexRawQuotient.scaleRat (1/1728) D)
    rw [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat,
      show (4096:Rat)*(1/1728)=64/27 by decide +kernel]
  exact equiv_trans (latticeDiscriminantMap.eval z hz).property (scaleRat_valid (mul_valid p.property d.property))
    (scaleRat_valid (mul_valid p.property (scaleRat_valid d.property)))
    (latticeDiscriminantMap_normalized_fourier_numerator z hz r hr hg hq) he

end ComputableAnalysis.ModularForms
