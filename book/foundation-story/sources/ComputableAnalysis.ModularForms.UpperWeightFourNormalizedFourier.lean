import ComputableAnalysis.ModularForms.HorizontalWeightFourNormalization
import ComputableAnalysis.ModularForms.UpperLatticeLambert

/-! Exact normalized weight-four Fourier formula for the actual lattice construction. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual weight-four lattice sum has its normalized Fourier formula,
with the horizontal constant evaluated and the actual weighted Lambert sum. -/
theorem upperWeightFourLatticeSum_normalized_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 32*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (upperWeightFourLatticeSum z hz).Equiv
      (scaleRat (1/45) (mul (LocalODE.power geometricPiScalar.val 4)
        (add one (scaleRat 240 (weightedLambertSum (nome.eval z hz) r 3 hr (by grind only) hq))))) := by
  have hg : 4*r*(2:Rat)^3≤(1:Rat)/2 := by
    rw [show (2:Rat)^3=8 by decide +kernel]
    grind only
  let P : Scalar := ⟨LocalODE.power geometricPiScalar.val 4,LocalODE.power_valid _ geometricPiScalar.property 4⟩
  let W : Scalar := ⟨weightedLambertSum (nome.eval z hz) r 3 hr
    (nomeMomentGuard_lambertLocal r 3 hr hg) hq,
    weightedLambertSum_valid (nome.eval z hz) r 3 hr (nomeMomentGuard_lambertLocal r 3 hr hg) hq
      (nomeMomentGuard_lambertRatio r 3 hr hg)⟩
  have h1 := upperWeightFourLatticeSum_lambert z hz r hr hlocal hq
  have h2 := add_equiv (upperHorizontalWeightFourSum_pi_fourth z hz)
    (equiv_refl (scaleRat (16/3) (mul P.val W.val)) (scaleRat_valid (mul_valid P.property W.property)))
  have h3 : (add (scaleRat (1/45) P.val) (scaleRat (16/3) (mul P.val W.val))).Equiv
      (scaleRat (1/45) (mul P.val (add one (scaleRat 240 W.val)))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (scaleRat_valid P.property) (scaleRat_valid (mul_valid P.property W.property)))
      (hright := scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property))))
    let p := ComplexRawQuotient.ofRaw P.val P.property
    let w := ComplexRawQuotient.ofRaw W.val W.property
    change ComplexRawQuotient.scaleRat (1/45) p+ComplexRawQuotient.scaleRat (16/3) (p*w)=
      ComplexRawQuotient.scaleRat (1/45) (p*(1+ComplexRawQuotient.scaleRat 240 w))
    rw [ComplexRawQuotient.mul_add,ComplexRawQuotient.mul_scaleRat]
    have hp : p*(1:ScalarAlgebra.Value)=p := by grind only
    rw [hp,ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_scaleRat,
      show (1/45:Rat)*240=16/3 by decide +kernel]
  exact equiv_trans (upperWeightFourLatticeSum_valid z hz)
    (add_valid (upperHorizontalWeightFourSum_valid z hz) (scaleRat_valid (mul_valid P.property W.property)))
    (scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property)))) h1
    (equiv_trans (add_valid (upperHorizontalWeightFourSum_valid z hz) (scaleRat_valid (mul_valid P.property W.property)))
      (add_valid (scaleRat_valid P.property) (scaleRat_valid (mul_valid P.property W.property)))
      (scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property)))) h2 h3)

end ComputableAnalysis.ModularForms
