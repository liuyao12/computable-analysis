import ComputableAnalysis.ModularForms.HorizontalWeightSixNormalization
import ComputableAnalysis.ModularForms.UpperLatticeLambert

/-! Exact normalized weight-six Fourier formula for the actual lattice construction. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual weight-six lattice sum has its normalized Fourier formula,
with the horizontal constant evaluated and the actual weighted Lambert sum. -/
theorem upperWeightSixLatticeSum_normalized_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (upperWeightSixLatticeSum z hz).Equiv
      (scaleRat (2/945) (mul (LocalODE.power geometricPiScalar.val 6)
        (add one (scaleRat (-504) (weightedLambertSum (nome.eval z hz) r 5 hr (by grind only) hq))))) := by
  have hg : 4*r*(2:Rat)^5≤(1:Rat)/2 := by
    rw [show (2:Rat)^5=32 by decide +kernel]
    grind only
  let P : Scalar := ⟨LocalODE.power geometricPiScalar.val 6,LocalODE.power_valid _ geometricPiScalar.property 6⟩
  let W : Scalar := ⟨weightedLambertSum (nome.eval z hz) r 5 hr
    (nomeMomentGuard_lambertLocal r 5 hr hg) hq,
    weightedLambertSum_valid (nome.eval z hz) r 5 hr (nomeMomentGuard_lambertLocal r 5 hr hg) hq
      (nomeMomentGuard_lambertRatio r 5 hr hg)⟩
  have h1 := upperWeightSixLatticeSum_lambert z hz r hr hlocal hq
  have h2 := add_equiv (upperHorizontalWeightSixSum_pi_sixth z hz)
    (equiv_refl (scaleRat (-16/15) (mul P.val W.val)) (scaleRat_valid (mul_valid P.property W.property)))
  have h3 : (add (scaleRat (2/945) P.val) (scaleRat (-16/15) (mul P.val W.val))).Equiv
      (scaleRat (2/945) (mul P.val (add one (scaleRat (-504) W.val)))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (scaleRat_valid P.property) (scaleRat_valid (mul_valid P.property W.property)))
      (hright := scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property))))
    let p := ComplexRawQuotient.ofRaw P.val P.property
    let w := ComplexRawQuotient.ofRaw W.val W.property
    change ComplexRawQuotient.scaleRat (2/945) p+ComplexRawQuotient.scaleRat (-16/15) (p*w)=
      ComplexRawQuotient.scaleRat (2/945) (p*(1+ComplexRawQuotient.scaleRat (-504) w))
    rw [ComplexRawQuotient.mul_add,ComplexRawQuotient.mul_scaleRat]
    have hp : p*(1:ScalarAlgebra.Value)=p := by grind only
    rw [hp,ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_scaleRat,
      show (2/945:Rat)*(-504)=-16/15 by decide +kernel]
  exact equiv_trans (upperWeightSixLatticeSum_valid z hz)
    (add_valid (upperHorizontalWeightSixSum_valid z hz) (scaleRat_valid (mul_valid P.property W.property)))
    (scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property)))) h1
    (equiv_trans (add_valid (upperHorizontalWeightSixSum_valid z hz) (scaleRat_valid (mul_valid P.property W.property)))
      (add_valid (scaleRat_valid P.property) (scaleRat_valid (mul_valid P.property W.property)))
      (scaleRat_valid (mul_valid P.property (add_valid (ofQComplex_valid _) (scaleRat_valid W.property)))) h2 h3)

end ComputableAnalysis.ModularForms
