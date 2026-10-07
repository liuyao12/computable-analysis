import ComputableAnalysis.ModularForms.UpperWeightFourNormalizedFourier
import ComputableAnalysis.ModularForms.UpperWeightSixNormalizedFourier
import ComputableAnalysis.ModularForms.LatticeDiscriminant

/-! Actual normalized Fourier values and their agreement with lattice invariants. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem local_guard (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) : 4*r≤(1:Rat)/2 := by grind only
private theorem ratio_four (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) :
    weightedLambertRatio r 3≤(1:Rat)/2 := by
  unfold weightedLambertRatio
  rw [show (2:Rat)^3=8 by decide +kernel]
  grind only
private theorem ratio_six (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) :
    weightedLambertRatio r 5≤(1:Rat)/2 := by
  unfold weightedLambertRatio
  rw [show (2:Rat)^5=32 by decide +kernel]
  grind only

def nomeEisensteinFour (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) : Scalar :=
  let w := weightedLambertSum q r 3 hr (local_guard r hr hg) hq
  ⟨add one (scaleRat 240 w),add_valid (ofQComplex_valid _)
    (scaleRat_valid (weightedLambertSum_valid q r 3 hr (local_guard r hr hg) hq (ratio_four r hr hg)))⟩

def nomeEisensteinSix (q : Scalar) (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2)
    (hq : Small q.val r) : Scalar :=
  let w := weightedLambertSum q r 5 hr (local_guard r hr hg) hq
  ⟨add one (scaleRat (-504) w),add_valid (ofQComplex_valid _)
    (scaleRat_valid (weightedLambertSum_valid q r 5 hr (local_guard r hr hg) hq (ratio_six r hr hg)))⟩

private theorem rational_scaled (r s : Rat) (x : Scalar) :
    (mul (ofQComplex ⟨r,0⟩) (scaleRat s x.val)).Equiv (scaleRat (r*s) x.val) := by
  have h := rationalReal_mul_scale r ⟨scaleRat s x.val,scaleRat_valid x.property⟩
  have he : (scaleRat r (scaleRat s x.val)).Equiv (scaleRat (r*s) x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (scaleRat_valid x.property)) (hright := scaleRat_valid x.property)
    change ComplexRawQuotient.scaleRat r (ComplexRawQuotient.scaleRat s (ComplexRawQuotient.ofRaw x.val x.property))=
      ComplexRawQuotient.scaleRat (r*s) (ComplexRawQuotient.ofRaw x.val x.property)
    exact ComplexRawQuotient.scaleRat_scaleRat r s _
  exact equiv_trans (mul_valid (ofQComplex_valid _) (scaleRat_valid x.property))
    (scaleRat_valid (scaleRat_valid x.property)) (scaleRat_valid x.property) h he

/-- The actual lattice invariant has its normalized weight-four Fourier value. -/
theorem latticeG2Map_normalized_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (latticeG2Map.eval z hz).val.Equiv
      (scaleRat (4/3) (mul (LocalODE.power geometricPiScalar.val 4)
        (nomeEisensteinFour (nome.eval z hz) r hr hg hq).val)) := by
  let e := nomeEisensteinFour (nome.eval z hz) r hr hg hq
  let p : Scalar := ⟨LocalODE.power geometricPiScalar.val 4,LocalODE.power_valid _ geometricPiScalar.property 4⟩
  have h4 : 32*r≤(1:Rat)/2 := by grind only
  have h := mul_equiv (ofQComplex_valid ⟨60,0⟩) (ofQComplex_valid ⟨60,0⟩) (upperWeightFourLatticeSum_valid z hz)
    (scaleRat_valid (mul_valid p.property e.property)) (equiv_refl _ (ofQComplex_valid ⟨60,0⟩))
    (upperWeightFourLatticeSum_normalized_fourier z hz r hr h4 hq)
  have he := rational_scaled 60 (1/45) (scalarProduct p e)
  rw [show (60:Rat)*(1/45)=4/3 by decide +kernel] at he
  exact equiv_trans (latticeG2Map.eval z hz).property
    (mul_valid (ofQComplex_valid ⟨60,0⟩) (scaleRat_valid (scalarProduct p e).property))
    (scaleRat_valid (scalarProduct p e).property) h he

/-- The actual lattice invariant has its normalized weight-six Fourier value. -/
theorem latticeG3Map_normalized_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (latticeG3Map.eval z hz).val.Equiv
      (scaleRat (8/27) (mul (LocalODE.power geometricPiScalar.val 6)
        (nomeEisensteinSix (nome.eval z hz) r hr hg hq).val)) := by
  let e := nomeEisensteinSix (nome.eval z hz) r hr hg hq
  let p : Scalar := ⟨LocalODE.power geometricPiScalar.val 6,LocalODE.power_valid _ geometricPiScalar.property 6⟩
  have h := mul_equiv (ofQComplex_valid ⟨140,0⟩) (ofQComplex_valid ⟨140,0⟩) (upperWeightSixLatticeSum_valid z hz)
    (scaleRat_valid (mul_valid p.property e.property)) (equiv_refl _ (ofQComplex_valid ⟨140,0⟩))
    (upperWeightSixLatticeSum_normalized_fourier z hz r hr hg hq)
  have he := rational_scaled 140 (2/945) (scalarProduct p e)
  rw [show (140:Rat)*(2/945)=8/27 by decide +kernel] at he
  exact equiv_trans (latticeG3Map.eval z hz).property
    (mul_valid (ofQComplex_valid ⟨140,0⟩) (scaleRat_valid (scalarProduct p e).property))
    (scaleRat_valid (scalarProduct p e).property) h he

end ComputableAnalysis.ModularForms
