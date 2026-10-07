import ComputableAnalysis.ModularForms.UpperPositiveRowsLambert
import ComputableAnalysis.ModularForms.UpperLatticeIteratedRows

/-! Full actual lattice sums expressed as their horizontal row and weighted Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem scale_twice (x : Scalar) (a b : Rat) (he : 2*a=b) :
    (scaleRat 2 (scaleRat a x.val)).Equiv (scaleRat b x.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (scaleRat_valid x.property)) (hright := scaleRat_valid x.property)
  change ComplexRawQuotient.scaleRat 2 (ComplexRawQuotient.scaleRat a (ComplexRawQuotient.ofRaw x.val x.property))=
    ComplexRawQuotient.scaleRat b (ComplexRawQuotient.ofRaw x.val x.property)
  rw [ComplexRawQuotient.scaleRat_scaleRat,he]

/-- The actual weight-4 lattice sum has its full Lambert expansion, with the
horizontal constant retained as its constructed row sum. -/
theorem upperWeightFourLatticeSum_lambert (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 32*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) :
    (upperWeightFourLatticeSum z hz).Equiv
      (add (upperHorizontalWeightFourSum z hz)
        (scaleRat (16/3) (mul (LocalODE.power geometricPiScalar.val 4)
          (weightedLambertSum (nome.eval z hz) r 3 hr (by grind only) hq)))) := by
  have hg : 4*r*(2:Rat)^3≤(1:Rat)/2 := by
    have hp : (2:Rat)^3=8 := by decide +kernel
    rw [hp]
    grind only
  let W : Scalar := ⟨weightedLambertSum (nome.eval z hz) r 3 hr
    (nomeMomentGuard_lambertLocal r 3 hr hg) hq,
    weightedLambertSum_valid (nome.eval z hz) r 3 hr
      (nomeMomentGuard_lambertLocal r 3 hr hg) hq (nomeMomentGuard_lambertRatio r 3 hr hg)⟩
  let X : Scalar := ⟨mul (LocalODE.power geometricPiScalar.val 4) W.val,
    mul_valid (LocalODE.power_valid _ geometricPiScalar.property 4) W.property⟩
  have hp := upperPositiveWeightFourRowsSum_lambert z hz r hr hlocal hq
  have hs := scaleRat_equiv (r := (2:Rat)) hp
  have hd := scale_twice X (8/3) (16/3) (by decide +kernel)
  have hrows := equiv_trans (scaleRat_valid (upperPositiveWeightFourRowsSum_valid z hz))
    (scaleRat_valid (scaleRat_valid X.property)) (scaleRat_valid X.property) hs hd
  have hsum := add_equiv (equiv_refl _ (upperHorizontalWeightFourSum_valid z hz)) hrows
  exact equiv_trans (upperWeightFourLatticeSum_valid z hz)
    (add_valid (upperHorizontalWeightFourSum_valid z hz) (scaleRat_valid (upperPositiveWeightFourRowsSum_valid z hz)))
    (add_valid (upperHorizontalWeightFourSum_valid z hz) (scaleRat_valid X.property))
    (upperWeightFourLatticeSum_iteratedRows z hz) hsum

/-- The actual weight-6 lattice sum has its full Lambert expansion, with the
horizontal constant retained as its constructed row sum. -/
theorem upperWeightSixLatticeSum_lambert (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 128*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) :
    (upperWeightSixLatticeSum z hz).Equiv
      (add (upperHorizontalWeightSixSum z hz)
        (scaleRat (-16/15) (mul (LocalODE.power geometricPiScalar.val 6)
          (weightedLambertSum (nome.eval z hz) r 5 hr (by grind only) hq)))) := by
  have hg : 4*r*(2:Rat)^5≤(1:Rat)/2 := by
    have hp : (2:Rat)^5=32 := by decide +kernel
    rw [hp]
    grind only
  let W : Scalar := ⟨weightedLambertSum (nome.eval z hz) r 5 hr
    (nomeMomentGuard_lambertLocal r 5 hr hg) hq,
    weightedLambertSum_valid (nome.eval z hz) r 5 hr
      (nomeMomentGuard_lambertLocal r 5 hr hg) hq (nomeMomentGuard_lambertRatio r 5 hr hg)⟩
  let X : Scalar := ⟨mul (LocalODE.power geometricPiScalar.val 6) W.val,
    mul_valid (LocalODE.power_valid _ geometricPiScalar.property 6) W.property⟩
  have hp := upperPositiveWeightSixRowsSum_lambert z hz r hr hlocal hq
  have hs := scaleRat_equiv (r := (2:Rat)) hp
  have hd := scale_twice X (-8/15) (-16/15) (by decide +kernel)
  have hrows := equiv_trans (scaleRat_valid (upperPositiveWeightSixRowsSum_valid z hz))
    (scaleRat_valid (scaleRat_valid X.property)) (scaleRat_valid X.property) hs hd
  have hsum := add_equiv (equiv_refl _ (upperHorizontalWeightSixSum_valid z hz)) hrows
  exact equiv_trans (upperWeightSixLatticeSum_valid z hz)
    (add_valid (upperHorizontalWeightSixSum_valid z hz) (scaleRat_valid (upperPositiveWeightSixRowsSum_valid z hz)))
    (add_valid (upperHorizontalWeightSixSum_valid z hz) (scaleRat_valid X.property))
    (upperWeightSixLatticeSum_iteratedRows z hz) hsum

end ComputableAnalysis.ModularForms
