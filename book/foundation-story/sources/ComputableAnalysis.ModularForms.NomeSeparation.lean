import ComputableAnalysis.ModularForms.Nome
import ComputableAnalysis.ModularForms.ExponentialNegativeSeparation

/-! Separation of the actual upper-half-plane nome from one. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem nomeExponent_negative_realPart (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (- (nomeExponentMap.eval z hu).val.realPart).Pos := by
  obtain ⟨n, hn⟩ := hu
  have hp := (GeometricPiRotation.halfPi_bounds n).1
  have ho := (GeometricPiRotation.halfPi_valid.1 n)
  have hz := (z.property.1 n).2
  change 0 < (z.val.compute n).lo.im at hn
  change 0 ≤ (GeometricPiRotation.halfPi.compute n).hi - (GeometricPiRotation.halfPi.compute n).lo at ho
  change 0 ≤ (z.val.compute n).hi.im - (z.val.compute n).lo.im at hz
  have hmul := QBox.mulRealInterval_of_nonneg
    (a := 4 * (GeometricPiRotation.halfPi.compute n).lo)
    (b := 4 * (GeometricPiRotation.halfPi.compute n).hi)
    (c := (z.val.compute n).lo.im) (d := (z.val.compute n).hi.im)
    (by grind) (by grind) (by grind) (by grind)
  refine ⟨n, ?_⟩
  change 0 < - (QBox.mul
    (QBox.scaleRat 4 ((mulI (ofRealRaw GeometricPiRotation.halfPi)).compute n))
    (z.val.compute n)).hi.re
  simp only [QBox.scaleRat, show (0 : Rat) ≤ 4 by decide, if_true,
    mulI, ofRealRaw, QBox.mul, Rat.mul_zero, Rat.neg_zero]
  rw [hmul]
  simp [QBox.mulRealInterval, min4, max4, minRat, maxRat2]
  have hpos := Rat.mul_pos (a := 4 * (GeometricPiRotation.halfPi.compute n).lo) (by grind) hn
  grind only

theorem nome_ne_one (z : Scalar) (hu : InUpperHalfPlane z.val) :
    ¬ (nome.eval z hu).val.Equiv (ofQComplex QComplex.one) :=
  entireExponential_negative_realPart_ne_one (nomeExponentMap.eval z hu)
    (nomeExponent_negative_realPart z hu)

end ComputableAnalysis.ModularForms
