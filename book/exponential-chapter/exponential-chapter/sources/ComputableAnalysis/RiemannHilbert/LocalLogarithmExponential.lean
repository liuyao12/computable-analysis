import ComputableAnalysis.RiemannHilbert.LocalLogarithmUniform
import ComputableAnalysis.RiemannHilbert.ExponentialODEUniqueness
import ComputableAnalysis.RiemannHilbert.MatrixCoordinateRemainders
import ComputableAnalysis.RiemannHilbert.ScalarNeumannInverse

/-! The actual entire exponential of the actual Taylor logarithm is one plus
its argument. Both sides have constructed uniform ODE remainders; finite
segment uniqueness proves the identity over arbitrary represented inputs. -/
namespace ComputableAnalysis.RiemannHilbert.LocalLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
set_option maxHeartbeats 1500000

private def I : ValueMap (Fiber 1) (Fiber 1) := ValueMap.identity
private theorem hI : IsLinear I := IsLinear.identity 1
private def S : QPos := ⟨5, by decide⟩

def exponential (z : Scalar) : Scalar :=
  Fiber.coordinate ((MatrixExponential.value I hI z).eval ScalarNeumannInverse.unit) 0

theorem exponential_congr (z w : Scalar) (hzw : z.val.Equiv w.val) :
    (exponential z).val.Equiv (exponential w).val :=
  MatrixExponential.value_congr I I hI hI (fun _ => Setoid.refl _) z w hzw
    ScalarNeumannInverse.unit ScalarNeumannInverse.unit (Setoid.refl _) 0

private theorem image (z : Scalar) (hz : interior radius.val z) : interior S.val (function.eval z hz) :=
  ⟨4, by decide, by decide, value_bound z hz⟩

private def f : UniformSegment.Field (n := 1) (interior radius.val) :=
  fun z hz => (MatrixExponential.value I hI (function.eval z hz)).eval ScalarNeumannInverse.unit

private def g : UniformSegment.Field (n := 1) (interior radius.val) :=
  fun z _ => ⟨fun _ => (onePlus z).val, fun _ => (onePlus z).property⟩

private def A : UniformSegment.OperatorField (n := 1) (interior radius.val) :=
  fun z hz => Fiber.scaleMap (derivativeValue z hz)

private def delta : QPos → QPos :=
  LinearField.coordinateDelta 9 (MatrixExponential.discDerivativeBound I S) (by decide)
    (MatrixExponential.discDerivativeBound_nonneg I S) (MatrixExponential.discDelta I S) uniformDelta

private theorem f_remainder (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (delta eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder A f w z hw hz) (eps.val*H.val) := by
  have hb := LinearField.coordinate_uniform_remainder (MatrixExponential.discField I hI S)
    (MatrixExponential.discSlope I hI S) function.eval derivativeValue image
    9 (MatrixExponential.discDerivativeBound I S) (by decide) (MatrixExponential.discDerivativeBound_nonneg I S)
    (MatrixExponential.discSlope_bound I hI S) lipschitz
    (MatrixExponential.discDelta I S) uniformDelta (MatrixExponential.disc_uniform_remainder I hI S)
    uniform_remainder eps H w z hw hz hH hzw 1 (by decide) ScalarNeumannInverse.unit ScalarNeumannInverse.unit_bound
  simpa only [Rat.mul_one, LinearField.operatorRemainder, LinearField.coordinateField,
    LinearField.coordinateSlope, MatrixExponential.discField, MatrixExponential.discSlope,
    ValueMap.followedBy, I, ValueMap.identity, id_eq, UniformSegment.remainder, A, f] using hb

private theorem g_remainder_zero (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z) :
    UniformSegment.remainder A g w z hw hz ≈ Fiber.zero 1 := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (onePlus w).property (derivativeValue w hw).property) (hright := ofQComplex_valid _)
    (derivativeValue_inverse w hw)
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (UniformSegment.remainder A g w z hw hz).property i) (hright := ofQComplex_valid _)
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let D := ComplexRawQuotient.ofRaw (derivativeValue w hw).val (derivativeValue w hw).property
  change (1+W)*D=1 at hi
  change ((1+Z)-(1+W))-(Z-W)*(D*(1+W))=0
  grind only

/-- Exact branch identity for the constructed logarithm, with all quantitative
choices made inside the proof. -/
theorem exponential_log (z : Scalar) (hz : interior radius.val z) :
    (exponential (function.eval z hz)).val.Equiv (onePlus z).val := by
  let p : Scalar := ⟨zero, ofQComplex_valid _⟩
  have hp : interior radius.val p := interior_zero _ radius.property
  have hdisp : Small (AffineSegment.displacement p z).val radius.val :=
    Small.congr z.property (AffineSegment.displacement p z).property
      (equiv_symm (MatrixExponential.offset_zero z)) (interior_bound radius.val z hz)
  have hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw := by
    intro z w hz hw hzw
    exact MatrixExponential.value_congr I I hI hI (fun _ => Setoid.refl _) _ _
      (function.eval_congr z w hz hw hzw) _ _ (Setoid.refl _)
  have hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw := by
    intro z w _ _ hzw i
    exact add_equiv (equiv_refl _ (ofQComplex_valid _)) hzw
  have hi : f p hp ≈ g p hp := by
    have h1 := Setoid.trans (MatrixExponential.value_congr I I hI hI (fun _ => Setoid.refl _)
      (function.eval p hp) p initial _ _ (Setoid.refl _)) (MatrixExponential.value_initial I hI ScalarNeumannInverse.unit)
    exact Setoid.trans h1 (fun _ => equiv_symm (add_zero_equiv one (ofQComplex_valid _)))
  have hfB : ∀ z hz, CoordinateBound (f z hz) (MatrixExponential.discValueBound I S) := by
    intro z hz
    simpa only [Rat.mul_one, MatrixExponential.discField, f] using MatrixExponential.discField_bound I hI S _ (image z hz)
      1 (by decide) ScalarNeumannInverse.unit ScalarNeumannInverse.unit_bound
  have hgB : ∀ z hz, CoordinateBound (g z hz) (1+radius.val) := by
    intro z hz i
    exact small_add (ScalarNeumannInverse.unit_bound 0) (interior_bound radius.val z hz)
  have hAb : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((A z hz).eval x) (8*E) := by
    intro z hz E hE x hx
    simpa only [A, Fiber.scaleMap, show (2 : Rat)*4=8 by decide +kernel] using
      bound_scale (by decide) hE (derivative_bound z hz) hx
  have he := UniformSegment.equal (interior radius.val) p z hp hz
    (MatrixExponential.disc_affine_mem radius p z hp hz) radius hdisp A f g
    8 (MatrixExponential.discValueBound I S) (1+radius.val) (by decide) (by decide +kernel)
    (MatrixExponential.discValueBound_nonneg I S) (by decide +kernel) hfcongr hgcongr hi hfB hgB
    (fun _ _ => Fiber.scaleMap_linear _) hAb delta (fun eps => eps) f_remainder
    (by
      intro eps H w z hw hz _ _
      exact bound_congr (Setoid.symm (g_remainder_zero w z hw hz))
        (bound_zero (eps.val*H.val) (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property))))
  exact he 0

end ComputableAnalysis.RiemannHilbert.LocalLogarithm
