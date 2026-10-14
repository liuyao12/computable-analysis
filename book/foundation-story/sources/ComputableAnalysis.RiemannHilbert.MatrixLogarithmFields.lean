import ComputableAnalysis.RiemannHilbert.MatrixLogarithmResolvent
import ComputableAnalysis.RiemannHilbert.FiniteMatrixBounds

/-! Matrix fields of the actual near-identity Taylor sum. Genuine entrywise
holomorphic witnesses, normalization, the exact matrix resolvent derivative,
uniform derivative bounds and invariance under represented names are proved. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}
set_option maxHeartbeats 1000000

theorem small_of_basis (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (B : Rat) (hB : 0 ≤ B) (hb : ∀ i, CoordinateBound (E.eval (Fiber.basis i)) B)
    (hbudget : 2*(n : Rat)*B ≤ contraction) : SmallOperator E := by
  intro C hC x hx i
  exact (ValueMap.linear_bound_of_basis E hE B hB hb x C hC hx i).mono
    (Rat.mul_le_mul_of_nonneg_right hbudget hC)

theorem parameterValue_congr (E F : ValueMap (Fiber n) (Fiber n)) (hsmallE : SmallOperator E) (hsmallF : SmallOperator F)
    (hEF : E.Equiv F) (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w)
    (hzw : z.val.Equiv w.val) (x y : Fiber n) (hxy : x ≈ y) :
    (parameterValue E hsmallE z hz).eval x ≈ (parameterValue F hsmallF w hw).eval y :=
  VectorSeries.value_congr _ _ z w (fun k => Setoid.trans ((coefficientMap E k).congr hxy) (coefficientMap_congr E F hEF k y)) hzw
    (2*1*initialBound x) contraction radius.val (2*1*initialBound y) contraction radius.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)) (by decide +kernel) (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg y)) (by decide +kernel) (by decide +kernel)
    (operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmallE) x (LocalSystem.initialBound_valid x))
    (operatorCoefficient_bound (coefficientMap F) 1 contraction _ (LocalSystem.initialBound_nonneg y)
      (coefficientMap_majorant F hsmallF) y (LocalSystem.initialBound_valid y))
    (interior_bound radius.val z hz) (interior_bound radius.val w hw) (by decide +kernel) (by decide +kernel)

theorem value_congr (E F : ValueMap (Fiber n) (Fiber n)) (hsmallE : SmallOperator E) (hsmallF : SmallOperator F)
    (hEF : E.Equiv F) : (value E hsmallE).Equiv (value F hsmallF) :=
  fun x => parameterValue_congr E F hsmallE hsmallF hEF unit unit unit_mem unit_mem (equiv_refl _ unit.property) x x (Setoid.refl _)

theorem coefficientMap_zero (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) : (coefficientMap E 0).eval x ≈ Fiber.zero n := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((coefficientMap E 0).eval x).property i) (hright := ofQComplex_valid _)
  change ComplexRawQuotient.scaleRat 0 (1 : ScalarAlgebra.Value)*ComplexRawQuotient.ofRaw (x.val i) (x.property i)=0
  rw [ComplexRawQuotient.scaleRat_zeroScalar]
  grind only

theorem coefficientMap_one (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) : (coefficientMap E 1).eval x ≈ E.eval x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((coefficientMap E 1).eval x).property i) (hright := (E.eval x).property i)
  have hc : LocalLogarithm.coefficientRat 1=1 := by decide +kernel
  change ComplexRawQuotient.scaleRat (LocalLogarithm.coefficientRat 1) (1 : ScalarAlgebra.Value)*
    ComplexRawQuotient.ofRaw ((E.eval x).val i) ((E.eval x).property i)=ComplexRawQuotient.ofRaw ((E.eval x).val i) ((E.eval x).property i)
  rw [hc,ComplexRawQuotient.scaleRat_one]
  grind only

theorem parameterValue_initial (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) :
    (parameterValue E hsmall ⟨zero,ofQComplex_valid _⟩ (interior_zero radius.val radius.property)).Equiv (ValueMap.zeroBetween n n) := by
  intro x i
  have hs := BoundedSeries.seriesMap_initial (fun k => ((coefficientMap E k).eval x).val i)
    (fun k => ((coefficientMap E k).eval x).property i) (2*1*initialBound x) contraction radius.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)) (by decide +kernel) (by decide +kernel)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x) k i) (by decide +kernel)
  exact equiv_trans (((parameterValue E hsmall ⟨zero,ofQComplex_valid _⟩ (interior_zero radius.val radius.property)).eval x).property i)
    (((coefficientMap E 0).eval x).property i) (ofQComplex_valid _) hs (coefficientMap_zero E x i)

def field (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) : LinearField.Field (n := n) (m := n) (interior radius.val) :=
  parameterValue E hsmall

theorem field_congr (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (hzw : z.val.Equiv w.val) :
    (field E hsmall z hz).Equiv (field E hsmall w hw) :=
  fun x => parameterValue_congr E E hsmall hsmall (ValueMap.equiv_refl E) z w hz hw hzw x x (Setoid.refl _)

def field_holomorphic (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) :
    LinearField.MatrixHolomorphic (field E hsmall) (vector E hsmall (Fiber.zero n)).domain_congr (field_congr E hsmall) :=
  fun i j => (vector_holomorphic E hsmall (Fiber.basis i)).coordinates j

theorem field_derivative_resolvent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hM : LinearField.MatrixHolomorphic (field E hsmall) (vector E hsmall (Fiber.zero n)).domain_congr (field_congr E hsmall))
    (z : Scalar) (hz : interior radius.val z) :
    (LinearField.derivativeField hM z hz).Equiv (E.followedBy (resolvent E hE hsmall z hz)) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (LinearField.derivativeField_linear hM z hz)
    (IsLinear.followedBy hE (resolvent_linear E hE hsmall z hz))).2
  intro i
  exact Setoid.trans (LinearField.derivativeField_unique hM (field_holomorphic E hsmall) z hz (Fiber.basis i))
    (Setoid.trans (ValueMap.ofColumns_basis (LinearField.derivativeColumn (field_holomorphic E hsmall) z hz) i)
      (vector_derivative_resolvent E hE hsmall (Fiber.basis i) (vector_holomorphic E hsmall (Fiber.basis i)) z hz))

theorem resolvent_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((resolvent E hE hsmall z hz).eval x) (4*B) :=
  Neumann.valueMap_bound (deviation E z) resolventContraction (by decide +kernel) (by decide +kernel)
    (deviation_bound E hsmall z hz) B hB x hx

theorem vector_derivative_bound (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (x : Fiber n) (hF : DomainVectorFunctions.Holomorphic (vector E hsmall x)) (z : Scalar) (hz : interior radius.val z)
    (B : Rat) (hB : 0 ≤ B) (hx : CoordinateBound x B) :
    CoordinateBound (DomainVectorFunctions.derivative (vector E hsmall x) hF z hz) ((1/8 : Rat)*B) := by
  have hb := resolvent_bound E hE hsmall z hz (contraction*B) (Rat.mul_nonneg (by decide +kernel) hB) (E.eval x) (hsmall B hB x hx)
  have he : 4*(contraction*B)=(1/8 : Rat)*B := by
    have hc : 4*contraction=(1/8 : Rat) := by decide +kernel
    rw [← Rat.mul_assoc,hc]
  rw [he] at hb
  exact bound_congr (Setoid.symm (vector_derivative_resolvent E hE hsmall x hF z hz)) hb

theorem resolvent_congr (E F : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hF : IsLinear F)
    (hsmallE : SmallOperator E) (hsmallF : SmallOperator F) (hEF : E.Equiv F)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (hzw : z.val.Equiv w.val) :
    (resolvent E hE hsmallE z hz).Equiv (resolvent F hF hsmallF w hw) :=
  Neumann.inverse_congr (identityPlus E z) (identityPlus F w) (identityPlus_linear E hE z) (identityPlus_linear F hF w)
    (identityPlus_congr E F hEF z w hzw) resolventContraction resolventContraction
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (deviation_bound E hsmallE z hz) (deviation_bound F hsmallF w hw)

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
