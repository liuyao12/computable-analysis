import ComputableAnalysis.RiemannHilbert.ContourMatrixParameters

/-! The actual matrix Cauchy series reconstructs the supplied linear
holomorphic evaluator, on an internally chosen common neighborhood. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedMatrixTaylor
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField RectangularContour
set_option autoImplicit false
variable {n m : Nat} {D : Scalar → Prop}
variable (G : Field (n := n) (m := m) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (b : Scalar) (hb : D b)

def entry (i : Fin n) (j : Fin m) : DomainFunctions.Map :=
  SeriesMatrix.entry b (coefficients G O hG hM b hb) (coefficients_valid G O hG hM b hb)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb) (radius_budget G O hG hM b hb) i j

theorem entry_agrees (i : Fin n) (j : Fin m) (z : Scalar)
    (hz : Centered.domain b (radius G O hG hM b hb).val z) (ha : D z) :
    (entry G O hG hM b hb i j).eval z hz≈matrixEntry G i j z ha := by
  let f := entryMap G O.invariant hG i j
  let hf := hM i j
  let ht := radius_entry_domain G O hG hM b hb i j z hz
  have he := CenteredSeries.value_agrees b (coefficients G O hG hM b hb i j) (coefficients_valid G O hG hM b hb i j)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb i j) (radius_budget G O hG hM b hb)
    b (localCauchyTaylorCoefficients f hf b hb) (localCauchyTaylorCoefficients_valid f hf b hb)
    (localCauchyCoefficientBound f b hb).val (localCauchyCoefficientRate f hf b hb).val (localCauchyTaylorRadius f hf b hb).val
    (Rat.le_of_lt (localCauchyCoefficientBound f b hb).property) (Rat.le_of_lt (localCauchyCoefficientRate f hf b hb).property)
    (Rat.le_of_lt (localCauchyTaylorRadius f hf b hb).property) (localCauchyMoment_majorant f hf b hb)
    (localCauchyTaylor_series_budget f hf b hb) (equiv_refl _ b.property)
    (fun k => equiv_refl _ (coefficients_valid G O hG hM b hb i j k)) z z hz ht (equiv_refl _ z.property)
  exact Setoid.trans (b := (localCauchyTaylor f hf b hb).eval z ht) he (localCauchyTaylor_agrees f hf b hb z ht ha)

def field : Field (n := n) (m := m) (Centered.domain b (radius G O hG hM b hb).val) :=
  SeriesMatrix.field b (coefficients G O hG hM b hb) (coefficients_valid G O hG hM b hb)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb) (radius_budget G O hG hM b hb)

def openData : ScalarTopology.OpenData (Centered.domain b (radius G O hG hM b hb).val) :=
  SeriesMatrix.openData b (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (Rat.le_of_lt (rate G O hG hM b hb).property) (Rat.le_of_lt (radius G O hG hM b hb).property) (radius_budget G O hG hM b hb)

theorem field_linear (z : Scalar) (hz : Centered.domain b (radius G O hG hM b hb).val z) :
    IsLinear (field G O hG hM b hb z hz) := ValueMap.ofColumns_linear _

theorem field_names (z w : Scalar) (hz : Centered.domain b (radius G O hG hM b hb).val z)
    (hw : Centered.domain b (radius G O hG hM b hb).val w) (he : z≈w) :
    (field G O hG hM b hb z hz).Equiv (field G O hG hM b hb w hw) :=
  SeriesMatrix.field_names b (coefficients G O hG hM b hb) (coefficients_valid G O hG hM b hb)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb) (radius_budget G O hG hM b hb) z w hz hw he

def field_holomorphic : MatrixHolomorphic (field G O hG hM b hb)
    (openData G O hG hM b hb).invariant (field_names G O hG hM b hb) :=
  SeriesMatrix.holomorphic b (coefficients G O hG hM b hb) (coefficients_valid G O hG hM b hb)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb) (radius_budget G O hG hM b hb)

theorem field_entry (i : Fin n) (j : Fin m) (z : Scalar)
    (hz : Centered.domain b (radius G O hG hM b hb).val z) :
    matrixEntry (field G O hG hM b hb) i j z hz≈(entry G O hG hM b hb i j).eval z hz :=
  SeriesMatrix.field_entry b (coefficients G O hG hM b hb) (coefficients_valid G O hG hM b hb)
    (bound G O hG b hb) (rate G O hG hM b hb).val (radius G O hG hM b hb).val
    (bound_nonneg G O hG b hb) (Rat.le_of_lt (rate G O hG hM b hb).property)
    (Rat.le_of_lt (radius G O hG hM b hb).property) (coefficients_bound G O hG hM b hb) (radius_budget G O hG hM b hb) i j z hz

/-- Exact equality of operators on every represented input vector. -/
theorem field_agrees (hlinear : ∀ z hz, IsLinear (G z hz)) (z : Scalar)
    (hz : Centered.domain b (radius G O hG hM b hb).val z) (ha : D z) :
    (field G O hG hM b hb z hz).Equiv (G z ha) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (field_linear G O hG hM b hb z hz) (hlinear z ha)).2
  intro i j
  exact equiv_trans (((field G O hG hM b hb z hz).eval (Fiber.basis i)).property j)
    ((entry G O hG hM b hb i j).eval z hz).property (((G z ha).eval (Fiber.basis i)).property j)
    (field_entry G O hG hM b hb i j z hz) (entry_agrees G O hG hM b hb i j z hz ha)

def coefficientOperators (k : Nat) : ValueMap (Fiber n) (Fiber m) :=
  ValueMap.ofColumns (fun i => ⟨fun j => coefficients G O hG hM b hb i j k,fun j => coefficients_valid G O hG hM b hb i j k⟩)

theorem coefficientOperators_linear (k : Nat) : IsLinear (coefficientOperators G O hG hM b hb k) :=
  ValueMap.ofColumns_linear _

theorem coefficientOperators_entry (i : Fin n) (j : Fin m) (k : Nat) :
    (((coefficientOperators G O hG hM b hb k).eval (Fiber.basis i)).val j).Equiv
      (coefficients G O hG hM b hb i j k) := ValueMap.ofColumns_basis _ i j

theorem coefficientOperators_bound (k : Nat) (E : Rat) (hE : 0≤E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((coefficientOperators G O hG hM b hb k).eval x)
      (2*((n : Rat)*bound G O hG b hb)*(rate G O hG hM b hb).val^k*E) := by
  have hp : 0≤bound G O hG b hb*(rate G O hG hM b hb).val^k :=
    Rat.mul_nonneg (bound_nonneg G O hG b hb) (Rat.pow_nonneg (Rat.le_of_lt (rate G O hG hM b hb).property))
  have hs := ValueMap.linear_bound_of_basis (coefficientOperators G O hG hM b hb k)
    (coefficientOperators_linear G O hG hM b hb k) _ hp (fun i j =>
      Small.congr (coefficients_valid G O hG hM b hb i j k)
        (((coefficientOperators G O hG hM b hb k).eval (Fiber.basis i)).property j)
        (equiv_symm (coefficientOperators_entry G O hG hM b hb i j k)) (coefficients_bound G O hG hM b hb i j k)) x E hE hx
  have he : (2*(n : Rat)*(bound G O hG b hb*(rate G O hG hM b hb).val^k))*E=
      2*((n : Rat)*bound G O hG b hb)*(rate G O hG hM b hb).val^k*E := by grind only
  rw [he] at hs
  exact hs

theorem coefficientOperators_congr (hN : MatrixHolomorphic G O.invariant hG) (c : Scalar) (hc : D c)
    (hbc : b≈c) (k : Nat) :
    (coefficientOperators G O hG hM b hb k).Equiv (coefficientOperators G O hG hN c hc k) :=
  ValueMap.ofColumns_congr _ _ (fun i j => coefficients_congr G O hG hM b hb hN c hc hbc i j k)

theorem coefficientOperators_data_congr (P : ScalarTopology.OpenData D)
    (hNnames : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hNnames) (c : Scalar) (hc : D c) (hbc : b≈c) (k : Nat) :
    (coefficientOperators G O hG hM b hb k).Equiv (coefficientOperators G P hNnames hN c hc k) :=
  ValueMap.ofColumns_congr _ _ (fun i j => coefficients_data_congr G O hG hM b hb P hNnames hN c hc hbc i j k)

end ComputableAnalysis.RiemannHilbert.ConstructedMatrixTaylor
