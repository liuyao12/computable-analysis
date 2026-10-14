import ComputableAnalysis.RiemannHilbert.ContourTaylorKernel

/-! Exact boundary linearity for arbitrary finite represented series,
and convergence of their actual finite sums. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem rectangleGridBoundary_zero (J : QInterval × QInterval) (M : Nat) :
    rectangleGridBoundary (fun _ => (rationalRectangleScalar QComplex.zero)) J M≈(rationalRectangleScalar QComplex.zero) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (rectangleGridBoundary (fun _ => (rationalRectangleScalar QComplex.zero)) J M).property) (hright := (rationalRectangleScalar QComplex.zero).property)
  change gridScalarValue (rectangleGridBoundary (fun _ => (rationalRectangleScalar QComplex.zero)) J M)=0
  simp only [rectangleGridBoundary,gridScalarBoundary,gridScalarValue_add,gridScalarValue_sub,gridScalarSum_value]
  have hh (j k : Nat) : gridScalarValue (rectangleGridHorizontal (fun _ => (rationalRectangleScalar QComplex.zero)) J M j k)=0 := by
    change 0*gridScalarValue (rationalRectangleScalar _)=0; grind only
  have hv (j k : Nat) : gridScalarValue (rectangleGridVertical (fun _ => (rationalRectangleScalar QComplex.zero)) J M j k)=0 := by
    change 0*gridScalarValue (rationalRectangleScalar _)=0; grind only
  have hzero : (0:ScalarAlgebra.Value)-0=0 := by grind only
  simp only [hh,hv,hzero,gridValueSum_zero]
  grind only

theorem rectangleGridBoundary_sum (f g : QComplex → Scalar) (J : QInterval × QInterval)
    (M : Nat) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    rectangleGridBoundary (fun q => scalarSum (f q) (g q)) J M≈
      scalarSum (rectangleGridBoundary f J M) (rectangleGridBoundary g J M) := by
  have hp (q : QComplex) : scalarSum (f q) (g q)≈sampleLinear oneScalar oneScalar f g q := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarSum (f q) (g q)).property) (hright := (sampleLinear oneScalar oneScalar f g q).property)
    change gridScalarValue (f q)+gridScalarValue (g q)=1*gridScalarValue (f q)+1*gridScalarValue (g q)
    grind only
  apply Setoid.trans (b := rectangleGridBoundary (sampleLinear oneScalar oneScalar f g) J M)
    (rectangleGridBoundary_congr _ _ J M hX hY (fun q _ => hp q))
  apply Setoid.trans (rectangleGridBoundary_linear oneScalar oneScalar f g J M)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarProduct oneScalar (rectangleGridBoundary f J M))
      (scalarProduct oneScalar (rectangleGridBoundary g J M))).property)
    (hright := (scalarSum (rectangleGridBoundary f J M) (rectangleGridBoundary g J M)).property)
  change 1*gridScalarValue (rectangleGridBoundary f J M)+1*gridScalarValue (rectangleGridBoundary g J M)=
    gridScalarValue (rectangleGridBoundary f J M)+gridScalarValue (rectangleGridBoundary g J M)
  grind only

theorem rectangleGridBoundary_product_left (a : Scalar) (f : QComplex → Scalar)
    (J : QInterval × QInterval) (M : Nat) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    rectangleGridBoundary (fun q => scalarProduct a (f q)) J M≈scalarProduct a (rectangleGridBoundary f J M) := by
  have hp (q : QComplex) : scalarProduct a (f q)≈sampleLinear a (rationalRectangleScalar QComplex.zero) f f q := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarProduct a (f q)).property) (hright := (sampleLinear a (rationalRectangleScalar QComplex.zero) f f q).property)
    change gridScalarValue a*gridScalarValue (f q)=gridScalarValue a*gridScalarValue (f q)+0*gridScalarValue (f q)
    grind only
  apply Setoid.trans (b := rectangleGridBoundary (sampleLinear a (rationalRectangleScalar QComplex.zero) f f) J M)
    (rectangleGridBoundary_congr _ _ J M hX hY (fun q _ => hp q))
  apply Setoid.trans (rectangleGridBoundary_linear a (rationalRectangleScalar QComplex.zero) f f J M)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarProduct a (rectangleGridBoundary f J M))
      (scalarProduct (rationalRectangleScalar QComplex.zero) (rectangleGridBoundary f J M))).property)
    (hright := (scalarProduct a (rectangleGridBoundary f J M)).property)
  change gridScalarValue a*gridScalarValue (rectangleGridBoundary f J M)+0*gridScalarValue (rectangleGridBoundary f J M)=
    gridScalarValue a*gridScalarValue (rectangleGridBoundary f J M)
  grind only

theorem rectangleGridBoundary_finite_sum (s : Nat → QComplex → Scalar)
    (J : QInterval × QInterval) (M : Nat) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (N : Nat) :
    rectangleGridBoundary (fun q => gridScalarSum N (fun k => s k q)) J M≈
      gridScalarSum N (fun k => rectangleGridBoundary (s k) J M) := by
  induction N with
  | zero => exact rectangleGridBoundary_zero J M
  | succ N ih =>
    exact Setoid.trans (rectangleGridBoundary_sum (fun q => gridScalarSum N (fun k => s k q)) (s N) J M hX hY)
      (add_equiv ih (equiv_refl _ (rectangleGridBoundary (s N) J M).property))

theorem converge_constant (a : Scalar) : Converges (fun _ => a) a := by
  intro eps
  refine ⟨0,fun _ _ => ?_⟩
  have he : (sub a.val a.val).Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid a.property a.property) (hright := ofQComplex_valid _)
    change gridScalarValue a-gridScalarValue a=0
    grind only
  exact Small.congr (ofQComplex_valid _) (sub_valid a.property a.property) (equiv_symm he)
    ((Small.zero (by decide +kernel : (0:Rat)≤0)).mono (Rat.le_of_lt eps.property))

theorem converge_finite_sum (p : Nat → Nat → Scalar) (a : Nat → Scalar)
    (hp : ∀ k, Converges (p k) (a k)) (N : Nat) :
    Converges (fun n => gridScalarSum N (fun k => p k n)) (gridScalarSum N a) := by
  induction N with
  | zero => exact converge_constant (rationalRectangleScalar QComplex.zero)
  | succ N ih => exact converge_sum _ _ _ _ ih (hp N)

end ComputableAnalysis.RiemannHilbert.RectangularContour
