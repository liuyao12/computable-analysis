import ComputableAnalysis.RiemannHilbert.ContourHalfEdgeGeometry

/-! Finite scaling and oriented square averages for arbitrary represented samples. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

theorem rationalRectangleScalar_scale (q : QComplex) (r : Rat) :
    (rationalRectangleScalar (QComplex.scaleRat r q)).val=
      scaleRat r (rationalRectangleScalar q).val := by
  simp only [rationalRectangleScalar,scaleRat,ofQComplex,QBox.scaleRat,QComplex.scaleRat]
  apply congrArg (fun f : Nat → QBox => ({compute := f} : ComplexRaw))
  funext n
  split <;> rfl

theorem rationalWeightedSample_scale (z : Scalar) (q : QComplex) (r : Rat) :
    (scalarProduct z (rationalRectangleScalar (QComplex.scaleRat r q))).val.Equiv
      (scaleRat r (scalarProduct z (rationalRectangleScalar q)).val) := by
  let w := rationalRectangleScalar q
  have hs : (rationalRectangleScalar (QComplex.scaleRat r q)).val=scaleRat r w.val :=
    rationalRectangleScalar_scale q r
  have ha := mul_comm_equiv z.val (scaleRat r w.val) z.property (scaleRat_valid w.property)
  have hb := scaleRat_mul_equiv r w.val z.val w.property z.property
  have hc : (scaleRat r (mul w.val z.val)).Equiv (scaleRat r (mul z.val w.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (mul_valid w.property z.property))
      (hright := scaleRat_valid (mul_valid z.property w.property))
    rw [ComplexRawQuotient.ofRaw_scaleRat,ComplexRawQuotient.ofRaw_scaleRat]
    congr 1
    exact ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := mul_valid w.property z.property) (hright := mul_valid z.property w.property)
      (mul_comm_equiv w.val z.val w.property z.property)
  change (mul z.val (rationalRectangleScalar (QComplex.scaleRat r q)).val).Equiv _
  rw [hs]
  exact equiv_trans (mul_valid z.property (scaleRat_valid w.property))
    (mul_valid (scaleRat_valid w.property) z.property)
    (scaleRat_valid (mul_valid z.property w.property)) ha
    (equiv_trans (mul_valid (scaleRat_valid w.property) z.property)
      (scaleRat_valid (mul_valid w.property z.property))
      (scaleRat_valid (mul_valid z.property w.property)) (equiv_symm hb) hc)

theorem gridValueSum_scale (r : Rat) (f : Nat → ScalarAlgebra.Value) (n : Nat) :
    gridValueSum n (fun j => ComplexRawQuotient.scaleRat r (f j))=
      ComplexRawQuotient.scaleRat r (gridValueSum n f) := by
  induction n with
  | zero => exact (ComplexRawQuotient.scaleRat_zero r).symm
  | succ n ih =>
    simp only [gridValueSum,ih,ComplexRawQuotient.scaleRat_add]

theorem gridScalarSum_scale (r : Rat) (f : Nat → Scalar) (n : Nat) :
    (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩)).val.Equiv
      (scaleRat r (gridScalarSum n f).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩)).property)
    (hright := scaleRat_valid (gridScalarSum n f).property)
  change gridScalarValue (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩))=
    ComplexRawQuotient.ofRaw (scaleRat r (gridScalarSum n f).val) _
  rw [gridScalarSum_value,ComplexRawQuotient.ofRaw_scaleRat]
  change gridValueSum n (fun j => ComplexRawQuotient.ofRaw (scaleRat r (f j).val) _)=
    ComplexRawQuotient.scaleRat r (gridScalarValue (gridScalarSum n f))
  simp only [ComplexRawQuotient.ofRaw_scaleRat,gridScalarSum_value]
  exact gridValueSum_scale r (fun j => gridScalarValue (f j)) n

def commonSquareKernelAverage (f : QComplex → Scalar) (edge : HalfEdge)
    (S : QPos) (M : Nat) : Scalar :=
  let sum := gridScalarSum M (fun n => scalarProduct
    (f (QComplex.scaleRat S.val (point edge (squareMidpointParameter M n))))
    (rationalRectangleScalar (QComplex.scaleRat S.val (velocity edge))))
  ⟨scaleRat (1/(M:Rat)) sum.val,scaleRat_valid sum.property⟩

def commonSquareKernelEdgeList (f : QComplex → Scalar) (S : QPos) (M : Nat) :
    List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | e::es =>
    let v := commonSquareKernelAverage f e S M
    scalarSum (if e.upper then v else scalarNeg v) (commonSquareKernelEdgeList f S M es)

theorem gridScalarSum_reflected_parameters (f : Rat → Scalar) (M : Nat) (hM : 0<M) :
    (gridScalarSum M (fun v => f (1-squareMidpointParameter M v))).val.Equiv
      (gridScalarSum M (fun v => f (squareMidpointParameter M v))).val := by
  have he := gridScalarSum_congr_bounded M
    (fun v => f (1-squareMidpointParameter M v))
    (fun v => f (squareMidpointParameter M (M-1-v))) (by
      intro v hv
      rw [squareMidpointParameter_reverse M v hM hv]
      exact equiv_refl _ (f (1-squareMidpointParameter M v)).property)
  exact equiv_trans (gridScalarSum M (fun v => f (1-squareMidpointParameter M v))).property
    (gridScalarSum M (fun v => f (squareMidpointParameter M (M-1-v)))).property
    (gridScalarSum M (fun v => f (squareMidpointParameter M v))).property he
    (gridScalarSum_reverse (fun v => f (squareMidpointParameter M v)) M)

end ComputableAnalysis.RiemannHilbert.RectangularContour
