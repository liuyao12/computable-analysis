import ComputableAnalysis.RiemannHilbert.ScalarPolynomialHorner

/-! Literal coefficient-list arithmetic, with exact evaluation identities.
No coefficient equality test or finite precision comparison is used. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPolynomialArithmetic
open ComplexRaw FunctionTheory DomainFunctions RectangularContour ScalarPolynomial
set_option autoImplicit false

def add : Polynomial → Polynomial → Polynomial
  | [],Q => Q
  | P,[] => P
  | a::P,b::Q => scalarSum a b::add P Q
def scale (c : Scalar) (P : Polynomial) : Polynomial := P.map (scalarProduct c)
def shift (P : Polynomial) : Polynomial := zeroScalar::P
def multiply : Polynomial → Polynomial → Polynomial
  | [],_ => []
  | a::P,Q => add (scale a Q) (shift (multiply P Q))
def negate (P : Polynomial) : Polynomial := scale (rationalRectangleScalar ⟨-1,0⟩) P
def subtract (P Q : Polynomial) : Polynomial := add P (negate Q)

theorem value_cons_image (a : Scalar) (P : Polynomial) (z : Scalar) :
    gridScalarValue (value (a::P) z)=gridScalarValue a+gridScalarValue z*gridScalarValue (value P z) :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (ScalarPolynomialHorner.value_cons a P z)

theorem value_add_image (P Q : Polynomial) (z : Scalar) :
    gridScalarValue (value (add P Q) z)=gridScalarValue (value P z)+gridScalarValue (value Q z) := by
  induction P generalizing Q with
  | nil => change gridScalarValue (value Q z)=0+gridScalarValue (value Q z); grind only
  | cons a P ih =>
    cases Q with
    | nil => change gridScalarValue (value (a::P) z)=gridScalarValue (value (a::P) z)+0; grind only
    | cons b Q =>
      simp only [add,value_cons_image,gridScalarValue_add,ih]
      grind only

theorem value_scale_image (c : Scalar) (P : Polynomial) (z : Scalar) :
    gridScalarValue (value (scale c P) z)=gridScalarValue c*gridScalarValue (value P z) := by
  induction P with
  | nil => change (0 : ScalarAlgebra.Value)=gridScalarValue c*0; grind only
  | cons a P ih =>
    change gridScalarValue (value (scalarProduct c a::scale c P) z)=_
    rw [value_cons_image,value_cons_image,ih]
    change gridScalarValue c*gridScalarValue a+gridScalarValue z*
      (gridScalarValue c*gridScalarValue (value P z))=_
    grind only

theorem value_shift_image (P : Polynomial) (z : Scalar) :
    gridScalarValue (value (shift P) z)=gridScalarValue z*gridScalarValue (value P z) := by
  rw [shift,value_cons_image]
  change (0 : ScalarAlgebra.Value)+_= _
  grind only

theorem value_multiply_image (P Q : Polynomial) (z : Scalar) :
    gridScalarValue (value (multiply P Q) z)=gridScalarValue (value P z)*gridScalarValue (value Q z) := by
  induction P with
  | nil => change (0 : ScalarAlgebra.Value)=0*gridScalarValue (value Q z); grind only
  | cons a P ih =>
    rw [multiply,value_add_image,value_scale_image,value_shift_image,ih,value_cons_image]
    grind only

theorem value_negate_image (P : Polynomial) (z : Scalar) :
    gridScalarValue (value (negate P) z)= -gridScalarValue (value P z) := by
  rw [negate,value_scale_image]
  change (-1 : ScalarAlgebra.Value)*_= _
  grind only

theorem value_subtract_image (P Q : Polynomial) (z : Scalar) :
    gridScalarValue (value (subtract P Q) z)=gridScalarValue (value P z)-gridScalarValue (value Q z) := by
  rw [subtract,value_add_image,value_negate_image]
  rfl

theorem value_constant_image (c : Scalar) (z : Scalar) :
    gridScalarValue (value [c] z)=gridScalarValue c := by
  rw [value_cons_image]
  change gridScalarValue c+gridScalarValue z*0=gridScalarValue c
  grind only

theorem value_add (P Q : Polynomial) (z : Scalar) :
    value (add P Q) z≈scalarSum (value P z) (value Q z) :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (value_add_image P Q z)
theorem value_scale (c : Scalar) (P : Polynomial) (z : Scalar) :
    value (scale c P) z≈scalarProduct c (value P z) :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (value_scale_image c P z)
theorem value_multiply (P Q : Polynomial) (z : Scalar) :
    value (multiply P Q) z≈scalarProduct (value P z) (value Q z) :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (value_multiply_image P Q z)
theorem value_subtract (P Q : Polynomial) (z : Scalar) :
    value (subtract P Q) z≈gridScalarSub (value P z) (value Q z) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (value (subtract P Q) z).property)
    (hright := (gridScalarSub (value P z) (value Q z)).property)
  change gridScalarValue (value (subtract P Q) z)=
    gridScalarValue (gridScalarSub (value P z) (value Q z))
  rw [gridScalarValue_sub]
  exact value_subtract_image P Q z
theorem value_constant (c : Scalar) (z : Scalar) : value [c] z≈c :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (value_constant_image c z)

end ComputableAnalysis.RiemannHilbert.ScalarPolynomialArithmetic
