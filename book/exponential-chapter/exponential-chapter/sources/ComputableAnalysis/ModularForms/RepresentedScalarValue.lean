import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! The proof-facing quotient value of a supplied represented scalar.
This identifies valid names and constructs no completion or numerical selector. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert
set_option autoImplicit false

def gridScalarValue (x : Scalar) : ScalarAlgebra.Value := ComplexRawQuotient.ofRaw x.val x.property

end ComputableAnalysis.ModularForms
