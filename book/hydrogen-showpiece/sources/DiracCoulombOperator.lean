import ComputableAnalysis.HydrogenCartesianRadius

/-! The dimensionless Dirac--Coulomb differential expression. The value
and partial arrays are supplied separately; clients must justify their
derivative role. The hydrogen client constructs all of those witnesses. -/
namespace ComputableAnalysis.DiracCoulombOperator
open RiemannHilbert DomainFunctions HydrogenRadialEnvelope HydrogenCartesianRadius
open ComputableCoefficient PauliSpinor

def coulomb (alpha : Value) (X : Point) (hX : domain X) : Scalar :=
  scalarProduct (coefficient alpha) (radiusInverse X hX)
def upperDiagonal (alpha : Value) (X : Point) (hX : domain X) : Scalar :=
  scalarSum oneScalar (scalarNeg (coulomb alpha X hX))
def lowerDiagonal (alpha : Value) (X : Point) (hX : domain X) : Scalar :=
  scalarNeg (scalarSum oneScalar (coulomb alpha X hX))

def actionUpper (alpha : Value) (X : Point) (hX : domain X) (u v : Spinor)
    (du dv : Fin 3 → Spinor) : Spinor := fun k =>
  scalarSum (scalarProduct (upperDiagonal alpha X hX) (u k))
    (scalarProduct (scalarNeg imaginary) (gradient dv k))
def actionLower (alpha : Value) (X : Point) (hX : domain X) (u v : Spinor)
    (du dv : Fin 3 → Spinor) : Spinor := fun k =>
  scalarSum (scalarProduct (scalarNeg imaginary) (gradient du k))
    (scalarProduct (lowerDiagonal alpha X hX) (v k))
def action (alpha : Value) (X : Point) (hX : domain X) (u v : Spinor)
    (du dv : Fin 3 → Spinor) : Fin 4 → Scalar := fun k =>
  if k.val=0 then actionUpper alpha X hX u v du dv 0
  else if k.val=1 then actionUpper alpha X hX u v du dv 1
  else if k.val=2 then actionLower alpha X hX u v du dv 0
  else actionLower alpha X hX u v du dv 1

end ComputableAnalysis.DiracCoulombOperator
