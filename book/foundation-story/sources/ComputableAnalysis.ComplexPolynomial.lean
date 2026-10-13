import ComputableAnalysis.Basic

namespace ComputableAnalysis

namespace CPoly

abbrev Coeffs := List QComplex

def eval (coeffs : Coeffs) (z : QComplex) : QComplex :=
  coeffs.foldr (fun c acc => QComplex.add c (QComplex.mul z acc)) QComplex.zero

def degreeBound (coeffs : Coeffs) : Nat :=
  coeffs.length

def coeffNonzero (c : QComplex) : Bool :=
  decide (c != QComplex.zero)

def isZeroPoly (coeffs : Coeffs) : Bool :=
  coeffs.all (fun c => decide (c = QComplex.zero))

def positiveDegree (coeffs : Coeffs) : Prop :=
  Exists fun n : Nat => Exists fun c : QComplex =>
    coeffs[n]? = some c /\ n != 0 /\ c != QComplex.zero

def hasExactRoot (coeffs : Coeffs) (z : QComplex) : Prop :=
  eval coeffs z = QComplex.zero

end CPoly

end ComputableAnalysis
