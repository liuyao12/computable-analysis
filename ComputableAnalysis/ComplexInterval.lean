import ComputableAnalysis.ComplexPolynomial

namespace ComputableAnalysis

namespace QBox

def evalPoly (coeffs : CPoly.Coeffs) (Z : QBox) : QBox :=
  coeffs.foldr (fun c acc => add (point c) (mul Z acc)) zero

theorem add_point (z w : QComplex) :
    add (point z) (point w) = point (QComplex.add z w) := by
  rfl

theorem mul_point (z w : QComplex) :
    mul (point z) (point w) = point (QComplex.mul z w) := by
  simp [mul, mulRealInterval, point, QComplex.mul, min4, max4, minRat, maxRat2]

theorem evalPoly_point (coeffs : CPoly.Coeffs) (z : QComplex) :
    evalPoly coeffs (point z) = point (CPoly.eval coeffs z) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      change add (point c) (mul (point z) (evalPoly cs (point z))) =
        point (QComplex.add c (QComplex.mul z (CPoly.eval cs z)))
      rw [ih]
      rw [mul_point, add_point]

def zeroAround (eps : QPos) : QBox :=
  { lo := { re := -eps.val, im := -eps.val },
    hi := { re := eps.val, im := eps.val } }

end QBox

def IsApproxRootAt (coeffs : CPoly.Coeffs) (z : ComplexRaw) (n : Nat) : Prop :=
  let eps : QPos :=
    if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := by
          rw [Rat.div_def, Rat.one_mul]
          exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }
  QBox.Overlaps (QBox.evalPoly coeffs (z.compute n)) (QBox.zeroAround eps)

def approxRootCheck (coeffs : CPoly.Coeffs) (z : ComplexRaw) (n : Nat) : Bool :=
  let eps : QPos :=
    if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := by
          rw [Rat.div_def, Rat.one_mul]
          exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }
  QBox.overlaps (QBox.evalPoly coeffs (z.compute n)) (QBox.zeroAround eps)

end ComputableAnalysis
