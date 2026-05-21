import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.Polynomial

/-!
# Algebraic numbers as certified raw algorithms

This file sets up the project-facing algebraic-number layer.

The point is not to define algebraic numbers as an abstract completed field.
An algebraic complex number is a certified `ComplexRaw` together with a
nonzero rational polynomial that it satisfies.  Closure facts and algebraic
closure over algebraic coefficients are theorem targets; the nontrivial
algebraic proofs are intentionally left as `sorry` placeholders for now.
-/

namespace ComputableAnalysis

namespace RatPoly

abbrev Coeffs := List Rat

def toComplexCoeffs (p : Coeffs) : CPoly.Coeffs :=
  p.map QComplex.ofRat

def Nonzero (p : Coeffs) : Prop :=
  Exists fun n : Nat =>
  Exists fun c : Rat =>
    p[n]? = some c /\ c != 0

def PositiveDegree (p : Coeffs) : Prop :=
  Exists fun n : Nat =>
  Exists fun c : Rat =>
    p[n]? = some c /\ n != 0 /\ c != 0

def linearRoot (q : Rat) : Coeffs := [-q, 1]

def qcomplexRoot (z : QComplex) : Coeffs :=
  [z.re * z.re + z.im * z.im, -((2 : Rat) * z.re), 1]

theorem linearRoot_nonzero (q : Rat) : Nonzero (linearRoot q) := by
  exact ⟨1, 1, by simp [linearRoot]⟩

theorem qcomplexRoot_nonzero (z : QComplex) : Nonzero (qcomplexRoot z) := by
  refine Exists.intro 2 ?_
  refine Exists.intro (1 : Rat) ?_
  simp [qcomplexRoot]

theorem linearRoot_exact_root (q : Rat) :
    CPoly.hasExactRoot (toComplexCoeffs (linearRoot q)) (QComplex.ofRat q) := by
  simp [CPoly.hasExactRoot, toComplexCoeffs, linearRoot, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem qcomplexRoot_exact_root (z : QComplex) :
    CPoly.hasExactRoot (toComplexCoeffs (qcomplexRoot z)) z := by
  simp [CPoly.hasExactRoot, toComplexCoeffs, qcomplexRoot, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

end RatPoly

/-- A certified computable root of a complex polynomial. -/
def IsComputableRoot (coeffs : CPoly.Coeffs) (z : ComplexCert) : Prop :=
  forall n : Nat, IsApproxRootAt coeffs z.raw n

def exactComplexCert (z : QComplex) : ComplexCert where
  raw := ComplexRaw.ofQComplex z
  valid := ComplexRaw.ofQComplex_valid z

/-- Any exact rational-complex root is automatically a computable root. -/
theorem exactRoot_is_computable
    {coeffs : CPoly.Coeffs} {z : QComplex}
    (h : CPoly.hasExactRoot coeffs z) :
    IsComputableRoot coeffs (exactComplexCert z) := by
  intro n
  change QBox.Overlaps
    (QBox.evalPoly coeffs (QBox.point z))
    (QBox.zeroAround (if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }))
  rw [QBox.evalPoly_point, h]
  simp [QBox.point, QBox.zeroAround, QBox.Overlaps, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

/-- A certified complex raw representative satisfies a rational polynomial
when polynomial evaluation on its boxes overlaps zero at every public stage.

For valid shrinking boxes this is the project-facing exact-root certificate:
the residual boxes shrink to zero around the origin.
-/
def ComplexRootWitness (p : RatPoly.Coeffs) (z : ComplexCert) : Prop :=
  forall n, IsApproxRootAt (RatPoly.toComplexCoeffs p) z.raw n

/-- Algebraic complex numbers are certified complex interval algorithms with a
rational-polynomial annihilator. -/
structure AlgebraicComplex where
  value : ComplexCert
  annihilator : RatPoly.Coeffs
  nonzero_annihilator : RatPoly.Nonzero annihilator
  root_witness : ComplexRootWitness annihilator value

namespace AlgebraicComplex

def asComplex (z : AlgebraicComplex) : Complex :=
  Complex.ofCert z.value

def compute (z : AlgebraicComplex) (n : Nat) : QBox :=
  z.value.raw.compute n

def Equiv (z w : AlgebraicComplex) : Prop :=
  z.value.raw.Equiv w.value.raw

def Nonzero (z : AlgebraicComplex) : Prop :=
  ¬ z.value.raw.Equiv ComplexRaw.zero

def ofQComplex (z : QComplex) : AlgebraicComplex where
  value := exactComplexCert z
  annihilator := RatPoly.qcomplexRoot z
  nonzero_annihilator := RatPoly.qcomplexRoot_nonzero z
  root_witness := exactRoot_is_computable (RatPoly.qcomplexRoot_exact_root z)

def ofRat (q : Rat) : AlgebraicComplex where
  value := exactComplexCert (QComplex.ofRat q)
  annihilator := RatPoly.linearRoot q
  nonzero_annihilator := RatPoly.linearRoot_nonzero q
  root_witness := exactRoot_is_computable (RatPoly.linearRoot_exact_root q)

def addRaw (z w : AlgebraicComplex) : ComplexRaw :=
  ComplexRaw.add z.value.raw w.value.raw

def negRaw (z : AlgebraicComplex) : ComplexRaw :=
  ComplexRaw.neg z.value.raw

def subRaw (z w : AlgebraicComplex) : ComplexRaw :=
  ComplexRaw.sub z.value.raw w.value.raw

def mulRaw (z w : AlgebraicComplex) : ComplexRaw :=
  ComplexRaw.mul z.value.raw w.value.raw

theorem addRaw_valid (z w : AlgebraicComplex) : (addRaw z w).Valid := by
  exact ComplexRaw.add_valid z.value.valid w.value.valid

theorem negRaw_valid (z : AlgebraicComplex) : (negRaw z).Valid := by
  exact ComplexRaw.neg_valid z.value.valid

theorem mulRaw_valid (z w : AlgebraicComplex) : (mulRaw z w).Valid := by
  -- Interval multiplication preserves validity.
  sorry

def addCert (z w : AlgebraicComplex) : ComplexCert where
  raw := addRaw z w
  valid := addRaw_valid z w

def negCert (z : AlgebraicComplex) : ComplexCert where
  raw := negRaw z
  valid := negRaw_valid z

def mulCert (z w : AlgebraicComplex) : ComplexCert where
  raw := mulRaw z w
  valid := mulRaw_valid z w

/-- Algebraic closure under addition, expressed as an annihilator-existence
target for the concrete addition algorithm. -/
theorem add_annihilator_exists (z w : AlgebraicComplex) :
    Exists fun p : RatPoly.Coeffs =>
      RatPoly.Nonzero p /\ ComplexRootWitness p (addCert z w) := by
  -- Future proof: eliminate `z` and `w` using their rational annihilators,
  -- e.g. through resultants or finite-dimensional algebra.
  sorry

theorem neg_annihilator_exists (z : AlgebraicComplex) :
    Exists fun p : RatPoly.Coeffs =>
      RatPoly.Nonzero p /\ ComplexRootWitness p (negCert z) := by
  -- Future proof: transform the annihilator by `X |-> -X`.
  sorry

theorem mul_annihilator_exists (z w : AlgebraicComplex) :
    Exists fun p : RatPoly.Coeffs =>
      RatPoly.Nonzero p /\ ComplexRootWitness p (mulCert z w) := by
  -- Future proof: eliminate `z` and `w` using their rational annihilators.
  sorry

noncomputable def add (z w : AlgebraicComplex) : AlgebraicComplex :=
  let h := add_annihilator_exists z w
  { value := addCert z w
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

noncomputable def neg (z : AlgebraicComplex) : AlgebraicComplex :=
  let h := neg_annihilator_exists z
  { value := negCert z
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

noncomputable def mul (z w : AlgebraicComplex) : AlgebraicComplex :=
  let h := mul_annihilator_exists z w
  { value := mulCert z w
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

/-- Inversion closure is recorded relationally for now, since the project does
not yet have a complex interval inverse algorithm packaged as `ComplexRaw`. -/
theorem inv_exists (z : AlgebraicComplex) (hz : z.Nonzero) :
    Exists fun w : AlgebraicComplex =>
      (mul z w).Equiv (ofRat 1) := by
  -- Future proof: use the reciprocal polynomial and an apartness certificate.
  sorry

end AlgebraicComplex

namespace RootsOfUnity

/-!
Roots of unity are algebraic numbers first: they are roots of `X^n - 1`.
The exact rational-complex roots below cover the values already expressible in
`QComplex`; non-rational roots such as primitive third roots should later be
constructed by an isolating box or Newton certificate.
-/

def qpow (z : QComplex) : Nat -> QComplex
  | 0 => QComplex.one
  | n + 1 => QComplex.mul z (qpow z n)

/-- The rational polynomial `X^n - 1`, with coefficients in increasing
degree order.  The `n = 0` case is the zero polynomial. -/
def polynomial : Nat -> RatPoly.Coeffs
  | 0 => [0]
  | n + 1 => [-1] ++ List.replicate n 0 ++ [1]

def complexPolynomial (n : Nat) : CPoly.Coeffs :=
  RatPoly.toComplexCoeffs (polynomial n)

def IsNthRoot (n : Nat) (z : QComplex) : Prop :=
  qpow z n = QComplex.one

def IsPrimitiveNthRoot (n : Nat) (z : QComplex) : Prop :=
  IsNthRoot n z /\
    forall k : Nat, 0 < k -> k < n -> qpow z k != QComplex.one

theorem polynomial_nonzero {n : Nat} (hn : 0 < n) :
    RatPoly.Nonzero (polynomial n) := by
  cases n with
  | zero => cases hn
  | succ k =>
      refine Exists.intro (k + 1) ?_
      refine Exists.intro (1 : Rat) ?_
      simp [polynomial]

theorem polynomial_positiveDegree {n : Nat} (hn : 0 < n) :
    RatPoly.PositiveDegree (polynomial n) := by
  cases n with
  | zero => cases hn
  | succ k =>
      refine Exists.intro (k + 1) ?_
      refine Exists.intro (1 : Rat) ?_
      simp [polynomial]

theorem eval_monomial (z : QComplex) (n : Nat) :
    CPoly.eval (List.replicate n QComplex.zero ++ [QComplex.one]) z =
      qpow z n := by
  induction n with
  | zero =>
      grind [CPoly.eval, qpow, QComplex.add, QComplex.mul, QComplex.one,
        QComplex.zero]
  | succ n ih =>
      change
        QComplex.add QComplex.zero
          (QComplex.mul z
            (CPoly.eval (List.replicate n QComplex.zero ++ [QComplex.one]) z)) =
        qpow z (n + 1)
      rw [ih]
      grind [qpow, QComplex.add, QComplex.mul, QComplex.zero]

theorem eval_polynomial (z : QComplex) (n : Nat) :
    CPoly.eval (complexPolynomial n) z =
      QComplex.add (QComplex.ofRat (-1)) (qpow z n) := by
  cases n with
  | zero =>
      grind [complexPolynomial, polynomial, RatPoly.toComplexCoeffs,
        CPoly.eval, qpow, QComplex.ofRat, QComplex.add, QComplex.mul,
        QComplex.one, QComplex.zero]
  | succ k =>
      simp [complexPolynomial, polynomial, RatPoly.toComplexCoeffs]
      change
        CPoly.eval
          (QComplex.ofRat (-1) ::
            (List.replicate k QComplex.zero ++ [QComplex.one])) z =
        QComplex.add (QComplex.ofRat (-1)) (qpow z (k + 1))
      change
        QComplex.add (QComplex.ofRat (-1))
          (QComplex.mul z
            (CPoly.eval (List.replicate k QComplex.zero ++ [QComplex.one]) z)) =
        QComplex.add (QComplex.ofRat (-1)) (qpow z (k + 1))
      rw [eval_monomial]
      rfl

theorem exact_root_polynomial
    {n : Nat} {z : QComplex} (hz : IsNthRoot n z) :
    CPoly.hasExactRoot (complexPolynomial n) z := by
  unfold CPoly.hasExactRoot
  rw [eval_polynomial, hz]
  grind [QComplex.add, QComplex.ofRat, QComplex.one, QComplex.zero]

def exactAlgebraic (n : Nat) (hn : 0 < n)
    (z : QComplex) (hz : IsNthRoot n z) : AlgebraicComplex where
  value := exactComplexCert z
  annihilator := polynomial n
  nonzero_annihilator := polynomial_nonzero hn
  root_witness := exactRoot_is_computable (exact_root_polynomial hz)

/-- A root of unity packaged as an algebraic complex number together with the
specific `X^n - 1` witness. -/
structure Root where
  order : Nat
  order_pos : 0 < order
  number : AlgebraicComplex
  unity_witness : ComplexRootWitness (polynomial order) number.value

def exactRoot (n : Nat) (hn : 0 < n)
    (z : QComplex) (hz : IsNthRoot n z) : Root where
  order := n
  order_pos := hn
  number := exactAlgebraic n hn z hz
  unity_witness := by
    simpa [exactAlgebraic]
      using (exactRoot_is_computable (coeffs := RatPoly.toComplexCoeffs (polynomial n)) (z := z)
        (exact_root_polynomial hz))

def unity : Root :=
  exactRoot 1 (by native_decide) QComplex.one
    (by
      unfold IsNthRoot
      native_decide)

def minusOneQ : QComplex := QComplex.ofRat (-1)

def minusOne : Root :=
  exactRoot 2 (by native_decide) minusOneQ
    (by
      unfold IsNthRoot minusOneQ
      native_decide)

def imaginaryUnitQ : QComplex := { re := 0, im := 1 }

def imaginaryUnit : Root :=
  exactRoot 4 (by native_decide) imaginaryUnitQ
    (by
      unfold IsNthRoot imaginaryUnitQ
      native_decide)

def negImaginaryUnitQ : QComplex := QComplex.neg imaginaryUnitQ

def negImaginaryUnit : Root :=
  exactRoot 4 (by native_decide) negImaginaryUnitQ
    (by
      unfold IsNthRoot negImaginaryUnitQ imaginaryUnitQ
      native_decide)

end RootsOfUnity

namespace AlgPoly

abbrev Coeffs := List AlgebraicComplex

def evalRaw (p : Coeffs) (z : AlgebraicComplex) : ComplexRaw :=
  p.foldr
    (fun c acc => ComplexRaw.add c.value.raw (ComplexRaw.mul z.value.raw acc))
    ComplexRaw.zero

def Root (p : Coeffs) (z : AlgebraicComplex) : Prop :=
  (evalRaw p z).Equiv ComplexRaw.zero

def PositiveDegree (p : Coeffs) : Prop :=
  Exists fun n : Nat =>
  Exists fun c : AlgebraicComplex =>
    p[n]? = some c /\ n != 0 /\ c.Nonzero

/-- Algebraic closure target: every positive-degree polynomial with algebraic
complex coefficients has an algebraic complex root. -/
theorem exists_root (p : Coeffs) (hp : PositiveDegree p) :
    Exists fun z : AlgebraicComplex => Root p z := by
  -- Future proof: reduce algebraic coefficients to rational data and adjoin a
  -- root; no real-completeness or transcendental ambient field should be used.
  sorry

end AlgPoly

structure AlgebraicFun where
  value : RealFunRaw
  polynomialAt : Rat -> List Rat

end ComputableAnalysis
