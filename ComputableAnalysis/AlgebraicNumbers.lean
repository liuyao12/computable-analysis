import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.ComplexMultiplication
import ComputableAnalysis.Polynomial

/-!
# Algebraic numbers as certified raw algorithms

This file sets up the project-facing algebraic-number layer.

The point is not to define algebraic numbers as an abstract completed field.
An algebraic complex number is a certified `ComplexRaw` together with a
nonzero rational polynomial that it satisfies.  Closure facts and algebraic
closure over algebraic coefficients are recorded as explicit theorem targets
until the project supplies the corresponding elimination and isolation
algorithms.
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

theorem equiv_refl (z : AlgebraicComplex) : z.Equiv z :=
  ComplexRaw.equiv_refl z.value.raw z.value.valid

theorem equiv_symm {z w : AlgebraicComplex} : z.Equiv w -> w.Equiv z :=
  ComplexRaw.equiv_symm

theorem equiv_trans {z w u : AlgebraicComplex} :
    z.Equiv w -> w.Equiv u -> z.Equiv u :=
  ComplexRaw.equiv_trans z.value.valid w.value.valid u.value.valid

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

def MulRawValid (z w : AlgebraicComplex) : Prop :=
  (mulRaw z w).Valid

/-- The raw box product of two certified algebraic-complex representatives is
valid.  The remaining closure problem is algebraic, not analytic: construct a
rational-polynomial annihilator for this already certified product. -/
theorem mulRaw_valid (z w : AlgebraicComplex) : MulRawValid z w := by
  exact ComplexRaw.mul_valid z.value.valid w.value.valid

def addCert (z w : AlgebraicComplex) : ComplexCert where
  raw := addRaw z w
  valid := addRaw_valid z w

def negCert (z : AlgebraicComplex) : ComplexCert where
  raw := negRaw z
  valid := negRaw_valid z

def mulCert (z w : AlgebraicComplex) (hvalid : MulRawValid z w) :
    ComplexCert where
  raw := mulRaw z w
  valid := hvalid

/-- Algebraic closure under addition, expressed as an annihilator-existence
target for the concrete addition algorithm. -/
def add_annihilator_exists (z w : AlgebraicComplex) : Prop :=
  Exists fun p : RatPoly.Coeffs =>
    RatPoly.Nonzero p /\ ComplexRootWitness p (addCert z w)

def neg_annihilator_exists (z : AlgebraicComplex) : Prop :=
  Exists fun p : RatPoly.Coeffs =>
    RatPoly.Nonzero p /\ ComplexRootWitness p (negCert z)

def mul_annihilator_exists
    (z w : AlgebraicComplex) (hvalid : MulRawValid z w) : Prop :=
  Exists fun p : RatPoly.Coeffs =>
    RatPoly.Nonzero p /\ ComplexRootWitness p (mulCert z w hvalid)

/-- Conditional constructor for a sum of algebraic complex numbers.  The proof
argument is the still-missing elimination/resultant step. -/
noncomputable def add (z w : AlgebraicComplex)
    (h : add_annihilator_exists z w) : AlgebraicComplex :=
  { value := addCert z w
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

/-- Conditional constructor for negation.  The proof argument is the polynomial
transform `X |-> -X`. -/
noncomputable def neg (z : AlgebraicComplex)
    (h : neg_annihilator_exists z) : AlgebraicComplex :=
  { value := negCert z
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

/-- Conditional constructor for a product.  Besides the elimination/resultant
annihilator proof, it explicitly requires validity of complex interval
multiplication for the two representatives. -/
noncomputable def mul (z w : AlgebraicComplex)
    (hvalid : MulRawValid z w)
    (h : mul_annihilator_exists z w hvalid) : AlgebraicComplex :=
  { value := mulCert z w hvalid
    annihilator := Classical.choose h
    nonzero_annihilator := (Classical.choose_spec h).1
    root_witness := (Classical.choose_spec h).2 }

/-- Inversion closure is recorded relationally for now, since the project does
not yet have a complex interval inverse algorithm packaged as `ComplexRaw`. -/
def inv_exists (z : AlgebraicComplex) (_hz : z.Nonzero) : Prop :=
  Exists fun w : AlgebraicComplex =>
  Exists fun _hvalid : MulRawValid z w =>
    (mulRaw z w).Equiv (ofRat 1).value.raw

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

/-! Coordinatewise conjugation is a finite operation on rational complex data.
The following certificate records the root-pair symmetry of `X^n - 1` without
selecting any non-rational root or invoking a general closure theorem. -/

def conjugate (z : QComplex) : QComplex :=
  { re := z.re, im := -z.im }

theorem qpow_conjugate (z : QComplex) (n : Nat) :
    qpow (conjugate z) n = conjugate (qpow z n) := by
  induction n with
  | zero =>
      simp [qpow, conjugate, QComplex.one]
  | succ n ih =>
      rw [qpow, ih, qpow]
      cases z with
      | mk re im =>
          cases hpow : qpow { re := re, im := im } n with
          | mk pre pim =>
              simp [conjugate, QComplex.mul]
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem isNthRoot_conjugate {n : Nat} {z : QComplex}
    (hz : IsNthRoot n z) : IsNthRoot n (conjugate z) := by
  unfold IsNthRoot at *
  rw [qpow_conjugate, hz]
  simp [conjugate, QComplex.one]

theorem qpow_mul (z w : QComplex) (n : Nat) :
    qpow (QComplex.mul z w) n =
      QComplex.mul (qpow z n) (qpow w n) := by
  induction n with
  | zero =>
      simp [qpow, QComplex.one, QComplex.mul]
      grind
  | succ n ih =>
      rw [qpow, ih, qpow, qpow]
      simp only [QComplex.mul]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.add_assoc, Rat.add_comm]

theorem isNthRoot_mul {n : Nat} {z w : QComplex}
    (hz : IsNthRoot n z) (hw : IsNthRoot n w) :
    IsNthRoot n (QComplex.mul z w) := by
  unfold IsNthRoot at *
  rw [qpow_mul, hz, hw]
  simp [QComplex.one, QComplex.mul]
  grind

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

/-- Multiplication of two certified `n`th roots stays certified by the same
`X^n - 1` annihilator.  This is a finite closure certificate for a concrete
algebraic operation; it does not choose a root or assert general FTA. -/
def exactRoot_mul (n : Nat) (hn : 0 < n)
    (z w : QComplex) (hz : IsNthRoot n z) (hw : IsNthRoot n w) : Root :=
  exactRoot n hn (QComplex.mul z w) (isNthRoot_mul hz hw)

/-- Package the conjugate root in the same finite `X^n - 1` witness. -/
def exactRoot_conjugate (n : Nat) (hn : 0 < n)
    (z : QComplex) (hz : IsNthRoot n z) : Root :=
  exactRoot n hn (conjugate z) (isNthRoot_conjugate hz)

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
def exists_root (p : Coeffs) (_hp : PositiveDegree p) : Prop :=
  Exists fun z : AlgebraicComplex => Root p z

end AlgPoly

structure AlgebraicFun where
  value : RealFunRaw
  polynomialAt : Rat -> List Rat

end ComputableAnalysis
