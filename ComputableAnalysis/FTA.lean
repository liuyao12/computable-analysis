import ComputableAnalysis.AlgebraicNumbers

/-!
# Fundamental theorem of algebra targets

FTA sits above the algebraic-number layer.  Exact rational-complex roots and
roots of unity are supplied by `AlgebraicNumbers.lean`; this file records the
global theorem targets and small base cases.
-/

namespace ComputableAnalysis

def IsAlgebraicRoot (coeffs : CPoly.Coeffs) (z : AlgebraicComplex) : Prop :=
  IsComputableRoot coeffs z.value

/-- The exact root of the monic linear polynomial `X - r`. -/
theorem monicLinear_exact_root (r : QComplex) :
    CPoly.hasExactRoot [QComplex.neg r, QComplex.one] r := by
  simp [CPoly.hasExactRoot, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.neg, QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem monicLinear_positiveDegree (r : QComplex) :
    CPoly.positiveDegree [QComplex.neg r, QComplex.one] := by
  refine Exists.intro 1 ?_
  refine Exists.intro QComplex.one ?_
  simp [QComplex.one, QComplex.zero]

/-- First constructive FTA base case: every monic linear complex polynomial
has its evident computable root. -/
theorem monicLinear_has_computable_root (r : QComplex) :
    Exists fun z : ComplexCert =>
      IsComputableRoot [QComplex.neg r, QComplex.one] z := by
  refine Exists.intro (exactComplexCert r) ?_
  exact exactRoot_is_computable (monicLinear_exact_root r)

/-- Algebraic-number version of the monic-linear base case. -/
theorem monicLinear_has_algebraic_root (r : QComplex) :
    Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot [QComplex.neg r, QComplex.one] z := by
  refine Exists.intro (AlgebraicComplex.ofQComplex r) ?_
  exact exactRoot_is_computable (monicLinear_exact_root r)

abbrev imaginaryUnit : QComplex := RootsOfUnity.imaginaryUnitQ

def zSqPlusOne : CPoly.Coeffs := [QComplex.one, QComplex.zero, QComplex.one]

theorem zSqPlusOne_i_exact_root :
    CPoly.hasExactRoot zSqPlusOne imaginaryUnit := by
  simp [CPoly.hasExactRoot, zSqPlusOne, imaginaryUnit,
    RootsOfUnity.imaginaryUnitQ, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem zSqPlusOne_has_computable_root :
    Exists fun z : ComplexCert => IsComputableRoot zSqPlusOne z := by
  refine Exists.intro RootsOfUnity.imaginaryUnit.number.value ?_
  exact exactRoot_is_computable zSqPlusOne_i_exact_root

theorem zSqPlusOne_has_algebraic_root :
    Exists fun z : AlgebraicComplex => IsAlgebraicRoot zSqPlusOne z := by
  refine Exists.intro RootsOfUnity.imaginaryUnit.number ?_
  exact exactRoot_is_computable zSqPlusOne_i_exact_root

/-- Constructive/computable form of the Fundamental Theorem of Algebra target. -/
def ComputableFTA : Prop :=
  forall coeffs : CPoly.Coeffs,
    CPoly.positiveDegree coeffs ->
      Exists fun z : ComplexCert => IsComputableRoot coeffs z

/-- Algebraic-number form of FTA for rational-complex coefficient polynomials.

This is the sharper target for this project: the root is not just computable,
but packaged as an algebraic complex number with its own rational annihilator.
-/
def AlgebraicFTA : Prop :=
  forall coeffs : CPoly.Coeffs,
    CPoly.positiveDegree coeffs ->
      Exists fun z : AlgebraicComplex => IsAlgebraicRoot coeffs z

theorem ComputableFTA_of_AlgebraicFTA :
    AlgebraicFTA -> ComputableFTA := by
  intro h coeffs hp
  rcases h coeffs hp with ⟨z, hz⟩
  exact ⟨z.value, hz⟩

end ComputableAnalysis
