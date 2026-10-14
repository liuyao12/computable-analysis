import ComputableAnalysis.RiemannHilbert.LogarithmContinuationRefinement
import ComputableAnalysis.RiemannHilbert.StandardJordanLogarithm

/-! Jordan logarithms from a constructed continuation of the normalized
logarithm germ at one. Callers supply local route membership, not a scalar
logarithm or the exponential identity to be proved. -/
namespace ComputableAnalysis.RiemannHilbert.ContinuedJordanLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions NonzeroBoxSearch LogarithmContinuation

def zeroSeed : Scalar := ⟨zero,ofQComplex_valid _⟩
theorem one_nonzero : Nonzero oneScalar :=
  RepresentedReciprocal.nonzero_of_inverse oneScalar oneScalar (one_mul_equiv _ oneScalar.property)

def scalarBranch (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) : Scalar :=
  value p zeroSeed

theorem scalarBranch_exponential (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) :
    (MatrixExponential.scalarExponential (scalarBranch c hc p)).val.Equiv c.val :=
  value_exponential p zeroSeed MatrixExponential.scalarExponential_zero

def logarithm (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) :=
  StandardJordanLogarithm.logarithm n (scalarBranch c hc p) c (scalarBranch_exponential c hc p)

theorem logarithm_linear (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) :
    IsLinear (logarithm n c hc p) :=
  StandardJordanLogarithm.logarithm_linear n _ c (scalarBranch_exponential c hc p)

theorem exponential_logarithm (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) :
    (MatrixExponential.value (logarithm n c hc p) (logarithm_linear n c hc p) MatrixLogarithm.unit).Equiv
      (StandardJordanLogarithm.monodromy n c) :=
  StandardJordanLogarithm.exponential_logarithm n _ c (scalarBranch_exponential c hc p)

theorem logarithm_refines (n : Nat) (c : Scalar) (hc : Nonzero c)
    {p q : Chain oneScalar one_nonzero c hc} (h : Refines p q) :
    (logarithm n c hc p).Equiv (logarithm n c hc q) :=
  StandardJordanLogarithm.logarithm_congr n _ _ c c (scalarBranch_exponential c hc p) (scalarBranch_exponential c hc q)
    (value_refines h zeroSeed) (equiv_refl _ c.property)

def vector (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) (x : Fiber n) :=
  StandardJordanLogarithm.vector n (scalarBranch c hc p) c (scalarBranch_exponential c hc p) x

def vector_holomorphic (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (vector n c hc p x) :=
  StandardJordanLogarithm.vector_holomorphic n _ c (scalarBranch_exponential c hc p) x

theorem vector_derivative (n : Nat) (c : Scalar) (hc : Nonzero c) (p : Chain oneScalar one_nonzero c hc)
    (x : Fiber n) (hF : DomainVectorFunctions.Holomorphic (vector n c hc p x)) :
    DomainVectorFunctions.derivative (vector n c hc p x) hF MatrixLogarithm.unit True.intro ≈
      (logarithm n c hc p).eval ((StandardJordanLogarithm.monodromy n c).eval x) :=
  StandardJordanLogarithm.vector_derivative_at_unit n _ c (scalarBranch_exponential c hc p) x hF

end ComputableAnalysis.RiemannHilbert.ContinuedJordanLogarithm
