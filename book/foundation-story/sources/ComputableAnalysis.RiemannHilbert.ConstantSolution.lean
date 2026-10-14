import ComputableAnalysis.HolomorphicExamples
import ComputableAnalysis.ComplexRawQuotientAlgebra
import ComputableAnalysis.RiemannHilbert.RepresentedFiber

/-!
# Constructed holomorphic solutions of the zero system

This supplies actual derivative and derivative-continuity evidence for
arbitrary valid represented initial vectors. The constant family has exact
initial values and overlap agreement; no general solution classification or
sphere bundle construction is claimed here.
-/
namespace ComputableAnalysis.RiemannHilbert.ConstantSolution

open ComplexRaw FunctionTheory

def scalarMap (initial : Scalar) : Map :=
  affine zero initial.val (ofQComplex_valid QComplex.zero) initial.property

def holomorphic (initial : Scalar) : Holomorphic (scalarMap initial) :=
  affine_holomorphic zero initial.val (ofQComplex_valid QComplex.zero) initial.property

/-- The actual function evaluator equals its initial datum as a value. -/
theorem value (initial : Scalar) (z : ComplexRaw) (hz : z.Valid) :
    ((scalarMap initial).eval z).Equiv initial.val :=
  equiv_trans
    (add_valid (mul_valid (ofQComplex_valid QComplex.zero) hz) initial.property)
    (add_valid (ofQComplex_valid QComplex.zero) initial.property) initial.property
    (add_equiv (zero_mul_equiv z hz) (equiv_refl _ initial.property))
    (zero_add_equiv initial.val initial.property)

/-- This is a complex derivative theorem, rather than a formal jet identity. -/
theorem derivative_zero (initial : Scalar) (z : ComplexRaw) :
    ((holomorphic initial).derivative z).Equiv zero :=
  equiv_refl zero (ofQComplex_valid QComplex.zero)

/-- Local branches with equivalent initial data agree on every valid input. -/
theorem overlap (a b : Scalar) (hab : a.val.Equiv b.val)
    (z : ComplexRaw) (hz : z.Valid) :
    ((scalarMap a).eval z).Equiv ((scalarMap b).eval z) :=
  equiv_trans ((scalarMap a).valid z hz True.intro) a.property
    ((scalarMap b).valid z hz True.intro) (value a z hz)
    (equiv_trans a.property b.property ((scalarMap b).valid z hz True.intro)
      hab (equiv_symm (value b z hz)))

/-- A constructed solution vector of any finite rank. -/
def eval (initial : Fiber n) (z : Scalar) : Fiber n :=
  ⟨fun i => (scalarMap ⟨initial.val i, initial.property i⟩).eval z.val,
    fun i => (scalarMap ⟨initial.val i, initial.property i⟩).valid z.val z.property True.intro⟩

theorem eval_initial (initial : Fiber n) (z : Scalar) : eval initial z ≈ initial :=
  fun i => value ⟨initial.val i, initial.property i⟩ z.val z.property

theorem eval_congr {initial other : Fiber n} (h : initial ≈ other)
    (z w : Scalar) : eval initial z ≈ eval other w :=
  Setoid.trans (eval_initial initial z) (Setoid.trans h (Setoid.symm (eval_initial other w)))

/-- Values agree at any two supplied chart points; the coefficient is zero
and the solution extends across every finite complex point. -/
theorem eval_independent_point (initial : Fiber n) (z w : Scalar) :
    eval initial z ≈ eval initial w :=
  eval_congr (Setoid.refl initial) z w

end ComputableAnalysis.RiemannHilbert.ConstantSolution
