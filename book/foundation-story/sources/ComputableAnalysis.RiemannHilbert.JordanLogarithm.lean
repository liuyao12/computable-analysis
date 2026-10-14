import ComputableAnalysis.RiemannHilbert.JordanShift
import ComputableAnalysis.RiemannHilbert.MatrixLogarithmSimilarity

/-! Finite logarithms of unipotent Jordan blocks of arbitrary rank. Rational
diagonal rescaling constructs the needed small basis. The independent entire
exponential recovers the original block, with no smallness in that basis. -/
namespace ComputableAnalysis.RiemannHilbert.JordanLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE JordanShift
set_option maxHeartbeats 1000000

def shrink : Rat := 1/128
theorem shrink_ne_zero : shrink ≠ 0 := by decide +kernel

theorem scaled_small (n : Nat) (r : Rat) (hr : 0 ≤ r) (hq : r ≤ MatrixLogarithm.contraction) :
    MatrixLogarithm.SmallOperator (scaled n r) := by
  intro B hB x hx i
  exact (bound_ratScale hr (offset_bound n 1 B hB x hx) i).mono
    (Rat.mul_le_mul_of_nonneg_right hq hB)

def smallShift (n : Nat) := scaled n shrink
theorem smallShift_linear (n : Nat) : IsLinear (smallShift n) := scaled_linear n shrink
theorem smallShift_small (n : Nat) : MatrixLogarithm.SmallOperator (smallShift n) :=
  scaled_small n shrink (by decide +kernel) (by decide +kernel)

def smallBasis (n : Nat) := basis n shrink shrink_ne_zero

def logarithm (n : Nat) := MatrixLogarithm.finitePrefix (shift n) MatrixLogarithm.unit n
theorem logarithm_linear (n : Nat) : IsLinear (logarithm n) :=
  MatrixLogarithm.prefix_linear (shift n) (shift_linear n) MatrixLogarithm.unit n

def monodromy (n : Nat) := MatrixLogarithm.identityPlus (shift n) MatrixLogarithm.unit
theorem monodromy_linear (n : Nat) : IsLinear (monodromy n) :=
  MatrixLogarithm.identityPlus_linear (shift n) (shift_linear n) MatrixLogarithm.unit

def transportedLogarithm (n : Nat) :=
  MatrixLogarithm.transportedValue (smallBasis n) (smallShift n) (smallShift_small n)

theorem transportedLogarithm_agreement (n : Nat) : (transportedLogarithm n).Equiv (logarithm n) :=
  MatrixLogarithm.transportedValue_finite (smallBasis n) (smallShift n) (smallShift_linear n)
    (smallShift_small n) n (scaled_nilpotent n shrink) (shift n) (basis_intertwines n shrink)

/-- The finite nilpotent formula is a logarithm of every unipotent Jordan
block, including ranks zero and one. Arbitrary represented vectors are allowed. -/
theorem exponential_logarithm (n : Nat) :
    (MatrixExponential.value (logarithm n) (logarithm_linear n) MatrixLogarithm.unit).Equiv (monodromy n) :=
  MatrixLogarithm.exponential_finite_of_small_basis (smallBasis n) (smallShift n) (smallShift_linear n)
    (smallShift_small n) n (scaled_nilpotent n shrink) (shift n) (shift_linear n) (basis_intertwines n shrink)

/-- The finite logarithm does not depend on the internal positive rational
scaling used to compute the Taylor evaluator in a small basis. -/
theorem scaling_agreement (n : Nat) (r : Rat) (hr : 0 < r) (hq : r ≤ MatrixLogarithm.contraction) :
    (MatrixLogarithm.transportedValue (basis n r (Rat.ne_of_gt hr)) (scaled n r)
      (scaled_small n r (Rat.le_of_lt hr) hq)).Equiv (logarithm n) :=
  MatrixLogarithm.transportedValue_finite (basis n r (Rat.ne_of_gt hr)) (scaled n r) (scaled_linear n r)
    (scaled_small n r (Rat.le_of_lt hr) hq) n (scaled_nilpotent n r) (shift n) (basis_intertwines n r)

def monodromyIso (n : Nat) : LinearIso n n := by
  let F := MatrixExponential.frame (logarithm n) (logarithm_linear n) MatrixLogarithm.unit
  have hFM : F.toValueIso.forward.Equiv (monodromy n) := exponential_logarithm n
  exact {
    toValueIso := {
      forward := monodromy n
      backward := F.toValueIso.backward
      backward_forward x := Setoid.trans (F.toValueIso.backward.congr (Setoid.symm (hFM x))) (F.toValueIso.backward_forward x)
      forward_backward x := Setoid.trans (Setoid.symm (hFM (F.toValueIso.backward.eval x))) (F.toValueIso.forward_backward x) }
    linear := monodromy_linear n }

theorem monodromy_inverse (n : Nat) (x : Fiber n) :
    (monodromyIso n).toValueIso.backward.eval ((monodromy n).eval x) ≈ x :=
  (monodromyIso n).toValueIso.backward_forward x

theorem logarithm_intertwines {n m : Nat} (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hJ : ∀ x, N.eval ((shift n).eval x) ≈ (shift m).eval (N.eval x)) (x : Fiber n) :
    N.eval ((logarithm n).eval x) ≈ (logarithm m).eval (N.eval x) :=
  MatrixLogarithm.finite_nilpotent_intertwines (shift n) (shift_linear n) n (shift_nilpotent n)
    (shift m) (shift_linear m) m (shift_nilpotent m) N hN hJ MatrixLogarithm.unit x

end ComputableAnalysis.RiemannHilbert.JordanLogarithm
