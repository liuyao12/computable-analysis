import ComputableAnalysis.RiemannHilbert.ExponentialMajorant
import ComputableAnalysis.RiemannHilbert.NeumannFinite

/-! Identification of the exponential coefficients with factorial-scaled
operator powers. This connects the fast recurrence to the usual series,
without identifying raw programs or appealing to completed scalars. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n m : Nat}

theorem ratScale_as_scalar (r : Rat) (x : Fiber n) :
    ratScale r x ≈ Fiber.scale ⟨scaleRat r one, scaleRat_valid (ofQComplex_valid _)⟩ x := by
  intro i
  exact equiv_trans (scaleRat_valid (x.property i))
    (scaleRat_valid (mul_valid (ofQComplex_valid _) (x.property i)))
    (mul_valid (scaleRat_valid (ofQComplex_valid _)) (x.property i))
    (scaleRat_equiv (r := r) (equiv_symm (one_mul_equiv _ (x.property i))))
    (scaleRat_mul_equiv r one (x.val i) (ofQComplex_valid _) (x.property i))

theorem linear_ratScale (A : ValueMap (Fiber n) (Fiber m)) (hA : IsLinear A) (r : Rat) (x : Fiber n) :
    A.eval (ratScale r x) ≈ ratScale r (A.eval x) :=
  Setoid.trans (A.congr (ratScale_as_scalar r x))
    (Setoid.trans (hA.2 _ x) (Setoid.symm (ratScale_as_scalar r (A.eval x))))

theorem factorialCoefficient_succ (k : Nat) :
    FormalPowerSeries.expCoeff (k+1) = (1/((k+1 : Nat) : Rat))*FormalPowerSeries.expCoeff k := by
  have h := congrFun FormalPowerSeries.expCoeff_derivative k
  change ((k+1 : Nat) : Rat)*FormalPowerSeries.expCoeff (k+1) = FormalPowerSeries.expCoeff k at h
  calc
    _ = (1/((k+1 : Nat) : Rat))*(((k+1 : Nat) : Rat)*FormalPowerSeries.expCoeff (k+1)) := by
      rw [Rat.div_def, Rat.one_mul]
      have he : ((k+1 : Nat) : Rat)⁻¹*((k+1 : Nat) : Rat) = 1 := by
        rw [Rat.mul_comm, Rat.mul_inv_cancel _ (succCast_ne_zero k)]
      rw [← Rat.mul_assoc, he, Rat.one_mul]
    _ = _ := by rw [h]

theorem weight_one_factorial (k : Nat) : weight 1 k = 1/factorialRat k := by
  change weight 1 k = FormalPowerSeries.expCoeff k
  induction k with
  | zero => decide +kernel
  | succ k ih => rw [weight, ih, factorialCoefficient_succ]

/-- The coefficient of degree k is exactly the kth operator power divided
by k factorial, for every represented initial vector. -/
theorem coefficient_factorial_power (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (k : Nat) :
    coefficient A x k ≈ ratScale (1/factorialRat k) ((Neumann.power A k).eval x) := by
  change coefficient A x k ≈ ratScale (FormalPowerSeries.expCoeff k) ((Neumann.power A k).eval x)
  induction k with
  | zero =>
      have he : FormalPowerSeries.expCoeff 0 = 1 := by decide +kernel
      rw [he]
      exact fun i => equiv_symm (scaleRat_one_equiv (x.val i) (x.property i))
  | succ k ih =>
      rw [coefficient_succ, factorialCoefficient_succ]
      exact Setoid.trans (ratScale_congr _ (A.congr ih))
        (Setoid.trans (ratScale_congr _ (linear_ratScale A hA _ _))
          (fun i => scaleRat_scaleRat_equiv _ _ (((Neumann.power A (k+1)).eval x).val i)
            (((Neumann.power A (k+1)).eval x).property i)))

theorem coefficient_unique (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (y : Nat → Fiber n)
    (h0 : x ≈ y 0) (hEq : ∀ k, ratScale ((k+1 : Nat) : Rat) (y (k+1)) ≈ A.eval (y k)) (k : Nat) :
    coefficient A x k ≈ y k := by
  induction k with
  | zero => exact h0
  | succ k ih =>
      exact Setoid.trans (ratScale_congr _ (Setoid.trans (A.congr ih) (Setoid.symm (hEq k))))
        (fun i => cancel_scale_reverse _ (succCast_ne_zero k) ((y (k+1)).val i) ((y (k+1)).property i))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
