import ComputableAnalysis.RiemannHilbert.FiniteFiberBasis

/-! Executable constant-operator exponential coefficients. The recurrence is
linear in the initial vector and uses arbitrary valid represented operators.
Convergence is proved separately. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def coefficient (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) : Nat → Fiber n
  | 0 => x
  | k+1 => ratScale (1/((k+1 : Nat) : Rat)) (A.eval (coefficient A x k))

theorem coefficient_zero (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) :
    coefficient A x 0 = x := rfl

theorem coefficient_succ (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (k : Nat) :
    coefficient A x (k+1) = ratScale (1/((k+1 : Nat) : Rat)) (A.eval (coefficient A x k)) := rfl

theorem coefficient_congr (A B : ValueMap (Fiber n) (Fiber n)) (hAB : A.Equiv B)
    (x y : Fiber n) (hxy : x ≈ y) (k : Nat) : coefficient A x k ≈ coefficient B y k := by
  induction k with
  | zero => exact hxy
  | succ k ih => exact ratScale_congr _ (Setoid.trans (A.congr ih) (hAB _))

theorem coefficient_add (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x y : Fiber n) (k : Nat) :
    coefficient A (Fiber.add x y) k ≈ Fiber.add (coefficient A x k) (coefficient A y k) := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
      exact Setoid.trans
        (ratScale_congr _ (Setoid.trans (A.congr ih) (hA.1 _ _))) (ratScale_add _ _ _)

theorem coefficient_scale (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (x : Fiber n) (k : Nat) :
    coefficient A (Fiber.scale c x) k ≈ Fiber.scale c (coefficient A x k) := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
      exact Setoid.trans
        (ratScale_congr _ (Setoid.trans (A.congr ih) (hA.2 _ _))) (ratScale_scale _ _ _)

def coefficientMap (A : ValueMap (Fiber n) (Fiber n)) (k : Nat) : ValueMap (Fiber n) (Fiber n) :=
  ⟨fun x => coefficient A x k,
    fun h => coefficient_congr A A (fun _ => Setoid.refl _) _ _ h k⟩

theorem coefficientMap_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (k : Nat) :
    IsLinear (coefficientMap A k) :=
  ⟨fun x y => coefficient_add A hA x y k, fun c x => coefficient_scale A hA c x k⟩

/-- The exact coefficient equation for the constant differential equation. -/
theorem coefficient_equation (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (k : Nat) :
    ratScale ((k+1 : Nat) : Rat) (coefficient A x (k+1)) ≈ A.eval (coefficient A x k) := by
  intro i
  exact LocalODE.cancel_scale ((k+1 : Nat) : Rat) (LocalODE.succCast_ne_zero k)
    ((A.eval (coefficient A x k)).val i) ((A.eval (coefficient A x k)).property i)

end ComputableAnalysis.RiemannHilbert.MatrixExponential
