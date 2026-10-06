import ComputableAnalysis.RiemannHilbert.OperatorPowerAlgebra
import ComputableAnalysis.RiemannHilbert.ExponentialIntertwiners

/-! Moving an arbitrary represented scalar from the operator to the
parameter preserves the independent entire exponential. Finite power laws
and the two explicit shrinking tails prove the full represented identity. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

def parameterProduct (a z : Scalar) : Scalar := ⟨mul a.val z.val,mul_valid a.property z.property⟩

theorem power_product (a z : Scalar) (k : Nat) :
    (mul (power z.val k) (power a.val k)).Equiv (power (parameterProduct a z).val k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (power_valid z.val z.property k) (power_valid a.val a.property k))
    (hright := power_valid (parameterProduct a z).val (parameterProduct a z).property k)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ComplexRawQuotient.ofRaw (power z.val k) (power_valid z.val z.property k) *
    ComplexRawQuotient.ofRaw (power a.val k) (power_valid a.val a.property k) =
    ComplexRawQuotient.ofRaw (power (parameterProduct a z).val k) (power_valid (parameterProduct a z).val (parameterProduct a z).property k)
  rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power]
  change Z^k*A^k=(A*Z)^k
  induction k with
  | zero => change (1 : ScalarAlgebra.Value)*1=1; grind only
  | succ k ih => change (Z^k*Z)*(A^k*A)=(A*Z)^k*(A*Z); grind only

theorem coefficient_scaled_operator (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (a : Scalar) (x : Fiber n) (k : Nat) :
    coefficient (OperatorPower.scaled A a) x k ≈
      Fiber.scale ⟨power a.val k,power_valid a.val a.property k⟩ (coefficient A x k) := by
  let p : Scalar := ⟨power a.val k,power_valid a.val a.property k⟩
  have h1 : coefficient (OperatorPower.scaled A a) x k ≈
      ratScale (1/factorialRat k) (Fiber.scale p ((Neumann.power A k).eval x)) :=
    Setoid.trans (coefficient_factorial_power _ (OperatorPower.scaled_linear A hA a) x k)
      (ratScale_congr _ (OperatorPower.power_scaled A hA a x k))
  exact Setoid.trans h1 (Setoid.trans (ratScale_scale _ p _)
    (Fiber.scale_congr (equiv_refl _ p.property) (Setoid.symm (coefficient_factorial_power A hA x k))))

theorem term_scaled_operator (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (a z : Scalar) (x : Fiber n) (k : Nat) :
    VectorSeries.term (coefficient (OperatorPower.scaled A a) x) z k ≈
      VectorSeries.term (coefficient A x) (parameterProduct a z) k :=
  Setoid.trans (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property k))
    (coefficient_scaled_operator A hA a x k))
    (Setoid.trans (Fiber.scale_scale ⟨power z.val k,power_valid z.val z.property k⟩
      ⟨power a.val k,power_valid a.val a.property k⟩ (coefficient A x k))
      (Fiber.scale_congr (power_product a z k) (Setoid.refl (coefficient A x k))))

theorem prefix_scaled_operator (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (a z : Scalar) (N : Nat) :
    (finitePrefix (OperatorPower.scaled A a) z N).Equiv (finitePrefix A (parameterProduct a z) N) :=
  fun x => vectorBlock_congr _ _ (term_scaled_operator A hA a z x) 0 N

/-- Scaling the represented residue agrees with scaling the represented
parameter. All finite ranks and arbitrary valid scalar coefficients occur. -/
theorem value_scaled_operator (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (a z : Scalar) :
    (value (OperatorPower.scaled A a) (OperatorPower.scaled_linear A hA a) z).Equiv
      (value A hA (parameterProduct a z)) := by
  intro x
  let B := OperatorPower.scaled A a
  let hB := OperatorPower.scaled_linear A hA a
  let w := parameterProduct a z
  let R := pointRadius z
  let S := pointRadius w
  let C := LocalSystem.initialBound x
  have hC := LocalSystem.initialBound_nonneg x
  let e := fun k : Nat => 8*discBudget B R.val*C*(2*rate R.val*R.val)^k
  let f := fun k : Nat => 8*discBudget A S.val*C*(2*rate S.val*S.val)^k
  have he := RepresentedCauchySum.sum_shrinks _ _ (prefix_error_shrinks B R C hC) (prefix_error_shrinks A S C hC)
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ he
  intro k
  have hl := value_prefix_close B hB R z (pointRadius_inside z) C hC x (LocalSystem.initialBound_valid x) k
  have hr := value_prefix_close A hA S w (pointRadius_inside w) C hC x (LocalSystem.initialBound_valid x) k
  have hp := prefix_scaled_operator A hA a z k x
  have hb : CoordinateBound (Fiber.sub ((finitePrefix B z k).eval x) ((value A hA w).eval x)) (f k) :=
    bound_congr (Setoid.symm (Fiber.sub_congr hp (Setoid.refl _)))
      (fun j => RepresentedCauchySum.small_sub_symm _ _ _ (hr j))
  have hs := small_add (hl i) (hb i)
  have ht := Small.congr
    ((Fiber.add (Fiber.sub ((value B hB z).eval x) ((finitePrefix B z k).eval x))
      (Fiber.sub ((finitePrefix B z k).eval x) ((value A hA w).eval x))).property i)
    ((Fiber.sub ((value B hB z).eval x) ((value A hA w).eval x)).property i)
    (equiv_symm (Fiber.difference_split _ _ _ i)) hs
  simpa only [Rat.zero_add,Fiber.sub] using ht

end ComputableAnalysis.RiemannHilbert.MatrixExponential
