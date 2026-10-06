import ComputableAnalysis.RiemannHilbert.ExponentialOperatorBounds
import ComputableAnalysis.RiemannHilbert.ExponentialCommutingSum

/-! Exact commuting operator increments and their proved quadratic
exponential remainder. All exponentials are the independent entire interval
evaluators; only the operator increment is required to be small. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

theorem commuting_increment (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (x : Fiber n) :
    A.eval ((ValueMap.difference B A).eval x) ≈ (ValueMap.difference B A).eval (A.eval x) :=
  Setoid.trans (hA.sub (B.eval x) (A.eval x)) (Fiber.sub_congr (hAB x) (Setoid.refl _))

theorem increment_sum (A B : ValueMap (Fiber n) (Fiber n)) : (sumResidue A (ValueMap.difference B A)).Equiv B := by
  intro x i
  exact SeriesLimitLaws.add_difference ((B.eval x).val i) ((A.eval x).val i)
    ((B.eval x).property i) ((A.eval x).property i)

theorem value_increment_factor (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (x : Fiber n) :
    (value B hB operatorUnit).eval x ≈ (value A hA operatorUnit).eval
      ((value (ValueMap.difference B A) (ValueMap.difference_linear B A hB hA) operatorUnit).eval x) :=
  Setoid.trans (value_congr B (sumResidue A (ValueMap.difference B A)) hB
    (sumResidue_linear A _ hA (ValueMap.difference_linear B A hB hA))
    (fun y => Setoid.symm (increment_sum A B y)) operatorUnit operatorUnit (equiv_refl _ operatorUnit.property) x x (Setoid.refl _))
    (value_commuting_sum A _ hA (ValueMap.difference_linear B A hB hA) (commuting_increment A B hA hAB) operatorUnit x)

def incrementRemainder (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (x : Fiber n) : Fiber n :=
  Fiber.sub (Fiber.sub ((value B hB operatorUnit).eval x) ((value A hA operatorUnit).eval x))
    ((value A hA operatorUnit).eval ((ValueMap.difference B A).eval x))

theorem incrementRemainder_identity (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (x : Fiber n) :
    incrementRemainder A B hA hB x ≈ (value A hA operatorUnit).eval
      (Fiber.sub ((value (ValueMap.difference B A) (ValueMap.difference_linear B A hB hA) operatorUnit).eval x)
        (Fiber.add x ((ValueMap.difference B A).eval x))) := by
  let F := value A hA operatorUnit
  let T := ValueMap.difference B A
  let v := (value T (ValueMap.difference_linear B A hB hA) operatorUnit).eval x
  have hFl := value_linear A hA operatorUnit
  have he : incrementRemainder A B hA hB x ≈ Fiber.sub (F.eval v) (Fiber.add (F.eval x) (F.eval (T.eval x))) := by
    apply Setoid.trans (Fiber.sub_congr (Fiber.sub_congr (value_increment_factor A B hA hB hAB x) (Setoid.refl _)) (Setoid.refl _))
    intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (Fiber.sub (Fiber.sub (F.eval v) (F.eval x)) (F.eval (T.eval x))).property i)
      (hright := (Fiber.sub (F.eval v) (Fiber.add (F.eval x) (F.eval (T.eval x)))).property i)
    let V := ComplexRawQuotient.ofRaw ((F.eval v).val i) ((F.eval v).property i)
    let X := ComplexRawQuotient.ofRaw ((F.eval x).val i) ((F.eval x).property i)
    let Y := ComplexRawQuotient.ofRaw ((F.eval (T.eval x)).val i) ((F.eval (T.eval x)).property i)
    change (V-X)-Y=V-(X+Y)
    grind only
  exact Setoid.trans he (Setoid.symm (Setoid.trans (hFl.sub v (Fiber.add x (T.eval x)))
    (Fiber.sub_congr (Setoid.refl _) (hFl.1 x (T.eval x)))))

theorem incrementRemainder_bound (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x))
    (P T : Rat) (hP : 0 ≤ P) (hT : 0 ≤ T) (hsmall : T ≤ 1/4)
    (hAP : OperatorBound A P) (hDT : OperatorBound (ValueMap.difference B A) T)
    (C : Rat) (hC : 0 ≤ C) (x : Fiber n) (hx : CoordinateBound x C) :
    CoordinateBound (incrementRemainder A B hA hB x) ((32*suppliedValueBound P*T^2)*C) := by
  have hs := quadratic_remainder (ValueMap.difference B A) (ValueMap.difference_linear B A hB hA) T hT hsmall hDT C hC x hx
  have hb := value_supplied_bound A hA P hP hAP ((32*T^2)*C)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hT)) hC) _ hs
  have he : suppliedValueBound P*((32*T^2)*C)=(32*suppliedValueBound P*T^2)*C := by grind only
  rw [he] at hb
  exact bound_congr (Setoid.symm (incrementRemainder_identity A B hA hB hAB x)) hb

end ComputableAnalysis.RiemannHilbert.MatrixExponential
