import ComputableAnalysis.RiemannHilbert.ExponentialNilpotent

/-! Bounds for the actual entire exponential from a supplied operator
bound. Sum agreement hides its first-box budget. The quadratic remainder
at identity is uniform over arbitrary represented operator increments. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

def OperatorBound (A : ValueMap (Fiber n) (Fiber n)) (P : Rat) : Prop :=
  ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (A.eval x) (P*B)

theorem coefficient_supplied_weight_bound (A : ValueMap (Fiber n) (Fiber n))
    (P : Rat) (hP : 0 ≤ P) (hAP : OperatorBound A P)
    (x : Fiber n) (B : Rat) (hB : 0 ≤ B) (hx : CoordinateBound x B) (k : Nat) :
    CoordinateBound (coefficient A x k) (weight P k*B) := by
  induction k with
  | zero => simpa only [coefficient,weight,Rat.one_mul] using hx
  | succ k ih =>
    have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
    have hr : 0 ≤ 1/((k+1 : Nat) : Rat) := by
      rw [Rat.div_def,Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 hd)
    have hs := bound_ratScale hr (hAP _ (Rat.mul_nonneg (weight_nonneg P hP k) hB) _ ih)
    have he : (1/((k+1 : Nat) : Rat))*(P*(weight P k*B))=weight P (k+1)*B := by
      simp only [weight,Rat.div_def,Rat.one_mul]
      grind only
    rw [he] at hs
    exact hs

theorem supplied_majorant (A : ValueMap (Fiber n) (Fiber n)) (P K : Rat)
    (hP : 0 ≤ P) (hK : 0 < K) (hAP : OperatorBound A P) :
    OperatorMajorant (coefficientMap A) (geometricBudget P K) K := by
  intro k B hB x hx i
  have hw := coefficient_supplied_weight_bound A P hP hAP x B hB hx k i
  have hg := Rat.mul_le_mul_of_nonneg_right (weight_geometric P K hP hK k) hB
  have hn : 0 ≤ geometricBudget P K*K^k*B := Rat.mul_nonneg
    (Rat.mul_nonneg (geometricBudget_nonneg P K) (Rat.pow_nonneg (Rat.le_of_lt hK))) hB
  exact hw.mono (by grind only)

theorem value_majorant_agreement (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (M K R : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ha : OperatorMajorant (coefficientMap A) M K) (z : Scalar) (hz : Small z.val R)
    (hq : 2*K*R ≤ (1 : Rat)/2) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    (value A hA z).eval x ≈ VectorSeries.value (coefficient A x) z (2*M*B) K R
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
      (operatorCoefficient_bound (coefficientMap A) M K B hB ha x hx) hz hq := by
  let S := pointRadius z
  have hS := Rat.le_of_lt S.property
  have hL := Rat.le_of_lt (rate_pos S.val hS)
  exact VectorSeries.value_congr _ _ z z (fun _ => Setoid.refl _) (equiv_refl _ z.property)
    (2*discBudget A S.val*LocalSystem.initialBound x) (rate S.val) S.val (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A S.val)) (LocalSystem.initialBound_nonneg x)) hL hS
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound (coefficientMap A) _ _ _ (LocalSystem.initialBound_nonneg x)
      (disc_majorant A hA S.val hS) x (LocalSystem.initialBound_valid x))
    (operatorCoefficient_bound (coefficientMap A) M K B hB ha x hx)
    (interior_bound S.val z (pointRadius_inside z)) hz
    (by have := rate_small S.val hS; have := Rat.mul_nonneg hL hS; grind only) hq

theorem value_majorant_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (M K R : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ha : OperatorMajorant (coefficientMap A) M K) (z : Scalar) (hz : Small z.val R)
    (hq : 2*K*R ≤ (1 : Rat)/2) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((value A hA z).eval x) (8*M*B) := by
  have hs := VectorSeries.value_bound (coefficient A x) z (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound (coefficientMap A) M K B hB ha x hx) hz hq
  have he : 4*(2*M*B)=8*M*B := by grind only
  rw [he] at hs
  exact bound_congr (Setoid.symm (value_majorant_agreement A hA M K R hM hK hR ha z hz hq B hB x hx)) hs

theorem value_majorant_close (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (M K R : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ha : OperatorMajorant (coefficientMap A) M K) (z : Scalar) (hz : Small z.val R)
    (hq : 2*K*R ≤ (1 : Rat)/2) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound (Fiber.sub ((value A hA z).eval x) ((finitePrefix A z N).eval x)) (8*M*B*(2*K*R)^N) := by
  have hs := VectorSeries.value_close (coefficient A x) z (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound (coefficientMap A) M K B hB ha x hx) hz hq N
  have he : 4*(2*M*B)*(2*K*R)^N=8*M*B*(2*K*R)^N := by grind only
  rw [he] at hs
  exact bound_congr (Fiber.sub_congr
    (Setoid.symm (value_majorant_agreement A hA M K R hM hK hR ha z hz hq B hB x hx)) (Setoid.refl _)) hs

theorem weight_le_power (P : Rat) (hP : 0 ≤ P) (k : Nat) : weight P k ≤ P^k := by
  induction k with
  | zero => simpa only [weight,Rat.pow_zero] using (Rat.le_refl : (1 : Rat) ≤ 1)
  | succ k ih =>
    have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
    have hd1 : (1 : Rat) ≤ ((k+1 : Nat) : Rat) := by exact_mod_cast (show 1 ≤ k+1 by omega)
    have hr : P/((k+1 : Nat) : Rat) ≤ P := by
      apply Rat.le_of_mul_le_mul_right (c := ((k+1 : Nat) : Rat)) ?_ hd
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)]
      simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left hd1 hP
    have h1 := Rat.mul_le_mul_of_nonneg_right hr (weight_nonneg P hP k)
    have h2 := Rat.mul_le_mul_of_nonneg_left ih hP
    change (P/((k+1 : Nat) : Rat))*weight P k ≤ P^(k+1)
    rw [Rat.pow_succ]
    exact Rat.le_trans h1 (by simpa only [Rat.mul_comm] using h2)

theorem small_majorant (A : ValueMap (Fiber n) (Fiber n)) (P : Rat) (hP : 0 ≤ P) (hAP : OperatorBound A P) :
    OperatorMajorant (coefficientMap A) 1 P := by
  intro k B hB x hx i
  have hs := coefficient_supplied_weight_bound A P hP hAP x B hB hx k i
  have hp := Rat.mul_le_mul_of_nonneg_right (weight_le_power P hP k) hB
  have hn : 0 ≤ P^k*B := Rat.mul_nonneg (Rat.pow_nonneg hP) hB
  exact hs.mono (by grind only)

def operatorUnit : Scalar := ⟨one,ofQComplex_valid _⟩
theorem operatorUnit_bound : Small operatorUnit.val 1 :=
  ⟨fun _ _ => by change (-1 : Rat) ≤ 1; decide +kernel,fun _ _ => Rat.le_refl,
    fun _ _ => by change (-1 : Rat) ≤ 0; decide +kernel,
    fun _ _ => by change (0 : Rat) ≤ 1; decide +kernel⟩

def suppliedValueBound (P : Rat) : Rat := 8*geometricBudget P (1/4)

theorem suppliedValueBound_nonneg (P : Rat) : 0 ≤ suppliedValueBound P :=
  Rat.mul_nonneg (by decide +kernel) (geometricBudget_nonneg P (1/4))

theorem value_supplied_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (P : Rat) (hP : 0 ≤ P) (hAP : OperatorBound A P)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((value A hA operatorUnit).eval x) (suppliedValueBound P*B) :=
  value_majorant_bound A hA (geometricBudget P (1/4)) (1/4) 1
    (geometricBudget_nonneg P (1/4)) (by decide +kernel) (by decide +kernel)
    (supplied_majorant A P (1/4) hP (by decide +kernel) hAP) operatorUnit operatorUnit_bound
    (by decide +kernel) B hB x hx

/-- The actual exponential has a quadratic operator remainder at identity.
The supplied contraction bound is on the increment, not on its exponential. -/
theorem quadratic_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (P : Rat) (hP : 0 ≤ P) (hsmall : P ≤ 1/4) (hAP : OperatorBound A P)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (Fiber.sub ((value A hA operatorUnit).eval x) (Fiber.add x (A.eval x))) ((32*P^2)*B) := by
  have hs := value_majorant_close A hA 1 P 1 (by decide +kernel) hP (by decide +kernel)
    (small_majorant A P hP hAP) operatorUnit operatorUnit_bound (by grind only) B hB x hx 2
  have he : 8*1*B*(2*P*1)^2=(32*P^2)*B := by
    simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul,Rat.mul_one]
    grind only
  rw [he] at hs
  have hp : (finitePrefix A operatorUnit 2).eval x ≈ Fiber.add x (A.eval x) :=
    Setoid.trans (nil_prefix_two A x operatorUnit) (Fiber.add_congr (Setoid.refl _)
      (fun i => one_mul_equiv _ ((A.eval x).property i)))
  exact bound_congr (Fiber.sub_congr (Setoid.refl _) hp) hs

end ComputableAnalysis.RiemannHilbert.MatrixExponential
