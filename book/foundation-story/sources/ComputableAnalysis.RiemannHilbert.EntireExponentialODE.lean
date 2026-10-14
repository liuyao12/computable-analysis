import ComputableAnalysis.RiemannHilbert.EntireExponentialHolomorphic
import ComputableAnalysis.RiemannHilbert.LinearDifference

/-! The actual entire exponential satisfies the constant linear ODE. Finite
prefix equations and independently shrinking value and derivative tails
prove the identity; it is not an assumed property of a certificate. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}

theorem derivativeTerm_image (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (z : Scalar) (k : Nat) (i : Fin n) :
    (BoundedSeries.derivativeTerm (fun j => (coefficient A x j).val i) z.val k).Equiv
      ((A.eval (VectorSeries.term (coefficient A x) z k)).val i) := by
  let p : Scalar := ⟨power z.val k, power_valid z.val z.property k⟩
  let v := coefficient A x (k+1)
  have hc : ratScale ((k+1 : Nat) : Rat) (Fiber.scale p v) ≈
      A.eval (Fiber.scale p (coefficient A x k)) :=
    Setoid.trans (ratScale_scale _ p v)
      (Setoid.trans (Fiber.scale_congr (equiv_refl _ p.property) (coefficient_equation A x k))
        (Setoid.symm (hA.2 p _)))
  exact equiv_trans (BoundedSeries.derivativeTerm_valid _ z.val (fun j => (coefficient A x j).property i) z.property k)
    ((ratScale ((k+1 : Nat) : Rat) (Fiber.scale p v)).property i)
    ((A.eval (VectorSeries.term (coefficient A x) z k)).property i)
    (scaleRat_equiv (mul_comm_equiv (v.val i) p.val (v.property i) p.property)) (hc i)

theorem derivativeBlock_image (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (z : Scalar) (N : Nat) (i : Fin n) :
    (BoundedSeries.derivativeBlock (fun j => (coefficient A x j).val i) z.val 0 N).Equiv
      ((A.eval (VectorSeries.block (coefficient A x) z 0 N)).val i) := by
  induction N with
  | zero => exact equiv_symm (hA.zero i)
  | succ N ih =>
      change (add (BoundedSeries.derivativeBlock (fun j => (coefficient A x j).val i) z.val 0 N)
        (BoundedSeries.derivativeTerm (fun j => (coefficient A x j).val i) z.val (0+N))).Equiv _
      simp only [Nat.zero_add]
      have hv : (add (BoundedSeries.derivativeBlock (fun j => (coefficient A x j).val i) z.val 0 N)
          (BoundedSeries.derivativeTerm (fun j => (coefficient A x j).val i) z.val N)).Valid :=
        add_valid
          (BoundedSeries.derivativeBlock_valid (fun j => (coefficient A x j).val i) z.val
            (fun j => (coefficient A x j).property i) z.property 0 N)
          (BoundedSeries.derivativeTerm_valid (fun j => (coefficient A x j).val i) z.val
            (fun j => (coefficient A x j).property i) z.property N)
      exact equiv_trans
        hv
        ((Fiber.add (A.eval (VectorSeries.block (coefficient A x) z 0 N))
          (A.eval (VectorSeries.term (coefficient A x) z N))).property i)
        ((A.eval (VectorSeries.block (coefficient A x) z 0 (N+1))).property i)
        (add_equiv ih (derivativeTerm_image A hA x z N i))
        (by simpa only [VectorSeries.block, vectorBlock, Nat.zero_add] using
          equiv_symm (hA.1 (VectorSeries.block (coefficient A x) z 0 N)
            (VectorSeries.term (coefficient A x) z N) i))

theorem onDisc_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (x : Fiber n) (z : Scalar) (hz : interior R.val z) :
    DomainVectorFunctions.derivative (discVector A hA R x) (discVector_holomorphic A hA R x) z hz ≈
      A.eval ((onDisc A hA R z hz).eval x) := by
  let M := discBudget A R.val
  let K := rate R.val
  let E := LocalSystem.initialBound x
  let C := 2*M*E
  let B := ValueMap.linearBound A
  let D := DomainVectorFunctions.derivative (discVector A hA R x) (discVector_holomorphic A hA R x) z hz
  let Y := (onDisc A hA R z hz).eval x
  have hM : 0 ≤ M := discBudget_nonneg A R.val
  have hK : 0 ≤ K := Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))
  have hE : 0 ≤ E := LocalSystem.initialBound_nonneg x
  have hC : 0 ≤ C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hE
  have hR := Rat.le_of_lt R.property
  have hB : 0 ≤ B := ValueMap.linearBound_nonneg A
  have hq : 0 ≤ 2*K*R.val := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have h8 : 8*K*R.val ≤ (1 : Rat)/2 := rate_small R.val hR
  have h2 : 2*K*R.val ≤ (1 : Rat)/2 := by grind
  have h4 : 4*K*R.val ≤ (1 : Rat)/2 := by grind
  have he := RepresentedCauchySum.sum_shrinks _ _ (derivativeTail_shrinks C K R.val hC hK hR h4)
    (SeriesLimitLaws.shrinks_scale _ (operatorError_shrinks M E K R.val hM hE hK hR h2) B hB)
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ he
  intro N
  let p := VectorSeries.block (coefficient A x) z 0 N
  have hleft := BoundedSeries.sumDerivative_close_prefix (fun j => (coefficient A x j).val i) z.val
    (fun j => (coefficient A x j).property i) z.property C K R.val hC hK hR
    (fun j => operatorCoefficient_bound (coefficientMap A) M K E hE (disc_majorant A hA R.val hR)
      x (LocalSystem.initialBound_valid x) j i) (interior_bound R.val z hz) h4 N
  have hl : Small (sub (D.val i) ((A.eval p).val i)) (derivativeTail C K R.val N) :=
    Small.congr
      (sub_valid (D.property i) (BoundedSeries.derivativeBlock_valid _ z.val
        (fun j => (coefficient A x j).property i) z.property 0 N))
      (sub_valid (D.property i) ((A.eval p).property i))
      (FunctionTheory.sub_congr (equiv_refl _ (D.property i)) (derivativeBlock_image A hA x z N i)) hleft
  have hy : CoordinateBound (Fiber.sub Y p) (8*M*E*(2*K*R.val)^N) :=
    operatorValue_close (coefficientMap A) z M K R.val E hM hK hR hE
      (disc_majorant A hA R.val hR) (interior_bound R.val z hz) h2 x (LocalSystem.initialBound_valid x) N
  have hb : 0 ≤ 8*M*E*(2*K*R.val)^N :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hE) (Rat.pow_nonneg hq)
  have hr := ValueMap.difference_bound A hA B (ValueMap.linear_bound A hA) _ hb Y p hy
  have hs := LocalODE.small_add hl
    (RepresentedCauchySum.small_sub_symm _ _ _ (hr i))
  have hc := Small.congr
    (add_valid (sub_valid (D.property i) ((A.eval p).property i))
      (sub_valid ((A.eval p).property i) ((A.eval Y).property i)))
    (sub_valid (D.property i) ((A.eval Y).property i))
    (equiv_symm (Fiber.difference_split D (A.eval Y) (A.eval p) i)) hs
  simpa only [Rat.zero_add] using hc

/-- Exact derivative identity on the whole represented complex plane. -/
theorem vector_derivative_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (z : Scalar) :
    DomainVectorFunctions.derivative (vector A hA x) (vector_holomorphic A hA x) z True.intro ≈
      A.eval ((value A hA z).eval x) :=
  onDisc_derivative_ode A hA (pointRadius z) x z (pointRadius_inside z)

/-- The equation applies to every independently justified holomorphic
witness, rather than to an internal derivative name alone. -/
theorem vector_derivative_ode_of_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (hH : DomainVectorFunctions.Holomorphic (vector A hA x)) (z : Scalar) :
    DomainVectorFunctions.derivative (vector A hA x) hH z True.intro ≈ A.eval ((value A hA z).eval x) :=
  Setoid.trans (DomainVectorFunctions.derivative_unique _ hH (vector_holomorphic A hA x) z True.intro)
    (vector_derivative_ode A hA x z)

theorem derivative_ode_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : A.Equiv B) (x y : Fiber n) (hxy : x ≈ y) (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hH : DomainVectorFunctions.Holomorphic (vector A hA x))
    (hJ : DomainVectorFunctions.Holomorphic (vector B hB y)) :
    DomainVectorFunctions.derivative (vector A hA x) hH z True.intro ≈
      DomainVectorFunctions.derivative (vector B hB y) hJ w True.intro :=
  Setoid.trans (vector_derivative_ode_of_holomorphic A hA x hH z)
    (Setoid.trans (Setoid.trans (A.congr (value_congr A B hA hB hAB z w hzw x y hxy)) (hAB _))
      (Setoid.symm (vector_derivative_ode_of_holomorphic B hB y hJ w)))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
