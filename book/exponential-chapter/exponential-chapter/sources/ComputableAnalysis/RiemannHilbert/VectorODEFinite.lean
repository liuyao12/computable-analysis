import ComputableAnalysis.RiemannHilbert.VectorKernelEvaluation

/-! Exact finite ODE products and explicit bounds on their omitted region. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

theorem finite_vector_product (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (initial : Fiber n) (z : Scalar) (N : Nat) :
    Fiber.sub
      ((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N))
      (derivativeVectorBlock a initial z N) ≈
      vectorMissing a (coefficient a initial) z N := by
  intro d
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub
      ((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N))
      (derivativeVectorBlock a initial z N)).property d)
    (hright := (vectorMissing a (coefficient a initial) z N).property d)
  change ComplexRawQuotient.ofRaw
    (((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N)).val d)
      (((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N)).property d) -
    ComplexRawQuotient.ofRaw ((derivativeVectorBlock a initial z N).val d) ((derivativeVectorBlock a initial z N).property d) =
    ComplexRawQuotient.ofRaw ((vectorMissing a (coefficient a initial) z N).val d) ((vectorMissing a (coefficient a initial) z N).property d)
  rw [operatorRectangle_image a ha (coefficient a initial) z N d,
    derivativeVectorBlock_image a initial z N d, vectorMissing_image a ha (coefficient a initial) z N d,
    FiniteProducts.rectangular_kernel]
  generalize FiniteProducts.kernelTriangle (kernelValue a (coefficient a initial) z d) N = x
  generalize FiniteProducts.partialSum
    (fun i => FiniteProducts.block (kernelValue a (coefficient a initial) z d i) (N-i) i) N = y
  grind

theorem vectorMissing_bound (a : Nat → ValueMap (Fiber n) (Fiber n)) (t : Nat → Fiber n)
    (z : Scalar) (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (haB : OperatorMajorant a M K) (ht : ∀ k, CoordinateBound (t k) (C*K^k))
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    CoordinateBound (vectorMissing a t z N) (32*M*C*(8*K*R)^N) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hB : 0 ≤ 16*M*C*(2*K*R)^N :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC) (Rat.pow_nonneg hq)
  have hs : CoordinateBound (vectorMissing a t z N) ((N : Rat)*(16*M*C*(2*K*R)^N)) := by
    apply vectorBlock_uniform _ (16*M*C*(2*K*R)^N) hB 0 N
    intro i hi
    simp only [Nat.zero_add]
    have htail : 0 ≤ 4*C*(2*K*R)^(N-i) :=
      Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)
    have hop := haB i (4*C*(2*K*R)^(N-i)) htail (VectorSeries.block t z (N-i) i)
      (VectorSeries.block_bound t z C K R hC hK hR ht hz hlocal (N-i) i)
    have hOpB : 0 ≤ 2*M*K^i*(4*C*(2*K*R)^(N-i)) :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (Rat.pow_nonneg hK)) htail
    have hp := bound_scale (x := (a i).eval (VectorSeries.block t z (N-i) i)) (c := powerScalar z i)
      (B := (2*R)^i) (C := 2*M*K^i*(4*C*(2*K*R)^(N-i)))
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hR)) hOpB
      (power_small z.val z.property R hR hz i) hop
    have he : (2*R)^i*K^i=(2*K*R)^i := by
      rw [← rational_mul_pow]; congr 1; grind
    have heq : (2*K*R)^i*(2*K*R)^(N-i)=(2*K*R)^N := by
      rw [← rational_pow_add]; congr 1; omega
    have hconst : 2*(2*R)^i*(2*M*K^i*(4*C*(2*K*R)^(N-i)))=16*M*C*(2*K*R)^N := by
      calc
        _ = (16*M*C)*(((2*R)^i*K^i)*(2*K*R)^(N-i)) := by grind
        _ = _ := by rw [he, heq]
    rw [hconst] at hp
    exact hp
  intro d
  apply (hs d).mono
  have hN : N ≤ (N+2)*(N+1) := by
    calc
      N ≤ N+2 := by omega
      _ ≤ (N+2)*(N+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hindex : (N : Rat) ≤ 2*(4 : Rat)^N := by
    rw [← cast_four_pow]
    exact_mod_cast Nat.le_trans hN (quadratic_index_bound N)
  have hh := Rat.mul_le_mul_of_nonneg_right hindex hB
  have he : (8*K*R)^N=(4 : Rat)^N*(2*K*R)^N := by
    rw [← rational_mul_pow]; congr 1; grind
  rw [he]
  grind

theorem finite_vector_product_bound (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (initial : Fiber n) (z : Scalar) (M C K R : Rat)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (hinit : CoordinateBound initial C)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    CoordinateBound (Fiber.sub
      ((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N))
      (derivativeVectorBlock a initial z N)) (32*M*C*(8*K*R)^N) :=
  bound_congr (Setoid.symm (finite_vector_product a ha initial z N))
    (vectorMissing_bound a (coefficient a initial) z M C K R hM hC hK hR haB
      (coefficient_majorant a initial M C K hM hC hK hMK haB hinit) hz hlocal N)

end ComputableAnalysis.RiemannHilbert.LocalSystem
