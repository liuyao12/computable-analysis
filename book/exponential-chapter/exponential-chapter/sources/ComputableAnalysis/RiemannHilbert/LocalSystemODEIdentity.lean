import ComputableAnalysis.RiemannHilbert.VectorODEFinite

/-! The actual finite-rank holomorphic local series satisfies its linear ODE. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory

namespace Fiber
theorem difference_split (x y p : Fiber n) : sub x y ≈ add (sub x p) (sub p y) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (sub x y).property i) (hright := (add (sub x p) (sub p y)).property i)
  change ComplexRawQuotient.ofRaw (x.val i) (x.property i)-ComplexRawQuotient.ofRaw (y.val i) (y.property i) =
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i)-ComplexRawQuotient.ofRaw (p.val i) (p.property i))+
    (ComplexRawQuotient.ofRaw (p.val i) (p.property i)-ComplexRawQuotient.ofRaw (y.val i) (y.property i))
  grind
end Fiber

namespace LocalSystem
open LocalODE
variable {n : Nat}

def coefficientValueMap (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (haB : OperatorMajorant a M K) (z : Scalar)
    (hz : interior (solutionRadius K hK).val z) : ValueMap (Fiber n) (Fiber n) :=
  operatorValue a z M K (solutionRadius K hK).val hM hK (Rat.le_of_lt (solutionRadius K hK).property)
    haB (interior_bound _ z hz) (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)

theorem localValue_close (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (N : Nat) :
    CoordinateBound (Fiber.sub (localValue a initial M K hM hK hMK haB z hz)
      (VectorSeries.block (coefficient a initial) z 0 N))
      (4*initialBound initial*(2*K*(solutionRadius K hK).val)^N) :=
  VectorSeries.value_close (coefficient a initial) z (initialBound initial) K (solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    (coefficient_majorant a initial M (initialBound initial) K hM (initialBound_nonneg initial) hK hMK haB
      (initialBound_valid initial))
    (interior_bound _ z hz) (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind) N

theorem localDerivative_close (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (N : Nat) :
    CoordinateBound (Fiber.sub (localDerivative a initial M K hM hK hMK haB z hz)
      (derivativeVectorBlock a initial z N))
      (derivativeTail (initialBound initial) K (solutionRadius K hK).val N) := by
  intro d
  have hs := BoundedSeries.sumDerivative_close_prefix (coordinateSeries a initial d) z.val
    (coordinateSeries_valid a initial d) z.property (initialBound initial) K (solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    (fun k => coefficient_majorant a initial M (initialBound initial) K hM (initialBound_nonneg initial) hK hMK haB
      (initialBound_valid initial) k d)
    (interior_bound _ z hz) (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind) N
  let D := localDerivative a initial M K hM hK hMK haB z hz
  have hp := BoundedSeries.derivativeBlock_valid (coordinateSeries a initial d) z.val
    (coordinateSeries_valid a initial d) z.property 0 N
  exact Small.congr (sub_valid (D.property d) hp)
    ((Fiber.sub D (derivativeVectorBlock a initial z N)).property d)
    (FunctionTheory.sub_congr (equiv_refl _ (D.property d))
      (equiv_symm (derivativeVectorBlock_coordinate a initial z N d))) hs

theorem localProduct_close (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (initial : Fiber n) (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar) (hz : interior (solutionRadius K hK).val z) (N : Nat) :
    CoordinateBound (Fiber.sub
      ((coefficientValueMap a M K hM hK haB z hz).eval (localValue a initial M K hM hK hMK haB z hz))
      ((operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N)))
      (64*M*initialBound initial*(2*K*(solutionRadius K hK).val)^N) := by
  let C := initialBound initial
  let R := (solutionRadius K hK).val
  let Y := localValue a initial M K hM hK hMK haB z hz
  let p := VectorSeries.block (coefficient a initial) z 0 N
  let A := coefficientValueMap a M K hM hK haB z hz
  have hC := initialBound_nonneg initial
  have hR := Rat.le_of_lt (solutionRadius K hK).property
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hlocal : 2*K*R ≤ (1 : Rat)/2 := by
    have := solutionRadius_small K hK
    have := Rat.mul_nonneg hK hR
    grind
  have hp := VectorSeries.block_bound (coefficient a initial) z C K R hC hK hR
    (coefficient_majorant a initial M C K hM hC hK hMK haB (initialBound_valid initial))
    (interior_bound _ z hz) hlocal 0 N
  simp only [Rat.pow_zero, Rat.mul_one] at hp
  have hf := operatorValue_difference_bound a ha z M K R (4*C*(2*K*R)^N) hM hK hR
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)) haB
    (interior_bound _ z hz) hlocal Y p (localValue_close a initial M K hM hK hMK haB z hz N)
  have hg := operatorValue_close a z M K R (4*C) hM hK hR (Rat.mul_nonneg (by decide) hC) haB
    (interior_bound _ z hz) hlocal p hp N
  have hs := bound_add hf hg
  have hbound : 8*M*(4*C*(2*K*R)^N)+8*M*(4*C)*(2*K*R)^N=64*M*C*(2*K*R)^N := by grind
  rw [hbound] at hs
  exact bound_congr (Setoid.symm (Fiber.difference_split (A.eval Y) ((operatorPrefixMap a z N).eval p) (A.eval p))) hs

/-- Exact functional ODE at every represented point of the constructed local
domain, at every finite rank, including rank zero. -/
theorem localValue_ode (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (initial : Fiber n) (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    localDerivative a initial M K hM hK hMK haB z hz ≈
      (coefficientValueMap a M K hM hK haB z hz).eval (localValue a initial M K hM hK hMK haB z hz) := by
  let C := initialBound initial
  let R := (solutionRadius K hK).val
  let Y := localValue a initial M K hM hK hMK haB z hz
  let D := localDerivative a initial M K hM hK hMK haB z hz
  let A := coefficientValueMap a M K hM hK haB z hz
  have hC := initialBound_nonneg initial
  have hR := Rat.le_of_lt (solutionRadius K hK).property
  have hlocal := solutionRadius_small K hK
  have h2 : 2*K*R ≤ (1 : Rat)/2 := by have := Rat.mul_nonneg hK hR; grind
  have he := odeError_shrinks M C K R hM hC hK hR hlocal
  intro d
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (odeError M C K R) he
  intro N
  let p := derivativeVectorBlock a initial z N
  let q := (operatorPrefixMap a z N).eval (VectorSeries.block (coefficient a initial) z 0 N)
  have hleft := localDerivative_close a initial M K hM hK hMK haB z hz N
  have hmiddle := finite_vector_product_bound a ha initial z M C K R hM hC hK hR hMK haB
    (initialBound_valid initial) (interior_bound _ z hz) h2 N
  have hright := localProduct_close a ha initial M K hM hK hMK haB z hz N
  have hs := LocalODE.small_add
    (LocalODE.small_add (hleft d)
      (RepresentedCauchySum.small_sub_symm (q.val d) (p.val d) (32*M*C*(8*K*R)^N) (hmiddle d)))
    (RepresentedCauchySum.small_sub_symm ((A.eval Y).val d) (q.val d) (64*M*C*(2*K*R)^N) (hright d))
  have hc := Small.congr
    ((Fiber.add (Fiber.add (Fiber.sub D p) (Fiber.sub p q)) (Fiber.sub q (A.eval Y))).property d)
    ((Fiber.sub D (A.eval Y)).property d) (equiv_symm (Fiber.difference_decompose D (A.eval Y) p q d)) hs
  simpa only [odeError, Rat.zero_add, C, R, D, A, Y, Fiber.sub] using hc

end LocalSystem
end ComputableAnalysis.RiemannHilbert
