import ComputableAnalysis.RiemannHilbert.OperatorSeries

/-! Quantitative continuity of the constructed coefficient operator. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

theorem operatorPrefix_bound (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (M K R B : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hB : 0 ≤ B) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound ((operatorPrefixMap a z N).eval x) (8*M*B) := by
  have hs := VectorSeries.block_bound (fun k => (a k).eval x) z (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound a M K B hB haB x hx) hz hlocal 0 N
  have he : 4*(2*M*B)*(2*K*R)^0=8*M*B := by rw [Rat.pow_zero]; grind
  rw [he] at hs; exact hs

theorem operatorError_shrinks (M B K R : Rat)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) : ShrinksToZero (fun N => 8*M*B*(2*K*R)^N) := by
  have hs := tail_bound_shrinks (2*M*B) (2*K*R)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  have he : (fun N : Nat => 8*M*B*(2*K*R)^N) = (fun N => 4*(2*M*B)*(2*K*R)^N) := by
    funext N; grind
  rw [he]; exact hs

/-- The operator's bound on a difference is derived from finite linearity and
the explicit errors of its two constructed sums. -/
theorem operatorValue_difference_bound (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (z : Scalar) (M K R E : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hE : 0 ≤ E) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (x y : Fiber n)
    (hxy : CoordinateBound (Fiber.sub x y) E) :
    CoordinateBound (Fiber.sub
      ((operatorValue a z M K R hM hK hR haB hz hlocal).eval x)
      ((operatorValue a z M K R hM hK hR haB hz hlocal).eval y)) (8*M*E) := by
  let f := operatorValue a z M K R hM hK hR haB hz hlocal
  let e := fun N : Nat => 8*M*initialBound x*(2*K*R)^N+8*M*initialBound y*(2*K*R)^N
  have he : ShrinksToZero e := RepresentedCauchySum.sum_shrinks _ _
    (operatorError_shrinks M (initialBound x) K R hM (initialBound_nonneg x) hK hR hlocal)
    (operatorError_shrinks M (initialBound y) K R hM (initialBound_nonneg y) hK hR hlocal)
  intro i
  apply SeriesLimitLaws.small_of_prefix_bound _ ((Fiber.sub (f.eval x) (f.eval y)).property i)
    (fun N => (Fiber.sub ((operatorPrefixMap a z N).eval x) ((operatorPrefixMap a z N).eval y)).val i)
    (fun N => (Fiber.sub ((operatorPrefixMap a z N).eval x) ((operatorPrefixMap a z N).eval y)).property i)
    (8*M*E) e he
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      ((f.eval x).property i) ((f.eval y).property i)
      (((operatorPrefixMap a z N).eval x).property i) (((operatorPrefixMap a z N).eval y).property i)
      _ _
      (operatorValue_close a z M K R (initialBound x) hM hK hR (initialBound_nonneg x) haB hz hlocal x
        (initialBound_valid x) N i)
      (operatorValue_close a z M K R (initialBound y) hM hK hR (initialBound_nonneg y) haB hz hlocal y
        (initialBound_valid y) N i)
  · intro N
    have hs := operatorPrefix_bound a z M K R E hM hK hR hE haB hz hlocal (Fiber.sub x y) hxy N
    exact bound_congr ((operatorPrefixMap_linear a ha z N).sub x y) hs i

end ComputableAnalysis.RiemannHilbert.LocalSystem
