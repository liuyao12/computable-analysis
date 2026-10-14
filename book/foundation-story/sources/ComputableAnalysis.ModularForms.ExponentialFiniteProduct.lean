import ComputableAnalysis.ModularForms.ExponentialProductTail
import ComputableAnalysis.ModularForms.ExponentialDiagonalTail

/-! The actual factorial rectangle compared with its represented diagonal prefix. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem factorialTerm_class (x : ComplexRaw) (hx : x.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (LocalODE.seriesTerm exponentialCoefficients x n)
      (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx n) =
    ExponentialDiagonal.coefficient n * (ComplexRawQuotient.ofRaw x hx)^n := by
  change ComplexRawQuotient.ofQComplex ⟨1/factorialRat n,0⟩ *
    ComplexRawQuotient.ofRaw (LocalODE.power x n) (LocalODE.power_valid x hx n) = _
  rw [ExponentialDiagonal.rationalValue_raw, ExponentialDiagonal.power_class x hx n]
  rfl

private theorem factorialDiagonal_class (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (n : Nat) :
    FiniteProducts.diagonal
      (fun i => ComplexRawQuotient.ofRaw (LocalODE.seriesTerm exponentialCoefficients x i)
        (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx i))
      (fun i => ComplexRawQuotient.ofRaw (LocalODE.seriesTerm exponentialCoefficients y i)
        (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy i)) n =
    ComplexRawQuotient.ofRaw (exponentialDiagonal x y n) (exponentialDiagonal_valid x y hx hy n) := by
  have hp (count : Nat) :
      FiniteProducts.partialSum (fun i =>
        ComplexRawQuotient.ofRaw (LocalODE.seriesTerm exponentialCoefficients x i)
          (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx i) *
        ComplexRawQuotient.ofRaw (LocalODE.seriesTerm exponentialCoefficients y (n-i))
          (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy (n-i))) count =
      ExponentialDiagonal.diagonalPrefix n (ComplexRawQuotient.ofRaw x hx)
        (ComplexRawQuotient.ofRaw y hy) count := by
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [FiniteProducts.partialSum, ExponentialDiagonal.diagonalPrefix, ih,
        factorialTerm_class x hx count, factorialTerm_class y hy (n-count)]
      rfl
  unfold FiniteProducts.diagonal exponentialDiagonal
  rw [hp, ExponentialDiagonal.rawPrefix_class n (n+1) x y hx hy]

/-- The difference between the literal product of factorial prefixes and
the complete diagonal prefix is exactly the previously bounded remainder. -/
theorem exponential_finite_product (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (N : Nat) :
    (sub (mul (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients x) 0 N)
      (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients y) 0 N))
      (ScalarSeries.block (exponentialDiagonal x y) 0 N)).Equiv
      (exponentialProductRemainder x y N) := by
  have ht := LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx
  have hu := LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy
  have hd := exponentialDiagonal_valid x y hx hy
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid (ScalarSeries.block_valid _ ht 0 N)
      (ScalarSeries.block_valid _ hu 0 N)) (ScalarSeries.block_valid _ hd 0 N))
    (hright := exponentialProductRemainder_valid x y hx hy N)
  change (ComplexRawQuotient.ofRaw (ScalarSeries.block _ 0 N) (ScalarSeries.block_valid _ ht 0 N) *
    ComplexRawQuotient.ofRaw (ScalarSeries.block _ 0 N) (ScalarSeries.block_valid _ hu 0 N)) -
    ComplexRawQuotient.ofRaw (ScalarSeries.block _ 0 N) (ScalarSeries.block_valid _ hd 0 N) =
    ComplexRawQuotient.ofRaw (ScalarSeries.missing _ _ N) (ScalarSeries.missing_valid _ _ ht hu N)
  rw [ScalarSeries.prefix_image _ ht N, ScalarSeries.prefix_image _ hu N,
    ScalarSeries.prefix_image _ hd N, ScalarSeries.missing_image _ _ ht hu N,
    FiniteProducts.rectangular_triangle, FiniteProducts.triangle_diagonals]
  have hdEq := FiniteProducts.prefix_congr _ _ N
    (fun i _ => factorialDiagonal_class x y hx hy i)
  rw [hdEq]
  grind

theorem exponential_finite_product_bound (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hsx : Small x R.val) (hsy : Small y R.val) (N : Nat) :
    Small (sub (mul (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients x) 0 N)
      (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients y) 0 N))
      (ScalarSeries.block (exponentialDiagonal x y) 0 N))
      (32*exponentialBudget (exponentialRatio R)*exponentialBudget (exponentialRatio R)*
        (8*exponentialRatio R*R.val)^N) := by
  apply Small.congr (exponentialProductRemainder_valid x y hx hy N)
    (sub_valid (mul_valid
      (ScalarSeries.block_valid _ (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx) 0 N)
      (ScalarSeries.block_valid _ (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy) 0 N))
      (ScalarSeries.block_valid _ (exponentialDiagonal_valid x y hx hy) 0 N))
    (equiv_symm (exponential_finite_product x y hx hy N))
  exact exponentialProductRemainder_bound x y hx hy R hsx hsy N

end ComputableAnalysis.ModularForms
