import ComputableAnalysis.ModularForms.ExponentialDiagonal
import ComputableAnalysis.ModularForms.ExponentialCharts

/-! Quantitative convergence of the complete factorial diagonals. The
rectangular product comparison is a separate, still necessary step. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def exponentialDiagonal (x y : ComplexRaw) (n : Nat) : ComplexRaw :=
  ExponentialDiagonal.rawPrefix n x y (n+1)

theorem exponentialDiagonal_valid (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (n : Nat) : (exponentialDiagonal x y n).Valid :=
  ExponentialDiagonal.rawPrefix_valid n (n+1) x y hx hy

theorem exponentialDiagonal_term (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (n : Nat) : (exponentialDiagonal x y n).Equiv
      (LocalODE.seriesTerm exponentialCoefficients (add x y) n) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := exponentialDiagonal_valid x y hx hy n)
    (hright := LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid (add_valid hx hy) n)
  unfold exponentialDiagonal
  rw [ExponentialDiagonal.rawPrefix_class n (n+1) x y hx hy, ExponentialDiagonal.complete]
  change ExponentialDiagonal.coefficient n *
    (ComplexRawQuotient.ofRaw x hx + ComplexRawQuotient.ofRaw y hy)^n =
    ComplexRawQuotient.ofQComplex ⟨1/factorialRat n,0⟩ *
      ComplexRawQuotient.ofRaw (LocalODE.power (add x y) n) (LocalODE.power_valid _ (add_valid hx hy) n)
  rw [ExponentialDiagonal.power_class (add x y) (add_valid hx hy) n,
    ComplexRawQuotient.ofRaw_add x y hx hy, ExponentialDiagonal.rationalValue_raw]
  rfl

theorem exponentialDiagonal_bound (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hs : Small (add x y) R.val) (n : Nat) :
    Small (exponentialDiagonal x y n)
      (2*exponentialBudget (exponentialRatio R)*(2*exponentialRatio R*R.val)^n) := by
  have hb := LocalODE.seriesTerm_bound exponentialCoefficients (add x y)
    exponentialCoefficients_valid (add_valid hx hy)
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
    (exponentialCoefficients_small _ (exponentialRatio_positive R)) hs n
  exact Small.congr
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid (add_valid hx hy) n)
    (exponentialDiagonal_valid x y hx hy n)
    (equiv_symm (exponentialDiagonal_term x y hx hy n)) hb

/-- Every finite block of complete diagonals has a geometric tail bound,
uniform in the length of the block. -/
theorem exponentialDiagonal_tail (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hs : Small (add x y) R.val) (N count : Nat) :
    Small (ScalarSeries.block (exponentialDiagonal x y) N count)
      (4*exponentialBudget (exponentialRatio R)*(2*exponentialRatio R*R.val)^N) := by
  apply ScalarSeries.block_bound
    (exponentialDiagonal x y) (exponentialBudget (exponentialRatio R))
    (2*exponentialRatio R*R.val)
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt (exponentialRatio_positive R))) (Rat.le_of_lt R.property))
    ?_ (exponentialDiagonal_bound x y hx hy R hs) N count
  have h := exponentialRatio_local R
  have hp := exponentialRatio_positive R
  have hr := R.property
  grind

private theorem diagonalRatio_nonnegative (R : QPos) : 0 ≤ 2*exponentialRatio R*R.val :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt (exponentialRatio_positive R))) (Rat.le_of_lt R.property)

private theorem diagonalRatio_local (R : QPos) :
    2*exponentialRatio R*R.val ≤ (1 : Rat)/2 := by
  have h := exponentialRatio_local R
  have hp := exponentialRatio_positive R
  have hr := R.property
  grind

/-- The evaluator sums actual executable complete diagonals. -/
def exponentialDiagonalSum (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) : ComplexRaw :=
  ScalarSeries.value (exponentialDiagonal x y) (exponentialDiagonal_valid x y hx hy)
    (exponentialBudget (exponentialRatio R)) (2*exponentialRatio R*R.val)

theorem exponentialDiagonalSum_valid (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hs : Small (add x y) R.val) :
    (exponentialDiagonalSum x y hx hy R).Valid :=
  ScalarSeries.value_valid _ _ _ _
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (diagonalRatio_nonnegative R) (diagonalRatio_local R)
    (exponentialDiagonal_bound x y hx hy R hs)

/-- The convergent complete-diagonal sum agrees exactly with the factorial
series at the sum of the inputs. No rectangular rearrangement is assumed. -/
theorem exponentialDiagonalSum_eq_series (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hs : Small (add x y) R.val) :
    (exponentialDiagonalSum x y hx hy R).Equiv
      (BoundedSeries.sumValue exponentialCoefficients (add x y)
        exponentialCoefficients_valid (add_valid hx hy)
        (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val) := by
  apply ScalarSeries.value_congr
    (exponentialDiagonal x y) (LocalODE.seriesTerm exponentialCoefficients (add x y))
    (exponentialDiagonal_valid x y hx hy)
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid (add_valid hx hy))
    (exponentialBudget (exponentialRatio R)) (2*exponentialRatio R*R.val)
    (exponentialBudget (exponentialRatio R)) (2*exponentialRatio R*R.val)
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (diagonalRatio_nonnegative R)
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (diagonalRatio_nonnegative R) (diagonalRatio_local R) (diagonalRatio_local R)
    (exponentialDiagonal_bound x y hx hy R hs)
    (LocalODE.seriesTerm_bound _ _ exponentialCoefficients_valid (add_valid hx hy)
      _ _ _ (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
      (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
      (exponentialCoefficients_small _ (exponentialRatio_positive R)) hs)
    (exponentialDiagonal_term x y hx hy)

end ComputableAnalysis.ModularForms
