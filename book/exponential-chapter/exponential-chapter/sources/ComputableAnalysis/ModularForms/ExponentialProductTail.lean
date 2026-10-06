import ComputableAnalysis.ModularForms.ExponentialCharts
import ComputableAnalysis.RiemannHilbert.SeriesProductTails

/-! Shrinking bounds for the literal omitted rows of factorial prefix products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def exponentialProductRemainder (x y : ComplexRaw) (N : Nat) : ComplexRaw :=
  ScalarSeries.missing (LocalODE.seriesTerm exponentialCoefficients x)
    (LocalODE.seriesTerm exponentialCoefficients y) N

theorem exponentialProductRemainder_valid (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (N : Nat) : (exponentialProductRemainder x y N).Valid :=
  ScalarSeries.missing_valid _ _
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx)
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy) N

theorem exponentialProductRemainder_bound (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hsx : Small x R.val) (hsy : Small y R.val) (N : Nat) :
    Small (exponentialProductRemainder x y N)
      (32*exponentialBudget (exponentialRatio R)*exponentialBudget (exponentialRatio R)*
        (8*exponentialRatio R*R.val)^N) := by
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have hq : 0 ≤ 2*exponentialRatio R*R.val :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have hlocal : 2*exponentialRatio R*R.val ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    grind
  have h := ScalarSeries.missing_bound
    (LocalODE.seriesTerm exponentialCoefficients x) (LocalODE.seriesTerm exponentialCoefficients y)
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx)
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy)
    (exponentialBudget (exponentialRatio R)) (exponentialBudget (exponentialRatio R))
    (2*exponentialRatio R*R.val) hC hC hq hlocal
    (LocalODE.seriesTerm_bound _ _ exponentialCoefficients_valid hx _ _ _ hC hK hR
      (exponentialCoefficients_small _ (exponentialRatio_positive R)) hsx)
    (LocalODE.seriesTerm_bound _ _ exponentialCoefficients_valid hy _ _ _ hC hK hR
      (exponentialCoefficients_small _ (exponentialRatio_positive R)) hsy) N
  have he : 4*(2*exponentialRatio R*R.val)=8*exponentialRatio R*R.val := by grind
  rw [he] at h
  exact h

theorem exponentialProductRemainder_shrinks (R : QPos) :
    ShrinksToZero (fun (N : Nat) =>
      32*exponentialBudget (exponentialRatio R)*exponentialBudget (exponentialRatio R)*
        (8*exponentialRatio R*R.val)^N) := by
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hq : 0 ≤ 8*exponentialRatio R*R.val :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt (exponentialRatio_positive R))) (Rat.le_of_lt R.property)
  have h := LocalODE.tail_bound_shrinks
    (8*exponentialBudget (exponentialRatio R)*exponentialBudget (exponentialRatio R))
    (8*exponentialRatio R*R.val)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) hC)
    hq (exponentialRatio_local R)
  have he : (fun (N : Nat) => 4*(8*exponentialBudget (exponentialRatio R)*
      exponentialBudget (exponentialRatio R))*(8*exponentialRatio R*R.val)^N) =
      (fun (N : Nat) => 32*exponentialBudget (exponentialRatio R)*
        exponentialBudget (exponentialRatio R)*(8*exponentialRatio R*R.val)^N) := by
    funext N
    grind
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
