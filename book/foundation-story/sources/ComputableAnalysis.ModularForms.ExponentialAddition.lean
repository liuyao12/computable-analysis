import ComputableAnalysis.ModularForms.ProductLimitComparison
import ComputableAnalysis.ModularForms.ExponentialFiniteProduct
import ComputableAnalysis.ModularForms.EntireExponential

/-! Addition for actual convergent factorial series on supplied rational bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE

theorem exponential_series_addition (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid)
    (R : QPos) (hsx : Small x R.val) (hsy : Small y R.val) (hs : Small (add x y) R.val) :
    (mul
      (BoundedSeries.sumValue exponentialCoefficients x exponentialCoefficients_valid hx
        (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val)
      (BoundedSeries.sumValue exponentialCoefficients y exponentialCoefficients_valid hy
        (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val)).Equiv
    (BoundedSeries.sumValue exponentialCoefficients (add x y) exponentialCoefficients_valid
      (add_valid hx hy) (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val) := by
  let C := exponentialBudget (exponentialRatio R)
  let q := 2*exponentialRatio R*R.val
  let t := LocalODE.seriesTerm exponentialCoefficients x
  let u := LocalODE.seriesTerm exponentialCoefficients y
  have ht := LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hx
  have hu := LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid hy
  have hd := exponentialDiagonal_valid x y hx hy
  have hC : 0 ≤ C := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have hq : 0 ≤ q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have hlocal : q ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    dsimp [q]
    grind
  have htB : ∀ n, Small (t n) (2*C*q^n) :=
    LocalODE.seriesTerm_bound _ _ exponentialCoefficients_valid hx C _ _ hC hK hR
      (exponentialCoefficients_small _ (exponentialRatio_positive R)) hsx
  have huB : ∀ n, Small (u n) (2*C*q^n) :=
    LocalODE.seriesTerm_bound _ _ exponentialCoefficients_valid hy C _ _ hC hK hR
      (exponentialCoefficients_small _ (exponentialRatio_positive R)) hsy
  have hdB : ∀ n, Small (exponentialDiagonal x y n) (2*C*q^n) :=
    exponentialDiagonal_bound x y hx hy R hs
  have hvT := ScalarSeries.value_valid t ht C q hC hq hlocal htB
  have hvU := ScalarSeries.value_valid u hu C q hC hq hlocal huB
  have hvD := exponentialDiagonalSum_valid x y hx hy R hs
  have he := LocalODE.tail_bound_shrinks C q hC hq hlocal
  have he0 (N : Nat) : 0 ≤ 4*C*q^N :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) (Rat.pow_nonneg hq)
  have hprod : (mul (ScalarSeries.value t ht C q) (ScalarSeries.value u hu C q)).Equiv
      (exponentialDiagonalSum x y hx hy R) := by
    apply product_limit_comparison _ _ _ hvT hvU hvD
      (fun N => ScalarSeries.block t 0 N) (fun N => ScalarSeries.block u 0 N)
      (fun N => ScalarSeries.block (exponentialDiagonal x y) 0 N)
      (ScalarSeries.block_valid t ht 0) (ScalarSeries.block_valid u hu 0)
      (ScalarSeries.block_valid _ hd 0)
      (fun N => 4*C*q^N) (fun N => 4*C*q^N) (fun N => 4*C*q^N)
      (fun N => 32*C*C*(8*exponentialRatio R*R.val)^N)
      he he he (exponentialProductRemainder_shrinks R) he0 he0
      (4*C) (4*C) (Rat.mul_nonneg (by decide +kernel) hC)
      (Rat.mul_nonneg (by decide +kernel) hC)
      ?_ (ScalarSeries.value_bound u hu C q hC hq hlocal huB)
      (ScalarSeries.value_close t ht C q hC hq hlocal htB)
      (ScalarSeries.value_close u hu C q hC hq hlocal huB)
      (ScalarSeries.value_close _ hd C q hC hq hlocal hdB)
      (exponential_finite_product_bound x y hx hy R hsx hsy)
    intro N
    simpa only [Rat.pow_zero, Rat.mul_one] using ScalarSeries.block_bound t C q hC hq hlocal htB 0 N
  exact equiv_trans (mul_valid hvT hvU) hvD
    (BoundedSeries.sumValue_valid _ _ exponentialCoefficients_valid (add_valid hx hy)
      C _ _ hC hK hR (exponentialCoefficients_small _ (exponentialRatio_positive R)) hs hlocal)
    hprod (exponentialDiagonalSum_eq_series x y hx hy R hs)

/-- Exact addition for every pair of valid represented complex inputs;
the internal rational chart choice is hidden from callers. -/
theorem entireExponential_addition (x y : Scalar) :
    (mul (entireExponentialValue x).val (entireExponentialValue y).val).Equiv
      (entireExponentialValue ⟨add x.val y.val, add_valid x.property y.property⟩).val := by
  let A := boxCoordinateBound (x.val.compute 0)
  let B := boxCoordinateBound (y.val.compute 0)
  have hA : 0 ≤ A := boxCoordinateBound_nonneg _
  have hB : 0 ≤ B := boxCoordinateBound_nonneg _
  let R : QPos := ⟨A+B+1, by grind⟩
  have hxA : Small x.val A := small_from_box x.val x.property 0
  have hyB : Small y.val B := small_from_box y.val y.property 0
  have hxR : Small x.val R.val := hxA.mono (by dsimp [R]; grind)
  have hyR : Small y.val R.val := hyB.mono (by dsimp [R]; grind)
  have hsR : Small (add x.val y.val) R.val :=
    (small_add hxA hyB).mono (by dsimp [R]; grind)
  have hxD : (exponentialChart R).domain x := ⟨A,hA,by dsimp [R]; grind,hxA⟩
  have hyD : (exponentialChart R).domain y := ⟨B,hB,by dsimp [R]; grind,hyB⟩
  let z : Scalar := ⟨add x.val y.val, add_valid x.property y.property⟩
  have hzD : (exponentialChart R).domain z :=
    ⟨A+B,Rat.add_nonneg hA hB,by dsimp [R]; grind,small_add hxA hyB⟩
  have hxy := exponential_series_addition x.val y.val x.property y.property R hxR hyR hsR
  have hvalidX := (exponentialChart R).valid x hxD
  have hvalidY := (exponentialChart R).valid y hyD
  have hvalidZ := (exponentialChart R).valid z hzD
  exact equiv_trans
    (mul_valid (entireExponentialValue x).property (entireExponentialValue y).property)
    (mul_valid hvalidX hvalidY) (entireExponentialValue z).property
    (mul_equiv (entireExponentialValue x).property hvalidX
      (entireExponentialValue y).property hvalidY (equiv_symm (entireExponential_chart R x hxD))
      (equiv_symm (entireExponential_chart R y hyD)))
    (equiv_trans (mul_valid hvalidX hvalidY) hvalidZ (entireExponentialValue z).property
      hxy (entireExponential_chart R z hzD))

end ComputableAnalysis.ModularForms
