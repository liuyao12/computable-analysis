import ComputableAnalysis.RiemannHilbert.LocalODEFiniteProduct
import ComputableAnalysis.RiemannHilbert.LocalSeriesHolomorphic

/-! The functional scalar ODE identity for the constructed local solution. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def odeError (M C K R : Rat) (N : Nat) : Rat :=
  derivativeTail C K R N + 32*M*C*(8*K*R)^N + 64*M*C*(2*K*R)^N

theorem odeError_shrinks (M C K R : Rat)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) : ShrinksToZero (odeError M C K R) := by
  have hKR : 0 ≤ K*R := Rat.mul_nonneg hK hR
  have h2 : 2*K*R ≤ (1 : Rat)/2 := by grind
  have h4 : 4*K*R ≤ (1 : Rat)/2 := by grind
  have hd := derivativeTail_shrinks C K R hC hK hR h4
  have hm : ShrinksToZero (fun N => 32*M*C*(8*K*R)^N) := by
    have hs := tail_bound_shrinks (8*M*C) (8*K*R)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    have he : (fun N : Nat => 32*M*C*(8*K*R)^N) = (fun N => 4*(8*M*C)*(8*K*R)^N) := by
      funext N; grind
    rw [he]; exact hs
  have hp : ShrinksToZero (fun N => 64*M*C*(2*K*R)^N) := by
    have hs := tail_bound_shrinks (16*M*C) (2*K*R)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) h2
    have he : (fun N : Nat => 64*M*C*(2*K*R)^N) = (fun N => 4*(16*M*C)*(2*K*R)^N) := by
      funext N; grind
    rw [he]; exact hs
  exact RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ hd hm) hp

theorem coefficient_product_close (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : ∀ i, Small (a i) (M*K^i)) (hinit : Small initial C)
    (hzR : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub
      (mul (coefficientSum a z ha hz M K R) (sumValue a initial z ha h0 hz C K R))
      (mul (ScalarSeries.block (seriesTerm a z) 0 N) (tailBlock a initial z 0 N)))
      (64*M*C*(2*K*R)^N) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have ht := seriesTerm_valid a z ha hz
  have hu := seriesTerm_valid (coefficient a initial) z (coefficient_valid a initial ha h0) hz
  have hA := coefficientSum_valid a z ha hz M K R hM hK hR haB hzR hlocal
  have hY := sumValue_valid a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR hlocal
  have hYBound : Small (sumValue a initial z ha h0 hz C K R) (4*C) := by
    rw [sumValue_as_terms a initial z ha h0 hz C K R]
    exact ScalarSeries.value_bound _ hu C (2*K*R) hC hq hlocal
      (term_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR)
  have hpBound : Small (ScalarSeries.block (seriesTerm a z) 0 N) (4*M) := by
    simpa only [Rat.pow_zero, Rat.mul_one] using
      ScalarSeries.block_bound _ M (2*K*R) hM hq hlocal
        (seriesTerm_bound a z ha hz M K R hM hK hR haB hzR) 0 N
  have hs := SeriesLimitLaws.product_close _ _ _ _ hA hY
    (ScalarSeries.block_valid _ ht 0 N) (tailBlock_valid a initial z ha h0 hz 0 N)
    (4*M*(2*K*R)^N) (4*C*(2*K*R)^N) (4*M) (4*C)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (Rat.pow_nonneg hq))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq))
    (Rat.mul_nonneg (by decide) hM) (Rat.mul_nonneg (by decide) hC)
    (coefficientSum_close a z ha hz M K R hM hK hR haB hzR hlocal N)
    (sumValue_close_prefix a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR hlocal N)
    hpBound hYBound
  have he : 2*(4*M*(2*K*R)^N)*(4*C)+2*(4*M)*(4*C*(2*K*R)^N) = 64*M*C*(2*K*R)^N := by grind
  rw [he] at hs
  exact hs

/-- The actual summed derivative equals the coefficient function times the
actual summed solution, for arbitrary valid represented inputs and data. -/
theorem sumDerivative_ode (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : ∀ i, Small (a i) (M*K^i)) (hinit : Small initial C)
    (hzR : Small z R) (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    (sumDerivative a initial z ha h0 hz C K R).Equiv
      (mul (coefficientSum a z ha hz M K R) (sumValue a initial z ha h0 hz C K R)) := by
  have hKR : 0 ≤ K*R := Rat.mul_nonneg hK hR
  have h2 : 2*K*R ≤ (1 : Rat)/2 := by grind
  have h4 : 4*K*R ≤ (1 : Rat)/2 := by grind
  have hA := coefficientSum_valid a z ha hz M K R hM hK hR haB hzR h2
  have hY := sumValue_valid a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR h2
  have hD := sumDerivative_valid a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR h4
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (odeError M C K R) (odeError_shrinks M C K R hM hC hK hR hlocal)
  intro N
  have hp := ScalarSeries.block_valid (seriesTerm a z) (seriesTerm_valid a z ha hz) 0 N
  have hq := tailBlock_valid a initial z ha h0 hz 0 N
  have hd := derivativeBlock_valid a initial z ha h0 hz 0 N
  have hleft := sumDerivative_close_prefix a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR h4 N
  have hmiddle := RepresentedCauchySum.small_sub_symm
    (mul (ScalarSeries.block (seriesTerm a z) 0 N) (tailBlock a initial z 0 N))
    (derivativeBlock a initial z 0 N) (32*M*C*(8*K*R)^N)
    (finite_ode_product_bound a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR h2 N)
  have hright := RepresentedCauchySum.small_sub_symm
    (mul (coefficientSum a z ha hz M K R) (sumValue a initial z ha h0 hz C K R))
    (mul (ScalarSeries.block (seriesTerm a z) 0 N) (tailBlock a initial z 0 N)) (64*M*C*(2*K*R)^N)
    (coefficient_product_close a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR h2 N)
  have hs := small_add (small_add hleft hmiddle) hright
  have hc := Small.congr
    (add_valid
      (add_valid (sub_valid hD hd) (sub_valid hd (mul_valid hp hq)))
      (sub_valid (mul_valid hp hq) (mul_valid hA hY)))
    (sub_valid hD (mul_valid hA hY))
    (equiv_symm (SeriesLimitLaws.difference_via _ _ _ _ hD (mul_valid hA hY) hd (mul_valid hp hq))) hs
  simpa only [odeError, Rat.zero_add] using hc

/-- The holomorphic witness satisfies the ODE at every point of its domain. -/
theorem seriesMap_ode (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : ∀ i, Small (a i) (M*K^i)) (hinit : Small initial C)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (z : Scalar) (hz : interior R z) :
    ((seriesMap_holomorphic a initial ha h0 M C K R hM hC hK hR hMK haB hinit hlocal).derivative z).Equiv
      (mul (coefficientSum a z.val ha z.property M K R)
        ((seriesMap a initial ha h0 M C K R hM hC hK hR hMK haB hinit hlocal).eval z)) :=
  sumDerivative_ode a initial z.val ha h0 z.property M C K R hM hC hK hR hMK haB hinit
    (interior_bound R z hz) hlocal

end ComputableAnalysis.RiemannHilbert.LocalODE
