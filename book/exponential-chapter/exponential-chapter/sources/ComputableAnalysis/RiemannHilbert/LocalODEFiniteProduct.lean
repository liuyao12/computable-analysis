import ComputableAnalysis.RiemannHilbert.ConvolutionEvaluation
import ComputableAnalysis.RiemannHilbert.SeriesProductTails

/-! The literal finite product discrepancy in the scalar ODE computation. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

theorem finite_ode_product (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N : Nat) :
    (sub (mul (ScalarSeries.block (seriesTerm a z) 0 N) (tailBlock a initial z 0 N))
      (derivativeBlock a initial z 0 N)).Equiv
      (ScalarSeries.missing (seriesTerm a z) (seriesTerm (coefficient a initial) z) N) := by
  have ht := seriesTerm_valid a z ha hz
  have hu := seriesTerm_valid (coefficient a initial) z (coefficient_valid a initial ha h0) hz
  have hbimage : ComplexRawQuotient.ofRaw (tailBlock a initial z 0 N) (tailBlock_valid a initial z ha h0 hz 0 N) =
      FiniteProducts.partialSum (fun i => ComplexRawQuotient.ofRaw (seriesTerm (coefficient a initial) z i) (hu i)) N := by
    simpa only [coefficientBlock] using ScalarSeries.prefix_image (seriesTerm (coefficient a initial) z) hu N
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid (ScalarSeries.block_valid _ ht 0 N) (tailBlock_valid a initial z ha h0 hz 0 N))
      (derivativeBlock_valid a initial z ha h0 hz 0 N))
    (hright := ScalarSeries.missing_valid _ _ ht hu N)
  change (ComplexRawQuotient.ofRaw (ScalarSeries.block (seriesTerm a z) 0 N) (ScalarSeries.block_valid _ ht 0 N)*
    ComplexRawQuotient.ofRaw (tailBlock a initial z 0 N) (tailBlock_valid a initial z ha h0 hz 0 N)) -
    ComplexRawQuotient.ofRaw (derivativeBlock a initial z 0 N) (derivativeBlock_valid a initial z ha h0 hz 0 N) =
    ComplexRawQuotient.ofRaw (ScalarSeries.missing (seriesTerm a z) (seriesTerm (coefficient a initial) z) N)
      (ScalarSeries.missing_valid _ _ ht hu N)
  rw [ScalarSeries.prefix_image _ ht N, hbimage, derivativeBlock_triangle a initial z ha h0 hz N,
    ScalarSeries.missing_image _ _ ht hu N]
  let f : Nat → ScalarAlgebra.Value := fun i => ComplexRawQuotient.ofRaw (seriesTerm a z i) (ht i)
  let g : Nat → ScalarAlgebra.Value := fun i => ComplexRawQuotient.ofRaw (seriesTerm (coefficient a initial) z i) (hu i)
  change FiniteProducts.partialSum f N*FiniteProducts.partialSum g N-FiniteProducts.triangle f g N =
    FiniteProducts.missing f g N
  rw [FiniteProducts.rectangular_triangle]
  generalize FiniteProducts.triangle f g N = x
  generalize FiniteProducts.missing f g N = y
  grind

theorem finite_ode_product_bound (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : ∀ i, Small (a i) (M*K^i)) (hinit : Small initial C)
    (hzR : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (mul (ScalarSeries.block (seriesTerm a z) 0 N) (tailBlock a initial z 0 N))
      (derivativeBlock a initial z 0 N)) (32*M*C*(8*K*R)^N) := by
  have ht := seriesTerm_valid a z ha hz
  have hu := seriesTerm_valid (coefficient a initial) z (coefficient_valid a initial ha h0) hz
  have hs := ScalarSeries.missing_bound _ _ ht hu M C (2*K*R) hM hC
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    (seriesTerm_bound a z ha hz M K R hM hK hR haB hzR)
    (term_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK haB hinit hzR) N
  have he : 4*(2*K*R)=8*K*R := by grind
  rw [he] at hs
  exact Small.congr (ScalarSeries.missing_valid _ _ ht hu N)
    (sub_valid (mul_valid (ScalarSeries.block_valid _ ht 0 N) (tailBlock_valid a initial z ha h0 hz 0 N))
      (derivativeBlock_valid a initial z ha h0 hz 0 N))
    (equiv_symm (finite_ode_product a initial z ha h0 hz N)) hs

end ComputableAnalysis.RiemannHilbert.LocalODE
