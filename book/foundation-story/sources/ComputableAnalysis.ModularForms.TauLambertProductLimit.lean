import ComputableAnalysis.ModularForms.TauFiniteLambertDifferential

/-! Quantitative product limits for the Euler-Lambert differential identity. -/
set_option maxHeartbeats 800000
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauLambertValue (q : Scalar) (hq : tauEulerNomeDomain q) : Scalar :=
  ⟨weightedLambertSum q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq),
    weightedLambertSum_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) (by decide +kernel)⟩

def tauLambertTail (N : Nat) : Rat := 4*(8*(1/1024:Rat))*(weightedLambertRatio (1/1024) 1)^N

def tauLambertProductError (N : Nat) : Rat :=
  2*tauEulerProductTail (1/1024) N*(4*(8*(1/1024:Rat)))+4*tauLambertTail N

theorem tauLambertProductError_shrinks : ShrinksToZero tauLambertProductError := by
  have hp := SeriesLimitLaws.shrinks_scale _
    (tauEulerProductTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl)
    (2*(4*(8*(1/1024:Rat)))) (by decide +kernel)
  have hl := SeriesLimitLaws.shrinks_scale _
    (weightedLambertSum_tail_shrinks (1/1024) 1 (by decide +kernel) (by decide +kernel)) 4 (by decide +kernel)
  have hs := RepresentedCauchySum.sum_shrinks _ _ hp hl
  have he : tauLambertProductError=(fun N =>
      (2*(4*(8*(1/1024:Rat))))*tauEulerProductTail (1/1024) N+
      4*(4*(8*(1/1024:Rat))*(weightedLambertRatio (1/1024) 1)^N)) := by
    funext N
    dsimp [tauLambertProductError,tauLambertTail]
    grind only
  rw [he]
  exact hs

/-- The actual Euler-Lambert product is approximated by the finite products
and the existing weighted Lambert prefixes with an explicit shrinking error. -/
theorem tauEulerLambertProduct_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (mul (tauEulerNomeMap.eval q hq).val (tauLambertValue q hq).val)
      (mul (finiteDiscriminantEulerProduct q N).val
        (ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N))) (tauLambertProductError N) := by
  have hqB := LocalODE.interior_bound (1/1024) q hq
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel) hqB
  have hE : 0≤tauEulerProductTail (1/1024) N := by
    unfold tauEulerProductTail
    exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
  have hU : 0≤tauLambertTail N := by
    unfold tauLambertTail
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (weightedLambertRatio_nonneg (1/1024) 1 (by decide +kernel)))
  have h := SeriesLimitLaws.product_close _ _ _ _ (tauEulerNomeMap.eval q hq).property
    (tauLambertValue q hq).property (finiteDiscriminantEulerProduct q N).property
    (ScalarSeries.block_valid _ ht 0 N) _ _ 2 (4*(8*(1/1024:Rat)))
    hE hU (by decide +kernel) (by decide +kernel)
    (tauEulerProduct_close_prefix q (1/1024) (by decide +kernel) Rat.le_refl hqB N)
    (weightedLambertSum_close q (1/1024) 1 (by decide +kernel) (by decide +kernel) hqB (by decide +kernel) N)
    (finiteDiscriminantEulerProduct_bound q (1/1024) (by decide +kernel) Rat.le_refl hqB N)
    (weightedLambertSum_bound q (1/1024) 1 (by decide +kernel) (by decide +kernel) hqB (by decide +kernel))

  apply h.mono
  unfold tauLambertProductError
  grind only

end ComputableAnalysis.ModularForms
