import ComputableAnalysis.ModularForms.WideEulerProductValue
import ComputableAnalysis.ModularForms.RepresentedPrefixFactors
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Equivalent inputs give equivalent literal finite tails. -/
theorem wideEulerTailPrefix_congr (q w : Scalar) (he : q.val.Equiv w.val) (N : Nat) :
    (wideEulerTailPrefix q N).val.Equiv (wideEulerTailPrefix w N).val := by
  induction N with
  | zero => exact equiv_refl _ oneScalar.property
  | succ N ih =>
    have hp := LocalODE.power_congr _ _ q.property w.property he (N+3)
    have hs := FunctionTheory.sub_congr (equiv_refl one (ofQComplex_valid _)) hp
    exact mul_equiv (wideEulerTailPrefix q N).property (wideEulerTailPrefix w N).property
      (tauEulerFactorValue q (N+2)).property (tauEulerFactorValue w (N+2)).property ih
      (LocalODE.power_congr _ _ (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _))
        (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ w.property _)) hs 24)

/-- The executable wider tail value is representation invariant. -/
theorem wideEulerTailValue_congr (q w : Scalar) (hq : Small q.val ((1:Rat)/64))
    (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideEulerTailValue q hq).val.Equiv (wideEulerTailValue w hw).val := by
  apply RepresentedCauchySum.value_congr _ _ _ _ _ _ wideEulerTailError_shrinks wideEulerTailError_shrinks
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)))
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)))
    (wideEulerTailPrefix_cauchy q hq) (wideEulerTailPrefix_cauchy w hw)
  exact wideEulerTailPrefix_congr q w he

theorem wideEulerProductValue_congr (q w : Scalar) (hq : Small q.val ((1:Rat)/64))
    (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideEulerProductValue q hq).val.Equiv (wideEulerProductValue w hw).val :=
  mul_equiv (finiteDiscriminantEulerProduct q 2).property (finiteDiscriminantEulerProduct w 2).property
    (wideEulerTailValue q hq).property (wideEulerTailValue w hw).property
    (finiteDiscriminantEulerProduct_congr q w he 2) (wideEulerTailValue_congr q w hq hw he)

/-- The full wider product is a limit of the actual full finite Euler products. -/
theorem wideEulerProductValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerProductValue q hq).val (finiteDiscriminantEulerProduct q (N+2)).val)
      (2*scalarBound (finiteDiscriminantEulerProduct q 2)*wideEulerTailError N) := by
  let c := finiteDiscriminantEulerProduct q 2
  let f := wideEulerTailValue q hq
  let p := wideEulerTailPrefix q N
  have h := representedFactor_difference_small c.val f.val p.val c.property f.property p.property
    (scalarBound c) (wideEulerTailError N) (Rat.le_of_lt (scalarBound_pos c))
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)))
    (scalar_small c) (wideEulerTailValue_close_prefix q hq N)
  exact Small.congr (sub_valid (mul_valid c.property f.property) (mul_valid c.property p.property))
    (sub_valid (wideEulerProductValue q hq).property (finiteDiscriminantEulerProduct q (N+2)).property)
    (FunctionTheory.sub_congr (equiv_refl _ (wideEulerProductValue q hq).property)
      (equiv_symm (finiteDiscriminantEulerProduct_wide_tail q N))) h

/-- The wider algorithm agrees exactly with every justified original Euler schedule. -/
theorem wideEulerProductValue_original_agreement (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (hw : Small q.val ((1:Rat)/64)) :
    (wideEulerProductValue q hw).val.Equiv (tauEulerProduct q r hr hrMax hq).val := by
  let f := tauEulerProduct q r hr hrMax hq
  let g := wideEulerTailValue q hw
  let c := finiteDiscriminantEulerProduct q 2
  let p := fun N => finiteDiscriminantEulerProduct q (N+2)
  let t := fun N => wideEulerTailPrefix q N
  have he := SeriesLimitLaws.shrinks_shift _ (tauEulerProductTail_shrinks r hr hrMax) 2
  have hfg := representedFactor_limit_comparison f g c p t
    (fun N => tauEulerProductTail r (N+2)) wideEulerTailError he wideEulerTailError_shrinks
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)))
    (fun N => tauEulerProduct_close_prefix q r hr hrMax hq (N+2))
    (wideEulerTailValue_close_prefix q hw) (finiteDiscriminantEulerProduct_wide_tail q)
  exact equiv_symm hfg

end ComputableAnalysis.ModularForms
