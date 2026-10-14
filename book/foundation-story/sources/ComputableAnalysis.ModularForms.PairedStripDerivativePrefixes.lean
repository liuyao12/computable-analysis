import ComputableAnalysis.ModularForms.PairedVerticalDerivativePrefixes
import ComputableAnalysis.ModularForms.PairedHorizontalDerivativeBlocks

/-! Uniform bounds for long derivative prefixes in a vertical strip. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem scalarSeries_prefix_append_equiv (t : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (K L : Nat) :
    (add (ScalarSeries.block t 0 K) (ScalarSeries.block t K L)).Equiv
      (ScalarSeries.block t 0 (K+L)) := by
  have hd := ScalarSeries.prefix_difference t ht K L
  exact equiv_trans
    (add_valid (ScalarSeries.block_valid t ht 0 K) (ScalarSeries.block_valid t ht K L))
    (add_valid (ScalarSeries.block_valid t ht 0 K)
      (sub_valid (ScalarSeries.block_valid t ht 0 (K+L)) (ScalarSeries.block_valid t ht 0 K)))
    (ScalarSeries.block_valid t ht 0 (K+L))
    (add_equiv (equiv_refl _ (ScalarSeries.block_valid t ht 0 K)) (equiv_symm hd))
    (SeriesLimitLaws.add_difference _ _ (ScalarSeries.block_valid t ht 0 (K+L))
      (ScalarSeries.block_valid t ht 0 K))

theorem pairedGlobalDerivative_strip_prefix_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (boxStage : Nat) (R eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute boxStage).lo.im)
    (hre : -R≤(z.val.compute boxStage).lo.re) (hhi : (z.val.compute boxStage).hi.re≤R)
    (K L : Nat) (hK : 0<K) (hlarge : 2*R≤((K+1:Nat):Rat)) :
    Small (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) 0 (K+L))
      ((K:Rat)*(4*(8/eta)*(8/eta))+1024*(K:Rat)⁻¹) := by
  have hh := pairedGlobalDerivative_vertical_prefix_bound z hz boxStage eta heta him K
  have ht := pairedGlobalDerivative_horizontal_block_tail z hz boxStage R hre hhi K L hK hlarge
  exact Small.congr
    (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 K)
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) K L))
    (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 (K+L))
    (scalarSeries_prefix_append_equiv _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) K L)
    (LocalODE.small_add hh ht)

end ComputableAnalysis.ModularForms
