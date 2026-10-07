import ComputableAnalysis.ModularForms.PairedVerticalSecondDerivativeBound
import ComputableAnalysis.ModularForms.PairedTailUniformBound

/-! Bounds for the actual finite value head from imaginary separation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedReciprocalTermMap_vertical_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (eta : Rat) (heta : 0<eta) (him : eta≤(z.val.compute N).lo.im) (n : Nat) :
    Small ((pairedReciprocalTermMap n).eval z hz).val (16/eta) :=
  (LocalODE.small_add (integerReciprocalMap_vertical_bound z hz N eta heta him (-((n+1:Nat):Int)))
    (integerReciprocalMap_vertical_bound z hz N eta heta him ((n+1:Nat):Int))).mono
      (by grind [Rat.div_def])

theorem pairedFiniteMap_vertical_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (eta : Rat) (heta : 0<eta) (him : eta≤(z.val.compute N).lo.im) (K : Nat) :
    Small ((pairedFiniteMap K).eval z hz).val ((K:Rat)*(16/eta)) := by
  induction K with
  | zero => exact Small.zero (by change (0:Rat)≤0*(16/eta); simp [Rat.zero_mul])
  | succ K ih =>
    have hs := LocalODE.small_add ih (pairedReciprocalTermMap_vertical_bound z hz N eta heta him K)
    have he : (K:Rat)*(16/eta)+16/eta=((K+1:Nat):Rat)*(16/eta) := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    simpa only [pairedFiniteMap,ScalarSeries.block,Nat.zero_add] using hs

theorem pairedPartialFractionMap_vertical_bound_at_cutoff (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) (eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute N).lo.im) (B : Nat) (hB : Small z.val (B:Rat))
    (hpos : 0<B) :
    Small (pairedPartialFractionMap.eval z hz).val (8/eta+((4*B:Nat):Rat)*(16/eta)+4) := by
  have hs := LocalODE.small_add
    (integerReciprocalMap_vertical_bound z hz N eta heta him 0)
    (LocalODE.small_add (pairedFiniteMap_vertical_bound z hz N eta heta him (4*B))
      (pairedTailValue_uniform_bound z B hB hpos))
  exact (Small.congr ((pairedWholeJoinedMap B).eval z ⟨hz,hB⟩).property
    (pairedPartialFractionMap.eval z hz).property
    (pairedWholeJoinedMap_eval B z ⟨hz,hB⟩) hs).mono (by grind only)

end ComputableAnalysis.ModularForms
