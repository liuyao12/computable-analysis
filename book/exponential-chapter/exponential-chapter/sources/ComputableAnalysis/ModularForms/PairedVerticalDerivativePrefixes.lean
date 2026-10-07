import ComputableAnalysis.ModularForms.PairedHorizontalDerivativeDecay
import ComputableAnalysis.ModularForms.PairedVerticalSecondDerivativeBound

/-! Uniform finite head bounds from supplied imaginary separation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalDerivativeTerm_vertical_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (eta : Rat) (heta : 0<eta) (him : eta≤(z.val.compute N).lo.im) (n : Nat) :
    Small ((pairedGlobalDerivativeTermMap n).eval z hz).val (4*(8/eta)*(8/eta)) := by
  have hM : 0≤8/eta := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr heta))
  have hm := integerReciprocalDerivativeMap_bound (-((n+1:Nat):Int)) z hz (8/eta) hM
    (integerReciprocalMap_vertical_bound z hz N eta heta him _)
  have hp := integerReciprocalDerivativeMap_bound ((n+1:Nat):Int) z hz (8/eta) hM
    (integerReciprocalMap_vertical_bound z hz N eta heta him _)
  exact (LocalODE.small_add hm hp).mono (by grind only)

theorem pairedGlobalDerivative_vertical_prefix_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (eta : Rat) (heta : 0<eta) (him : eta≤(z.val.compute N).lo.im) (K : Nat) :
    Small (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) 0 K)
      ((K:Rat)*(4*(8/eta)*(8/eta))) := by
  induction K with
  | zero => exact Small.zero (by change (0:Rat)≤0*(4*(8/eta)*(8/eta)); simp only [Rat.zero_mul]; exact Rat.le_refl)
  | succ K ih =>
    have hs := LocalODE.small_add ih (pairedGlobalDerivativeTerm_vertical_bound z hz N eta heta him K)
    have he : (K:Rat)*(4*(8/eta)*(8/eta))+4*(8/eta)*(8/eta)=
        ((K+1:Nat):Rat)*(4*(8/eta)*(8/eta)) := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    simpa only [ScalarSeries.block,Nat.zero_add] using hs

end ComputableAnalysis.ModularForms
