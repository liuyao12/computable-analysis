import ComputableAnalysis.ModularForms.RepresentedVerticalReciprocalBound
import ComputableAnalysis.ModularForms.PairedSecondDerivativeRegionalBound

/-! Actual derivative estimates with finite reciprocal bounds discharged by height evidence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalMap_vertical_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute N).lo.im) (k : Int) :
    Small ((integerReciprocalMap k).eval z hz).val (8/eta) :=
  globalIntegerReciprocal_vertical_bound z (pairedGlobalOffPole_upper_mem z hz) N eta heta him k

theorem pairedCanonicalSecondDerivative_vertical_regional_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hroom : Small z.val ((B:Rat)-2))
    (N : Nat) (eta : Rat) (heta : 0<eta) (him : eta≤(z.val.compute N).lo.im) :
    Small (pairedCanonicalSecondDerivative z hz).val
      (8*(8/eta)*(8/eta)*(8/eta)+((4*B:Nat):Rat)*(16*(8/eta)*(8/eta)*(8/eta))+131072) := by
  have hM : 0≤8/eta := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr heta))
  exact pairedCanonicalSecondDerivative_regional_bound z hz B hroom (8/eta) hM
    (integerReciprocalMap_vertical_bound z hz N eta heta him 0)
    (fun n _ => integerReciprocalMap_vertical_bound z hz N eta heta him (-((n+1:Nat):Int)))
    (fun n _ => integerReciprocalMap_vertical_bound z hz N eta heta him ((n+1:Nat):Int))

end ComputableAnalysis.ModularForms
