import ComputableAnalysis.ModularForms.PairedDerivativePrefixAgreement
import ComputableAnalysis.ModularForms.InverseSquareSeriesBound

/-! Height-independent bounds for the complete actual canonical derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedPartialFractionDerivative_strip_bound_at_cutoff (z : Scalar)
    (hz : InUpperHalfPlane z.val) (boxStage : Nat) (R eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute boxStage).lo.im)
    (hre : -R≤(z.val.compute boxStage).lo.re) (hhi : (z.val.compute boxStage).hi.re≤R)
    (K B : Nat) (hK : 0<K) (hlarge : 2*R≤((K+1:Nat):Rat))
    (hKB : K≤4*B) (hroom : Small z.val ((B:Rat)-1)) :
    Small (pairedPartialFractionDerivative z hz).val
      (2*(8/eta)*(8/eta)+(K:Rat)*(4*(8/eta)*(8/eta))+1024*(K:Rat)⁻¹+2048) := by
  have hM : 0≤8/eta := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr heta))
  have hc := integerReciprocalDerivativeMap_bound 0 z hz (8/eta) hM
    (integerReciprocalMap_vertical_bound z hz boxStage eta heta him 0)
  have hce := integerReciprocalDerivativeMap_eval 0 z hz
  have hcenter := Small.congr ((integerReciprocalDerivativeMap 0).eval z hz).property
    ((integerReciprocalMap_holomorphic 0).derivative z hz).property hce hc
  have hp := pairedGlobalDerivative_strip_prefix_bound z hz boxStage R eta heta him hre hhi
    K (4*B-K) hK hlarge
  rw [Nat.add_sub_of_le hKB] at hp
  have ht := pairedDerivativeTailValue_bound z hz B (pairedCutoff_room_small B z hroom)
  have hs := LocalODE.small_add hcenter (LocalODE.small_add hp ht)
  have he := pairedPartialFractionDerivative_prefix_tail B z hz hroom
  exact (Small.congr
    (add_valid ((integerReciprocalMap_holomorphic 0).derivative z hz).property
      (add_valid (ScalarSeries.block_valid _
        (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 (4*B))
        (pairedDerivativeTailValue_valid z hz B (pairedCutoff_room_small B z hroom))))
    (pairedPartialFractionDerivative z hz).property (equiv_symm he) hs).mono (by grind only)

theorem pairedPartialFractionDerivative_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (boxStage : Nat) (R eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute boxStage).lo.im)
    (hre : -R≤(z.val.compute boxStage).lo.re) (hhi : (z.val.compute boxStage).hi.re≤R)
    (K : Nat) (hK : 0<K) (hlarge : 2*R≤((K+1:Nat):Rat)) :
    Small (pairedPartialFractionDerivative z hz).val
      (2*(8/eta)*(8/eta)+(K:Rat)*(4*(8/eta)*(8/eta))+1024*(K:Rat)⁻¹+2048) := by
  let B := pairedInternalBound z+K+2
  have hroom : Small z.val ((B:Rat)-1) := by
    apply (pairedInternalBound_small z).mono
    dsimp [B]
    simp only [Rat.natCast_add]
    have hk : (0:Rat)≤(K:Rat) := Rat.natCast_nonneg
    change (pairedInternalBound z:Rat) ≤ (pairedInternalBound z:Rat)+(K:Rat)+2-1
    grind only
  exact pairedPartialFractionDerivative_strip_bound_at_cutoff z hz boxStage R eta heta
    him hre hhi K B hK hlarge (by dsimp [B]; omega) hroom

theorem pairedPartialFractionDerivative_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3) :
    Small (pairedPartialFractionDerivative z hz).val 4000 :=
  (pairedPartialFractionDerivative_strip_bound z hz N 3 1 (by decide +kernel)
    him hre hhi 6 (by decide +kernel) (by decide +kernel)).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
