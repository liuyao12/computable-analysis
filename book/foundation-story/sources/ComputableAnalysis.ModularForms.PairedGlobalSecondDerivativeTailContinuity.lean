import ComputableAnalysis.ModularForms.PairedSecondDerivativeTailPrefixHolomorphic
import ComputableAnalysis.ModularForms.PairedGlobalDerivativeTailDifferentiable
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity

/-! Continuity of the actual infinite global second-derivative tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

noncomputable def pairedGlobalSecondDerivativeTail_continuous (B : Nat) :
    ContinuousOn (pairedGlobalFirstDerivativeTailMap B).domain
      (fun z hz => ⟨pairedGlobalSecondDerivativeTailValue z hz.1 B,
        pairedGlobalSecondDerivativeTailValue_valid z hz.1 B hz.2⟩) := by
  apply continuousOn_of_uniform_prefixes _
    (fun N z hz => (pairedSecondDerivativeTailPrefixMap B (N+1)).eval z hz.1)
    _ (fun N => ((65536:Nat):Rat)*((N+1:Nat):Rat)⁻¹) (pairedReciprocalTail_shrinks 65536)
  · intro N z hz
    exact pairedGlobalSecondDerivativeTailValue_close z hz.1 B hz.2 N
  · intro N
    let hc := (pairedSecondDerivativeTailPrefixMap_holomorphic B (N+1)).continuous
    exact {
      delta := fun a ha eps => hc.delta a ha.1 eps
      estimate := fun a ha eps z hz hd => hc.estimate a ha.1 eps z hz.1 hd }

end ComputableAnalysis.ModularForms
