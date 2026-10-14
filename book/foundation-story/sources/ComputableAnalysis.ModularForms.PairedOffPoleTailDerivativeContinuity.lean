import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeInvariance

/-! Continuity of the actual constructed derivative candidate on the full cutoff disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailDerivativePrefixMap (B N : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval z hz := ⟨ScalarSeries.block (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property) 0 N⟩
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => pairedOffPoleTailDerivativeTerm_congr B n z w hz hw he) 0 N

def pairedOffPoleTailDerivativePrefixMap_continuous (B N : Nat) :
    ContinuousOn (pairedOffPoleTailMap B).domain (pairedOffPoleTailDerivativePrefixMap B N).eval := by
  induction N with
  | zero =>
    let ho : ScalarTopology.OpenData (pairedOffPoleTailMap B).domain := {
      invariant := (pairedOffPoleTailMap B).domain_congr
      radius := LocalODE.interiorRadius (B:Rat)
      inside := LocalODE.interiorRadius_inside (B:Rat) }
    exact (constantOn_holomorphic ho ⟨zero,ofQComplex_valid _⟩).continuous
  | succ N ih =>
    let hc := sumContinuous (pairedOffPoleTailDerivativePrefixMap B N).eval
      (pairedOffPoleTailDerivativeTerm B N) ih (pairedOffPoleTailDerivativeTerm_continuous B N)
    refine ⟨hc.delta, ?_⟩
    intro a ha eps z hz hd
    have hb := hc.estimate a ha eps z hz hd
    simpa only [pairedOffPoleTailDerivativePrefixMap,ScalarSeries.block.eq_2,Nat.zero_add,scalarSum] using hb

noncomputable def pairedOffPoleTailDerivativeMap_continuous (B : Nat) :
    ContinuousOn (pairedOffPoleTailDerivativeMap B).domain (pairedOffPoleTailDerivativeMap B).eval := by
  apply continuousOn_of_uniform_prefixes _
    (fun N z hz => (pairedOffPoleTailDerivativePrefixMap B (N+1)).eval z hz)
    _ (fun N => (pairedOffPoleTailDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks (pairedOffPoleTailDerivativeConstant B))
  · intro N z hz
    exact pairedOffPoleTailDerivativeValue_close B z hz N
  · intro N
    exact pairedOffPoleTailDerivativePrefixMap_continuous B (N+1)

end ComputableAnalysis.ModularForms
