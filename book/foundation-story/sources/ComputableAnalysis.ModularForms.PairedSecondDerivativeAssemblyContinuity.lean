import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTailContinuity
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeInvariance

/-! Continuity of the full constructed second-derivative assembly on regional domains. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

noncomputable def pairedGlobalSecondDerivativeAssembly_continuous (B : Nat) :
    ContinuousOn (pairedGlobalFirstDerivativeTailMap B).domain
      (fun z hz => pairedGlobalSecondDerivativeAssembly z hz.1 B hz.2) := by
  let hc := (integerReciprocalSecondDerivativeMap_holomorphic 0).continuous
  let hf := (pairedSecondDerivativeTailPrefixMap_holomorphic 0 (4*B)).continuous
  let central : ∀ z, (pairedGlobalFirstDerivativeTailMap B).domain z → Scalar :=
    fun z hz => (integerReciprocalSecondDerivativeMap 0).eval z hz.1
  let finite : ∀ z, (pairedGlobalFirstDerivativeTailMap B).domain z → Scalar :=
    fun z hz => (pairedSecondDerivativeTailPrefixMap 0 (4*B)).eval z hz.1
  let tail : ∀ z, (pairedGlobalFirstDerivativeTailMap B).domain z → Scalar :=
    fun z hz => ⟨pairedGlobalSecondDerivativeTailValue z hz.1 B,
      pairedGlobalSecondDerivativeTailValue_valid z hz.1 B hz.2⟩
  have hcentral : ContinuousOn (pairedGlobalFirstDerivativeTailMap B).domain central := {
    delta := fun a ha eps => hc.delta a ha.1 eps
    estimate := fun a ha eps z hz hd => hc.estimate a ha.1 eps z hz.1 hd }
  have hfinite : ContinuousOn (pairedGlobalFirstDerivativeTailMap B).domain finite := {
    delta := fun a ha eps => hf.delta a ha.1 eps
    estimate := fun a ha eps z hz hd => hf.estimate a ha.1 eps z hz.1 hd }
  let hsum : ContinuousOn (pairedGlobalFirstDerivativeTailMap B).domain
      (fun z hz => scalarSum (central z hz) (scalarSum (finite z hz) (tail z hz))) := sumContinuous central (fun z hz => scalarSum (finite z hz) (tail z hz))
    hcentral (sumContinuous finite tail hfinite (pairedGlobalSecondDerivativeTail_continuous B))

  let g := fun z hz => scalarSum (central z hz) (scalarSum (finite z hz) (tail z hz))
  have he (z : Scalar) (hz : (pairedGlobalFirstDerivativeTailMap B).domain z) :
      (g z hz).val.Equiv (pairedGlobalSecondDerivativeAssembly z hz.1 B hz.2).val := by
    have heval := pairedSecondDerivativeTailPrefixMap_eval 0 (4*B) z hz.1
    have ht : (fun n => (pairedGlobalSecondDerivativeTerm (4*0+n) z hz.1).val)=
        (fun n => (pairedGlobalSecondDerivativeTerm n z hz.1).val) := by
      funext n
      rw [show 4*0+n=n by omega]
    have heval' : ((pairedSecondDerivativeTailPrefixMap 0 (4*B)).eval z hz.1).val.Equiv
        (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz.1).val) 0 (4*B)) :=
      ht ▸ heval
    have hecentral : (central z hz).val.Equiv (integerReciprocalSecondDerivative 0 z hz.1).val := by
      change ((integerReciprocalSecondDerivativeMap 0).eval z hz.1).val.Equiv _
      rw [integerReciprocalSecondDerivativeMap_eval]
      exact equiv_refl _ (integerReciprocalSecondDerivative 0 z hz.1).property
    change (add (central z hz).val (add (finite z hz).val (tail z hz).val)).Equiv
      (add (integerReciprocalSecondDerivative 0 z hz.1).val
        (add (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz.1).val) 0 (4*B))
          (pairedGlobalSecondDerivativeTailValue z hz.1 B)))
    exact add_equiv hecentral
      (add_equiv heval' (equiv_refl _ (pairedGlobalSecondDerivativeTailValue_valid z hz.1 B hz.2)))
  refine ⟨hsum.delta, ?_⟩
  intro a ha eps z hz hd
  have hb : Small (sub (g z hz).val (g a ha).val) eps.val := hsum.estimate a ha eps z hz hd
  exact Small.congr (sub_valid (g z hz).property (g a ha).property)
    (sub_valid (pairedGlobalSecondDerivativeAssembly z hz.1 B hz.2).property
      (pairedGlobalSecondDerivativeAssembly a ha.1 B ha.2).property)
    (FunctionTheory.sub_congr (he z hz) (he a ha)) hb

end ComputableAnalysis.ModularForms
