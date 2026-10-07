import ComputableAnalysis.ModularForms.PairedOffPoleTailSecondDerivativeSeries

/-! Representation invariance and continuity of the actual off-pole second-derivative sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleTailSecondDerivativeTerm_congr (B n : Nat) (z w : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (hw : LocalODE.interior (B:Rat) w)
    (he : z.val.Equiv w.val) :
    (pairedOffPoleTailSecondDerivativeTerm B n z hz).val.Equiv
      (pairedOffPoleTailSecondDerivativeTerm B n w hw).val :=
  equiv_trans (pairedOffPoleTailSecondDerivativeTerm B n z hz).property
    ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative z hz).property
    (pairedOffPoleTailSecondDerivativeTerm B n w hw).property
    (equiv_symm (pairedOffPoleTailDerivativeTermMap_derivative B n z hz))
    (equiv_trans ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative z hz).property
      ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative w hw).property
      (pairedOffPoleTailSecondDerivativeTerm B n w hw).property
      ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative_congr z w hz hw he)
      (pairedOffPoleTailDerivativeTermMap_derivative B n w hw))

theorem pairedOffPoleTailSecondDerivativeValue_congr (B : Nat) (z w : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (hw : LocalODE.interior (B:Rat) w)
    (he : z.val.Equiv w.val) :
    (pairedOffPoleTailSecondDerivativeValue B z hz).val.Equiv
      (pairedOffPoleTailSecondDerivativeValue B w hw).val :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).property)
    (fun n => (pairedOffPoleTailSecondDerivativeTerm B n w hw).property)
    (pairedOffPoleTailSecondDerivativeConstant B)
    (fun n => pairedOffPoleTailSecondDerivativeTerm_bound B n z hz)
    (fun n => pairedOffPoleTailSecondDerivativeTerm_bound B n w hw)
    (fun n => pairedOffPoleTailSecondDerivativeTerm_congr B n z w hz hw he)

def pairedOffPoleTailSecondDerivativeMap (B : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval := pairedOffPoleTailSecondDerivativeValue B
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := pairedOffPoleTailSecondDerivativeValue_congr B z w hz hw he

def pairedOffPoleTailSecondDerivativeTerm_continuous (B n : Nat) :
    ContinuousOn (pairedOffPoleTailMap B).domain (pairedOffPoleTailSecondDerivativeTerm B n) where
  delta := (pairedOffPoleTailDerivativeTermMap_holomorphic B n).continuousDerivative.delta
  estimate a ha eps z hz hd := by
    have hb := (pairedOffPoleTailDerivativeTermMap_holomorphic B n).continuousDerivative.estimate a ha eps z hz hd
    exact Small.congr
      (sub_valid ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative z hz).property
        ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative a ha).property)
      (sub_valid (pairedOffPoleTailSecondDerivativeTerm B n z hz).property
        (pairedOffPoleTailSecondDerivativeTerm B n a ha).property)
      (FunctionTheory.sub_congr (pairedOffPoleTailDerivativeTermMap_derivative B n z hz)
        (pairedOffPoleTailDerivativeTermMap_derivative B n a ha)) hb

def pairedOffPoleTailSecondDerivativePrefixMap (B N : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval z hz := ⟨ScalarSeries.block (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).property) 0 N⟩
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => pairedOffPoleTailSecondDerivativeTerm_congr B n z w hz hw he) 0 N

def pairedOffPoleTailSecondDerivativePrefixMap_continuous (B N : Nat) :
    ContinuousOn (pairedOffPoleTailMap B).domain (pairedOffPoleTailSecondDerivativePrefixMap B N).eval := by
  induction N with
  | zero =>
    let ho : ScalarTopology.OpenData (pairedOffPoleTailMap B).domain := {
      invariant := (pairedOffPoleTailMap B).domain_congr
      radius := LocalODE.interiorRadius (B:Rat)
      inside := LocalODE.interiorRadius_inside (B:Rat) }
    exact (constantOn_holomorphic ho ⟨zero,ofQComplex_valid _⟩).continuous
  | succ N ih =>
    let hc := sumContinuous (pairedOffPoleTailSecondDerivativePrefixMap B N).eval
      (pairedOffPoleTailSecondDerivativeTerm B N) ih (pairedOffPoleTailSecondDerivativeTerm_continuous B N)
    refine ⟨hc.delta, ?_⟩
    intro a ha eps z hz hd
    have hb := hc.estimate a ha eps z hz hd
    simpa only [pairedOffPoleTailSecondDerivativePrefixMap,ScalarSeries.block.eq_2,Nat.zero_add,scalarSum] using hb

noncomputable def pairedOffPoleTailSecondDerivativeMap_continuous (B : Nat) :
    ContinuousOn (pairedOffPoleTailSecondDerivativeMap B).domain (pairedOffPoleTailSecondDerivativeMap B).eval := by
  apply continuousOn_of_uniform_prefixes _
    (fun N z hz => (pairedOffPoleTailSecondDerivativePrefixMap B (N+1)).eval z hz)
    _ (fun N => (pairedOffPoleTailSecondDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks (pairedOffPoleTailSecondDerivativeConstant B))
  · intro N z hz
    exact pairedOffPoleTailSecondDerivativeValue_close B z hz N
  · intro N
    exact pairedOffPoleTailSecondDerivativePrefixMap_continuous B (N+1)

end ComputableAnalysis.ModularForms
