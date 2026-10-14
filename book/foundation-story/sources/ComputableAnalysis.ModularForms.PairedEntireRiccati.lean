import ComputableAnalysis.ModularForms.PairedRiccatiChartEvaluation

/-! One represented entire Riccati map, assembled from the actual compatible charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedEntireRiccatiMap : DomainFunctions.Map where
  domain _ := True
  eval z _ := riccatiChartEvaluation (selectedRiccatiChart z) z (selectedRiccatiChart_mem z)
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := by
    let c := selectedRiccatiChart z
    let d := selectedRiccatiChart w
    let hcz := selectedRiccatiChart_mem z
    let hcw := ((riccatiChartMap c).domain_congr z w he).mp hcz
    let hdw := selectedRiccatiChart_mem w
    exact equiv_trans (riccatiChartEvaluation c z hcz).property
      (riccatiChartEvaluation c w hcw).property (riccatiChartEvaluation d w hdw).property
      (riccatiChartEvaluation_congr c z w hcz hcw he)
      (riccatiChartEvaluation_overlap c d w hcw hdw)

theorem pairedEntireRiccatiMap_chart_agreement (c : RiccatiChart) (z : Scalar)
    (hc : (riccatiChartMap c).domain z) :
    ((riccatiChartMap c).eval z hc).val.Equiv (pairedEntireRiccatiMap.eval z trivial).val :=
  equiv_trans ((riccatiChartMap c).eval z hc).property
    ((riccatiChartMap (selectedRiccatiChart z)).eval z (selectedRiccatiChart_mem z)).property
    (pairedEntireRiccatiMap.eval z trivial).property
    (riccatiChartMap_overlap_agreement c (selectedRiccatiChart z) z hc (selectedRiccatiChart_mem z))
    (equiv_symm (riccatiChartEvaluation_agreement (selectedRiccatiChart z) z (selectedRiccatiChart_mem z)))

noncomputable def pairedEntireRiccatiMap_holomorphic : Holomorphic pairedEntireRiccatiMap :=
  holomorphic_of_local pairedEntireRiccatiMap (fun a _ => riccatiChartMap (selectedRiccatiChart a))
    (fun a _ => riccatiChartMap_holomorphic (selectedRiccatiChart a))
    (fun a _ => selectedRiccatiChart_mem a) (fun _ _ _ _ => trivial)
    (fun a _ z hz => pairedEntireRiccatiMap_chart_agreement (selectedRiccatiChart a) z hz)

theorem pairedEntireRiccatiMap_chart_derivative_agreement (c : RiccatiChart) (z : Scalar)
    (hc : (riccatiChartMap c).domain z) :
    ((riccatiChartMap_holomorphic c).derivative z hc).val.Equiv
      (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val :=
  (riccatiChartMap_holomorphic c).derivative_equiv_on_overlap pairedEntireRiccatiMap_holomorphic
    (fun z hc _ => pairedEntireRiccatiMap_chart_agreement c z hc) z hc trivial

end ComputableAnalysis.ModularForms
