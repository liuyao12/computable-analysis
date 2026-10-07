import ComputableAnalysis.ModularForms.PairedWholePlaneChartSelection

/-! Executable numeric chart values, separate from noncomputable analytic witnesses. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleDerivativeEvaluation (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) : Scalar :=
  scalarSum ((integerReciprocalOffPoleMap_holomorphic 0).derivative z hz.1)
    (scalarSum ((pairedFiniteOffPoleMap_holomorphic (4*B)).derivative z hz.2.1)
      (pairedOffPoleTailDerivativeValue B z hz.2.2))

theorem pairedOffPoleDerivativeEvaluation_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    (pairedOffPoleDerivativeEvaluation B z hz).val.Equiv
      ((pairedOffPoleAssemblyMap_holomorphic B).derivative z hz).val :=
  equiv_refl _ (pairedOffPoleDerivativeEvaluation B z hz).property

def pairedGlobalOffPoleRiccatiEvaluation (z : Scalar) (hz : pairedOffPoleDomain z) : Scalar :=
  let B := pairedOffPoleCanonicalCutoff z
  let p := pairedGlobalOffPoleAssemblyMap.eval z hz
  scalarSum (pairedOffPoleDerivativeEvaluation B z (pairedOffPoleCanonicalCutoff_mem z hz))
    (scalarProduct p p)

theorem pairedGlobalOffPoleRiccatiEvaluation_agreement (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleRiccatiEvaluation z hz).val.Equiv (pairedGlobalOffPoleRiccatiMap.eval z hz).val :=
  equiv_refl _ (pairedGlobalOffPoleRiccatiEvaluation z hz).property

def riccatiChartEvaluation (c : RiccatiChart) (z : Scalar) (hc : (riccatiChartMap c).domain z) : Scalar :=
  match c with
  | .offPole => pairedGlobalOffPoleRiccatiEvaluation z hc
  | .pole k => (pairedIntegerRiccatiExtensionMap k).eval z hc

theorem riccatiChartEvaluation_agreement (c : RiccatiChart) (z : Scalar)
    (hc : (riccatiChartMap c).domain z) :
    (riccatiChartEvaluation c z hc).val.Equiv ((riccatiChartMap c).eval z hc).val := by
  cases c with
  | offPole => exact pairedGlobalOffPoleRiccatiEvaluation_agreement z hc
  | pole k => exact equiv_refl _ ((pairedIntegerRiccatiExtensionMap k).eval z hc).property

theorem riccatiChartEvaluation_congr (c : RiccatiChart) (z w : Scalar)
    (hz : (riccatiChartMap c).domain z) (hw : (riccatiChartMap c).domain w) (he : z.val.Equiv w.val) :
    (riccatiChartEvaluation c z hz).val.Equiv (riccatiChartEvaluation c w hw).val :=
  equiv_trans (riccatiChartEvaluation c z hz).property ((riccatiChartMap c).eval z hz).property
    (riccatiChartEvaluation c w hw).property (riccatiChartEvaluation_agreement c z hz)
    (equiv_trans ((riccatiChartMap c).eval z hz).property ((riccatiChartMap c).eval w hw).property
      (riccatiChartEvaluation c w hw).property ((riccatiChartMap c).eval_congr z w hz hw he)
      (equiv_symm (riccatiChartEvaluation_agreement c w hw)))

theorem riccatiChartEvaluation_overlap (c d : RiccatiChart) (z : Scalar)
    (hc : (riccatiChartMap c).domain z) (hd : (riccatiChartMap d).domain z) :
    (riccatiChartEvaluation c z hc).val.Equiv (riccatiChartEvaluation d z hd).val :=
  equiv_trans (riccatiChartEvaluation c z hc).property ((riccatiChartMap c).eval z hc).property
    (riccatiChartEvaluation d z hd).property (riccatiChartEvaluation_agreement c z hc)
    (equiv_trans ((riccatiChartMap c).eval z hc).property ((riccatiChartMap d).eval z hd).property
      (riccatiChartEvaluation d z hd).property (riccatiChartMap_overlap_agreement c d z hc hd)
      (equiv_symm (riccatiChartEvaluation_agreement d z hd)))

end ComputableAnalysis.ModularForms
