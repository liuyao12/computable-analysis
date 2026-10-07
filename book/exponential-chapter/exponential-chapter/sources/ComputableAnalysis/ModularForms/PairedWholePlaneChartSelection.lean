import ComputableAnalysis.ModularForms.PairedWholePlaneChartSearch

/-! Executable chart-index extraction and proved compatibility of all actual Riccati charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

inductive RiccatiChart where
  | offPole
  | pole (k : Int)
  deriving DecidableEq

noncomputable def riccatiChartMap : RiccatiChart → DomainFunctions.Map
  | .offPole => pairedGlobalOffPoleRiccatiMap
  | .pole k => pairedIntegerRiccatiExtensionMap k

noncomputable def riccatiChartMap_holomorphic (c : RiccatiChart) : Holomorphic (riccatiChartMap c) := by
  cases c with
  | offPole => exact pairedGlobalOffPoleRiccatiMap_holomorphic
  | pole k => exact pairedIntegerRiccatiExtensionMap_holomorphic k

def recognizedPoleIndex (z : Scalar) (N : Nat) : Nat :=
  ((List.range (N+1)).find? (fun n => LocalODE.boxInside (1/4)
    (integerShiftScalar z (-(poleChartInteger n))) N)).getD 0

theorem recognizedPoleIndex_good (z : Scalar) (N : Nat) (h : poleChartRecognized z N=true) :
    LocalODE.boxInside (1/4) (integerShiftScalar z (-(poleChartInteger (recognizedPoleIndex z N)))) N=true := by
  obtain ⟨n,hn,hg⟩ := List.any_eq_true.mp h
  cases hf : (List.range (N+1)).find? (fun n => LocalODE.boxInside (1/4)
      (integerShiftScalar z (-(poleChartInteger n))) N) with
  | none => exact False.elim ((List.find?_eq_none.mp hf n hn) hg)
  | some i =>
    have hi := List.find?_some hf
    simpa only [recognizedPoleIndex,hf,Option.getD_some] using hi

def selectedRiccatiChart (z : Scalar) : RiccatiChart :=
  let N := riccatiChartSearchStage z
  if offPoleChartRecognized z N then .offPole else .pole (poleChartInteger (recognizedPoleIndex z N))

theorem selectedRiccatiChart_mem (z : Scalar) : (riccatiChartMap (selectedRiccatiChart z)).domain z := by
  unfold selectedRiccatiChart
  dsimp only
  split
  · exact offPoleChartRecognized_sound z _ ‹_›
  · have hp : poleChartRecognized z (riccatiChartSearchStage z)=true :=
      (riccatiChartSearchStage_success z).resolve_left ‹_›
    have hg := recognizedPoleIndex_good z _ hp
    let w := integerShiftScalar z (-(poleChartInteger (recognizedPoleIndex z (riccatiChartSearchStage z))))
    have hb : LocalODE.boxCoordinateBound (w.val.compute (riccatiChartSearchStage z))<(1:Rat)/4 := by
      simpa only [LocalODE.boxInside,decide_eq_true_eq] using hg
    refine ⟨trivial,?_⟩
    exact ⟨LocalODE.boxCoordinateBound (w.val.compute (riccatiChartSearchStage z)),
      LocalODE.boxCoordinateBound_nonneg _,hb,LocalODE.small_from_box w.val w.property _⟩

theorem riccatiChartMap_overlap_agreement (c d : RiccatiChart) (z : Scalar)
    (hc : (riccatiChartMap c).domain z) (hd : (riccatiChartMap d).domain z) :
    ((riccatiChartMap c).eval z hc).val.Equiv ((riccatiChartMap d).eval z hd).val := by
  cases c with
  | offPole =>
    cases d with
    | offPole => exact equiv_refl _ ((riccatiChartMap .offPole).eval z hc).property
    | pole k => exact pairedGlobalOffPoleRiccatiMap_integer_extension_agreement k z hc hd
  | pole j =>
    cases d with
    | offPole => exact equiv_symm (pairedGlobalOffPoleRiccatiMap_integer_extension_agreement j z hd hc)
    | pole k => exact pairedIntegerRiccatiExtensionMap_overlap_agreement j k z hc hd

end ComputableAnalysis.ModularForms
