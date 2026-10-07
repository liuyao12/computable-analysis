import ComputableAnalysis.ModularForms.PairedGlobalStripDerivativeBound

/-! Exact coordinate strip hypotheses hide the internal box stage. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem exactUpperStrip_has_bounded_box (z : Scalar)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    ∃ N, -3≤(z.val.compute N).lo.re ∧ (z.val.compute N).hi.re≤3 ∧
      1≤(z.val.compute N).lo.im := by
  obtain ⟨N,hN⟩ := z.property.2.2 ⟨1,by decide +kernel⟩
  have hw := (hN N (Nat.le_refl N)).1
  have hh := (hN N (Nat.le_refl N)).2
  have hlo := hre 0 N
  have hupper := hhi N 0
  have hlower := him 0 N
  change 0≤(z.val.compute N).hi.re at hlo
  change (z.val.compute N).lo.re≤2 at hupper
  change 2≤(z.val.compute N).hi.im at hlower
  change (z.val.compute N).hi.re-(z.val.compute N).lo.re≤1 at hw
  change (z.val.compute N).hi.im-(z.val.compute N).lo.im≤1 at hh
  exact ⟨N,by grind only,by grind only,by grind only⟩

theorem pairedPartialFractionDerivative_exact_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedPartialFractionDerivative z hz).val 4000 := by
  obtain ⟨N,hlo,hup,hheight⟩ := exactUpperStrip_has_bounded_box z hre hhi him
  exact pairedPartialFractionDerivative_upper_strip_bound z hz N hheight hlo hup

theorem pairedGlobalOffPoleAssemblyMap_derivative_exact_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val 4000 := by
  obtain ⟨N,hlo,hup,hheight⟩ := exactUpperStrip_has_bounded_box z hre hhi him
  exact pairedGlobalOffPoleAssemblyMap_derivative_upper_strip_bound z hz N hheight hlo hup

end ComputableAnalysis.ModularForms
