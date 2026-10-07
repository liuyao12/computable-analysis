import ComputableAnalysis.ModularForms.RealExponentialPositiveGapOrder
import ComputableAnalysis.ModularForms.RealExponentialFiftyTwoUpperBound
import ComputableAnalysis.ModularForms.CMGrowthSharperUpperBounds163
import ComputableAnalysis.ModularForms.CMNomeQuadraticDecay163

/-! A justified analytic upper bound for the actual CM growth exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def cmGrowthGapToFiftyTwo163 : RealRaw := RealRaw.add (RealRaw.ofRat 52) (RealRaw.neg cmGrowthReal163)

theorem cmGrowthGapToFiftyTwo163_valid : cmGrowthGapToFiftyTwo163.Valid :=
  RealRaw.add_valid (RealRaw.ofRat_valid 52) (RealRaw.neg_valid cmGrowthReal163_valid)

theorem cmGrowthGapToFiftyTwo163_lower_three : (RealRaw.ofRat 3).Le cmGrowthGapToFiftyTwo163 := by
  intro n m
  have h := cmGrowthReal163_upper_fortyNine m 0
  change (cmGrowthReal163.compute m).lo≤(49:Rat) at h
  change (3:Rat)≤52+ -(cmGrowthReal163.compute m).lo
  grind only

theorem cmGrowthGapToFiftyTwo163_positive : cmGrowthGapToFiftyTwo163.Pos := by
  obtain ⟨N,hN⟩ := cmGrowthGapToFiftyTwo163_valid.2.2 (⟨1,by decide +kernel⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hl := cmGrowthGapToFiftyTwo163_lower_three 0 N
  change (3:Rat)≤(cmGrowthGapToFiftyTwo163.compute N).hi at hl
  unfold QInterval.width at hw
  refine ⟨N,?_⟩
  change 0<(cmGrowthGapToFiftyTwo163.compute N).lo
  grind only

private theorem real_gap_sum :
    (add (ofRealRaw cmGrowthReal163) (ofRealRaw cmGrowthGapToFiftyTwo163)).Equiv (ofQComplex ⟨52,0⟩) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ cmGrowthReal163_valid n
  simp only [add,ofRealRaw,cmGrowthGapToFiftyTwo163,RealRaw.add,RealRaw.addCompute,
    RealRaw.neg,RealRaw.negCompute,RealRaw.ofRat,QBox.add,QComplex.add,ofQComplex,QBox.point,
    QBox.Overlaps,QComplex.le_def,Rat.add_zero]
  change ((cmGrowthReal163.compute n).lo+(52+ -(cmGrowthReal163.compute n).hi)≤52 ∧ (0:Rat)≤0) ∧
    (52≤(cmGrowthReal163.compute n).hi+(52+ -(cmGrowthReal163.compute n).lo) ∧ (0:Rat)≤0)
  constructor <;> constructor <;> grind only

/-- The actual CM growth exponential is bounded above by the justified rational power. -/
theorem cmGrowthExponential163_upper_power :
    cmGrowthValue163.Le (RealRaw.ofRat ((8:Rat)^26)) := by
  let X : Scalar := ⟨ofRealRaw cmGrowthReal163,ofRealRaw_valid _ cmGrowthReal163_valid⟩
  let D : Scalar := ⟨ofRealRaw cmGrowthGapToFiftyTwo163,ofRealRaw_valid _ cmGrowthGapToFiftyTwo163_valid⟩
  have hx0 : (RealRaw.ofRat 0).Le cmGrowthReal163 := by
    intro n m
    have h := cmGrowthReal163_lower_twentyFour 0 m
    change (24:Rat)≤(cmGrowthReal163.compute m).hi at h
    change (0:Rat)≤(cmGrowthReal163.compute m).hi
    grind only
  have hd0 : (RealRaw.ofRat 0).Le cmGrowthGapToFiftyTwo163 := by
    intro n m
    have h := cmGrowthGapToFiftyTwo163_lower_three 0 m
    change (3:Rat)≤(cmGrowthGapToFiftyTwo163.compute m).hi at h
    change (0:Rat)≤(cmGrowthGapToFiftyTwo163.compute m).hi
    grind only
  have hm := entireExponential_real_positive_gap_order cmGrowthReal163 cmGrowthGapToFiftyTwo163
    cmGrowthReal163_valid cmGrowthGapToFiftyTwo163_valid cmGrowthReal163_positive
    cmGrowthGapToFiftyTwo163_positive hx0 hd0
  have hc := ComplexRaw.realPart_equiv (entireExponentialValue_congr cmGrowthExponent163 X cmGrowthExponent163_real)
  have hs := ComplexRaw.realPart_equiv (entireExponentialValue_congr (scalarSum X D)
    ⟨ofQComplex ⟨52,0⟩,ofQComplex_valid _⟩ real_gap_sum)
  exact RealRaw.le_trans (realPart_valid (entireExponentialValue X).property)
    (RealRaw.le_of_equiv (realPart_valid (entireExponentialValue cmGrowthExponent163).property)
      (realPart_valid (entireExponentialValue X).property) hc)
    (RealRaw.le_trans (realPart_valid (entireExponentialValue (scalarSum X D)).property) hm
      (RealRaw.le_trans (realPart_valid (entireExponentialValue ⟨ofQComplex ⟨52,0⟩,ofQComplex_valid _⟩).property)
        (RealRaw.le_of_equiv (realPart_valid (entireExponentialValue (scalarSum X D)).property)
          (realPart_valid (entireExponentialValue ⟨ofQComplex ⟨52,0⟩,ofQComplex_valid _⟩).property) hs)
        entireExponential_rational_fiftyTwo_upper))

end ComputableAnalysis.ModularForms
