import ComputableAnalysis.ModularForms.CMGrowthBounds163
import ComputableAnalysis.ModularForms.RealExponentialCore

/-! Real exponential lower bounds at arbitrary valid strictly positive real inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem cmGrowthExponential163_lower_twentyFive :
    (RealRaw.ofRat 25).Le (entireExponentialValue cmGrowthExponent163).val.realPart := by
  have hb := entireExponential_real_rational_lower cmGrowthReal163 cmGrowthReal163_valid
    cmGrowthReal163_positive 24 cmGrowthReal163_lower_twentyFour
  have hc : (1:Rat)+24=25 := by decide +kernel
  rw [hc] at hb
  have he := entireExponentialValue_congr cmGrowthExponent163
    ⟨ofRealRaw cmGrowthReal163,ofRealRaw_valid _ cmGrowthReal163_valid⟩ cmGrowthExponent163_real
  exact RealRaw.le_trans (realPart_valid (entireExponentialValue _).property) hb
    (RealRaw.le_of_equiv (realPart_valid (entireExponentialValue _).property)
      (realPart_valid (entireExponentialValue cmGrowthExponent163).property)
      (ComplexRaw.realPart_equiv (equiv_symm he)))

end ComputableAnalysis.ModularForms
