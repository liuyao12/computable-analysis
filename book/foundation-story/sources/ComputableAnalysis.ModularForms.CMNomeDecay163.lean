import ComputableAnalysis.ModularForms.CMNomeSmall163
import ComputableAnalysis.ModularForms.CMExponentialGrowth163

/-! Stronger actual CM nome decay, independent of reciprocal clipping choices. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem nome_cm163_small_of_growth (l : Rat) (hp : 0<l)
    (hl : (RealRaw.ofRat l).Le cmGrowthValue163) :
    Small (nome.eval cmScalar163 cmPoint163_upper).val (1/l) := by
  let r := RealRaw.positiveReciprocal cmGrowthValue163 l
  have hx : cmGrowthValue163.Valid := realPart_valid (entireExponentialValue cmGrowthExponent163).property
  have hr : r.Valid := RealRaw.positiveReciprocal_valid _ _ hx hp (fun n => hl 0 n)
  have he := positiveReciprocal_threshold_equiv cmGrowthValue163 hx 25 l (by decide) hp
    cmGrowthExponential163_lower_twentyFive hl
  have hc := ofRealRaw_equiv_of_equiv (x := cmNomeMagnitude163) (y := r) cmNomeMagnitude163_valid hr he
  have hn := equiv_trans (nome.eval cmScalar163 cmPoint163_upper).property
    (neg_valid (ofRealRaw_valid _ cmNomeMagnitude163_valid)) (neg_valid (ofRealRaw_valid _ hr))
    nome_cm163_reciprocal (neg_equiv hc)
  have hb := SeriesLimitLaws.small_neg (positiveReciprocal_embedding_small cmGrowthValue163 hx l hp hl)
  exact Small.congr (neg_valid (ofRealRaw_valid _ hr)) (nome.eval cmScalar163 cmPoint163_upper).property
    (equiv_symm hn) hb

theorem nome_cm163_small_power :
    Small (nome.eval cmScalar163 cmPoint163_upper).val (1/16777216) :=
  nome_cm163_small_of_growth 16777216 (by decide) cmGrowthExponential163_lower_power

end ComputableAnalysis.ModularForms
