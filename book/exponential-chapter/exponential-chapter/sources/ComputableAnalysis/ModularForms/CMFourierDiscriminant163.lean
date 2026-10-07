import ComputableAnalysis.ModularForms.CMExponentialSharperGrowth163
import ComputableAnalysis.ModularForms.CMNomeDecay163
import ComputableAnalysis.ModularForms.NomeDiscriminantNonvanishing
import ComputableAnalysis.ModularForms.CMDiscriminantAgreement163

/-! Actual CM Fourier discriminant with a stronger justified nome radius. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual CM nome has the stronger power-amplified decay bound. -/
theorem nome_cm163_small_thirtySix_power :
    Small (nome.eval cmScalar163 cmPoint163_upper).val (1/68719476736) :=
  nome_cm163_small_of_growth 68719476736 (by decide +kernel) cmGrowthExponential163_lower_thirtySix_power

def cmFourierDiscriminant163 : Scalar :=
  nomeModularDiscriminant (nome.eval cmScalar163 cmPoint163_upper) (1/68719476736)
    (by decide +kernel) (by decide +kernel) nome_cm163_small_thirtySix_power

/-- The constructed CM Fourier discriminant has a certified actual nome leading term. -/
theorem cmFourierDiscriminant163_nome_bound :
    Small (sub cmFourierDiscriminant163.val (nome.eval cmScalar163 cmPoint163_upper).val)
      (9000*(1/68719476736)*(1/68719476736)) :=
  nomeModularDiscriminant_linear_bound _ _ (by decide +kernel) (by decide +kernel)
    nome_cm163_small_thirtySix_power (by decide +kernel)

/-- The actual CM lattice discriminant agrees with the constructed normalized Fourier value. -/
theorem cmDiscriminant163_normalized_fourier :
    cmDiscriminant163.val.Equiv
      (scaleRat 4096 (mul (LocalODE.power geometricPiScalar.val 12) cmFourierDiscriminant163.val)) :=
  equiv_trans cmDiscriminant163.property
    (latticeDiscriminantMap.eval cmScalar163 cmPoint163_upper).property
    (scaleRat_valid (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 12) cmFourierDiscriminant163.property))
    (equiv_symm latticeDiscriminantMap_cm_agreement)
    (latticeDiscriminantMap_normalized_fourier cmScalar163 cmPoint163_upper _ (by decide +kernel)
      (by decide +kernel) nome_cm163_small_thirtySix_power)

end ComputableAnalysis.ModularForms
