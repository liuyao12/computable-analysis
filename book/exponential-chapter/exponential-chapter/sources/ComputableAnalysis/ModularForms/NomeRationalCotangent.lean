import ComputableAnalysis.ModularForms.CotangentRationalDerivative
import ComputableAnalysis.ModularForms.NomePeriodicity

/-! Actual rational nome composition on its justified pole-free domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def nomeRationalCotangentMap : DomainFunctions.Map := compose cotangentRationalMap nome

def nomeRationalCotangentMap_holomorphic : Holomorphic nomeRationalCotangentMap :=
  cotangentRationalMap_holomorphic.compose nome_holomorphic

theorem nomeRationalCotangentMap_domain (z : Scalar) :
    nomeRationalCotangentMap.domain z ↔
      ∃ hu : InUpperHalfPlane z.val, NonzeroBoxSearch.Nonzero (nomeDenominator (nome.eval z hu)) := by
  constructor
  · intro hz
    exact ⟨compose_inner_mem hz,(cotangentRationalMap_domain _).mp (compose_outer_mem hz)⟩
  · rintro ⟨hu,hd⟩
    exact ⟨hu,(cotangentRationalMap_domain _).mpr hd⟩

theorem nomeRationalCotangentMap_shift_domain (z : Scalar) (hz : nomeRationalCotangentMap.domain z) :
    nomeRationalCotangentMap.domain ⟨translate 1 z.val,translate_valid 1 z.property⟩ := by
  let hu := compose_inner_mem hz
  have he := nome_period_one z hu
  exact ⟨translate_mem 1 hu,(cotangentRationalMap.domain_congr _ _ he).mpr (compose_outer_mem hz)⟩

theorem nomeRationalCotangentMap_period_one (z : Scalar) (hz : nomeRationalCotangentMap.domain z) :
    (nomeRationalCotangentMap.eval ⟨translate 1 z.val,translate_valid 1 z.property⟩
      (nomeRationalCotangentMap_shift_domain z hz)).val.Equiv
      (nomeRationalCotangentMap.eval z hz).val :=
  cotangentRationalMap.eval_congr _ _ _ _ (nome_period_one z (compose_inner_mem hz))

theorem nomeRationalCotangentMap_series_agreement (z : Scalar) (hz : nomeRationalCotangentMap.domain z)
    (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hs : Small (nome.eval z (compose_inner_mem hz)).val r) :
    (nomeRationalCotangentMap.eval z hz).val.Equiv
      (cotangentNomeKernel (nome.eval z (compose_inner_mem hz)) r) :=
  cotangentRationalMap_series_agreement _ r hr hlocal hs (compose_outer_mem hz)

end ComputableAnalysis.ModularForms
