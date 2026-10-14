import ComputableAnalysis.ModularForms.NomeSeparation
import ComputableAnalysis.ModularForms.NomeRationalDifferential

/-! The rational cotangent nome kernel on the full upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem nomeDenominator_nonzero_of_ne_one (q : Scalar)
    (hq : ¬ q.val.Equiv (ofQComplex QComplex.one)) :
    NonzeroBoxSearch.Nonzero (nomeDenominator q) := by
  intro hd
  apply hq
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (nomeDenominator q).property) (hright := ofQComplex_valid _) hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := q.property) (hright := ofQComplex_valid _)
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change 1-Q=0 at he
  change Q=1
  grind only

theorem nome_upper_denominator_nonzero (z : Scalar) (hu : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero (nomeDenominator (nome.eval z hu)) :=
  nomeDenominator_nonzero_of_ne_one _ (nome_ne_one z hu)

theorem nomeRationalCotangentMap_full_domain (z : Scalar) :
    nomeRationalCotangentMap.domain z ↔ InUpperHalfPlane z.val := by
  constructor
  · intro hz; exact compose_inner_mem hz
  · intro hu
    exact (nomeRationalCotangentMap_domain z).mpr ⟨hu,nome_upper_denominator_nonzero z hu⟩

def upperNomeCotangentMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hu := nomeRationalCotangentMap.eval z ((nomeRationalCotangentMap_full_domain z).mpr hu)
  domain_congr := upperOpenData.invariant
  eval_congr z w _hz _hw he := nomeRationalCotangentMap.eval_congr z w _ _ he

def upperNomeCotangentMap_holomorphic : Holomorphic upperNomeCotangentMap := by
  apply nomeRationalCotangentMap_holomorphic.transfer upperNomeCotangentMap
    (fun z hz => (nomeRationalCotangentMap_full_domain z).mpr hz)
    ⟨upperRadius,upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ (upperNomeCotangentMap.eval z hz).property

theorem upperNomeCotangentMap_period_one (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (upperNomeCotangentMap.eval ⟨translate 1 z.val,translate_valid 1 z.property⟩
      (translate_mem 1 hu)).val.Equiv (upperNomeCotangentMap.eval z hu).val :=
  nomeRationalCotangentMap_period_one z ((nomeRationalCotangentMap_full_domain z).mpr hu)

def upperNomeCotangentDerivative (z : Scalar) (hu : InUpperHalfPlane z.val) : Scalar :=
  nomeRationalCotangentDerivative z ((nomeRationalCotangentMap_full_domain z).mpr hu)

theorem upperNomeCotangentMap_derivative (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (upperNomeCotangentMap_holomorphic.derivative z hu).val.Equiv
      (upperNomeCotangentDerivative z hu).val :=
  nomeRationalCotangentMap_derivative z ((nomeRationalCotangentMap_full_domain z).mpr hu)

theorem upperNomeCotangent_differential_identity (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (add (upperNomeCotangentDerivative z hu).val (upperNomeCotangentDerivative z hu).val).Equiv
      (mul nomeSlope.val (sub (mul (upperNomeCotangentMap.eval z hu).val
        (upperNomeCotangentMap.eval z hu).val) (ofQComplex QComplex.one))) :=
  nomeRationalCotangent_differential_identity z ((nomeRationalCotangentMap_full_domain z).mpr hu)

end ComputableAnalysis.ModularForms
