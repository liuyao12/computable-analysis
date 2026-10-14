import ComputableAnalysis.ModularForms.RationalLambertSamples
import ComputableAnalysis.ModularForms.RationalLambertLift
import ComputableAnalysis.ModularForms.WideNomeEisensteinTwo
import ComputableAnalysis.ModularForms.WideNomeEisensteinFour
import ComputableAnalysis.ModularForms.WideNomeEisensteinSix
import ComputableAnalysis.FunctionSampling

/-! Rational-first normalized Eisenstein nome charts. The represented maps
are derived from moving exact rational Lambert prefixes. Their domain is the
existing open coordinate square of radius `1/64`, including irrational points.
Weight two is quasimodular; holomorphicity alone does not assert modularity. -/
namespace ComputableAnalysis.ModularForms.RationalEisenstein
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RationalLambert

inductive Weight where
  | two | four | six
  deriving DecidableEq

def degree : Weight → Nat | .two => 1 | .four => 3 | .six => 5
def coefficient : Weight → Rat | .two => -24 | .four => 240 | .six => -504

theorem degree_supported (w : Weight) : degree w=1 ∨ degree w=3 ∨ degree w=5 := by
  cases w <;> simp [degree]

def legacyMap : Weight → DomainFunctions.Map
  | .two => wideNomeEisensteinTwoMap
  | .four => wideNomeEisensteinFourMap
  | .six => wideNomeEisensteinSixMap

theorem legacyDomain (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) : (legacyMap w).domain q := by
  cases w <;> exact hq

def derivedValue (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) : Scalar :=
  ⟨add one (scaleRat (coefficient w) (RationalLambert.value q hq (degree w))),
    add_valid (ofQComplex_valid _) (scaleRat_valid (value_valid q hq (degree w) (degree_supported w)))⟩

theorem derivedValue_agrees (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) :
    (derivedValue w q hq).val.Equiv ((legacyMap w).eval q (legacyDomain w q hq)).val := by
  have h := add_equiv (equiv_refl _ (ofQComplex_valid QComplex.one))
    (scaleRat_equiv (r := coefficient w) (value_agrees q hq (degree w) (degree_supported w)))
  cases w <;> simpa [derivedValue,degree,coefficient,legacyMap,RationalLambert.comparison,
    wideNomeEisensteinTwoMap,wideNomeEisensteinFourMap,wideNomeEisensteinSixMap,
    wideLambertFirstMap,wideLambertThirdMap,wideLambertFifthMap,ComplexRaw.one,
    if_pos (by decide : (1:Nat)=1),if_neg (by decide : (3:Nat)≠1),
    if_pos (by decide : (3:Nat)=3),if_neg (by decide : (5:Nat)≠1),if_neg (by decide : (5:Nat)≠3)] using h

def derivedMap (w : Weight) : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval := derivedValue w
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q z hq hz he := equiv_trans (derivedValue w q hq).property ((legacyMap w).eval q (legacyDomain w q hq)).property
    (derivedValue w z hz).property (derivedValue_agrees w q hq)
    (equiv_trans ((legacyMap w).eval q (legacyDomain w q hq)).property ((legacyMap w).eval z (legacyDomain w z hz)).property (derivedValue w z hz).property
      ((legacyMap w).eval_congr q z (legacyDomain w q hq) (legacyDomain w z hz) he) (equiv_symm (derivedValue_agrees w z hz)))

noncomputable def derivedMap_holomorphic (w : Weight) : Holomorphic (derivedMap w) := by
  have h : Holomorphic (legacyMap w) := by
    cases w
    · exact wideNomeEisensteinTwoMap_holomorphic
    · exact wideNomeEisensteinFourMap_holomorphic
    · exact wideNomeEisensteinSixMap_holomorphic
  exact h.transfer (derivedMap w) (fun q h => legacyDomain w q h)
    ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
    (fun q hq => equiv_symm (derivedValue_agrees w q hq))

def rationalDomain (q : QComplex) : Prop := BoxApproximation.coordinateBound q < (1:Rat)/64

theorem rationalDomain_small (q : QComplex) (hq : rationalDomain q) : Small (ofQComplex q) ((1:Rat)/64) :=
  (BoxApproximation.rational_small q).mono (Rat.le_of_lt hq)

theorem rationalDomain_inside (q : QComplex) (hq : rationalDomain q) : wideLambertFifthDomain (point q) :=
  ⟨BoxApproximation.coordinateBound q,BoxApproximation.coordinateBound_nonneg q,hq,BoxApproximation.rational_small q⟩

/-- Direct rational evaluation uses fixed rational prefixes, not a restriction
of any represented-point Eisenstein map. -/
def rationalValue (w : Weight) (q : QComplex) (hq : rationalDomain q) : Scalar :=
  ⟨add one (scaleRat (coefficient w) (RationalLambert.rationalValue q (degree w))),
    add_valid (ofQComplex_valid _) (scaleRat_valid
      (rationalValue_valid q (rationalDomain_small q hq) (degree w) (degree_supported w)))⟩

theorem rationalValue_agrees (w : Weight) (q : QComplex) (hq : rationalDomain q) :
    (rationalValue w q hq).val.Equiv ((legacyMap w).eval (point q) (legacyDomain w (point q) (rationalDomain_inside q hq))).val := by
  have h := add_equiv (equiv_refl _ (ofQComplex_valid QComplex.one))
    (scaleRat_equiv (r := coefficient w) (RationalLambert.rationalValue_agrees q (rationalDomain_small q hq) (degree w) (degree_supported w)))
  cases w <;> simpa [rationalValue,degree,coefficient,legacyMap,RationalLambert.comparison,
    wideNomeEisensteinTwoMap,wideNomeEisensteinFourMap,wideNomeEisensteinSixMap,
    wideLambertFirstMap,wideLambertThirdMap,wideLambertFifthMap,ComplexRaw.one,
    if_pos (by decide : (1:Nat)=1),if_neg (by decide : (3:Nat)≠1),
    if_pos (by decide : (3:Nat)=3),if_neg (by decide : (5:Nat)≠1),if_neg (by decide : (5:Nat)≠3)] using h

theorem derived_rational_agreement (w : Weight) (q : QComplex) (hq : rationalDomain q) :
    ((derivedMap w).eval (point q) (rationalDomain_inside q hq)).val.Equiv (rationalValue w q hq).val :=
  equiv_trans (derivedValue w (point q) (rationalDomain_inside q hq)).property
    ((legacyMap w).eval (point q) (legacyDomain w (point q) (rationalDomain_inside q hq))).property (rationalValue w q hq).property
    (derivedValue_agrees w _ _) (equiv_symm (rationalValue_agrees w q hq))

def rationalRaw (w : Weight) : FunctionRaw where
  domain := rationalDomain
  compute q hq := (rationalValue w q hq).val.compute

theorem rationalRaw_valid (w : Weight) : (rationalRaw w).Valid := fun q hq => (rationalValue w q hq).property

def legacyRationalRaw (w : Weight) : FunctionRaw where
  domain := rationalDomain
  compute q hq := ((legacyMap w).eval (point q) (legacyDomain w (point q) (rationalDomain_inside q hq))).val.compute

def legacyImplementation (w : Weight) : ComplexFunctionImplementation (rationalRaw w) where
  raw := legacyRationalRaw w
  valid q hq := ((legacyMap w).eval (point q) (legacyDomain w (point q) (rationalDomain_inside q hq))).property
  agrees q hq _ := rationalValue_agrees w q hq

def smallChartRationalFunction (w : Weight) : ComplexFunction where
  preferred := rationalRaw w
  valid := rationalRaw_valid w
  implementations := [legacyImplementation w]

abbrev smallChartRationalEisensteinTwo := smallChartRationalFunction .two
abbrev smallChartRationalEisensteinFour := smallChartRationalFunction .four
abbrev smallChartRationalEisensteinSix := smallChartRationalFunction .six
abbrev smallChartSampledEisensteinTwo := derivedMap .two
abbrev smallChartSampledEisensteinFour := derivedMap .four
abbrev smallChartSampledEisensteinSix := derivedMap .six

/-- Exact overlap with the original narrower nome computations. -/
theorem smallChartSampledEisensteinTwo_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (smallChartSampledEisensteinTwo.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv (tauWeightTwoNomeMap.eval q hq).val :=
  equiv_trans (derivedValue .two q _).property (wideNomeEisensteinTwoMap.eval q _).property
    (tauWeightTwoNomeMap.eval q hq).property (derivedValue_agrees .two q _) (wideNomeEisensteinTwoMap_agreement q hq)

theorem smallChartSampledEisensteinFour_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (smallChartSampledEisensteinFour.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv (nomeEisensteinFourMap.eval q hq).val :=
  equiv_trans (derivedValue .four q _).property (wideNomeEisensteinFourMap.eval q _).property
    (nomeEisensteinFourMap.eval q hq).property (derivedValue_agrees .four q _) (wideNomeEisensteinFourMap_agreement q hq)

theorem smallChartSampledEisensteinSix_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (smallChartSampledEisensteinSix.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv (nomeEisensteinSixMap.eval q hq).val :=
  equiv_trans (derivedValue .six q _).property (wideNomeEisensteinSixMap.eval q _).property
    (nomeEisensteinSixMap.eval q hq).property (derivedValue_agrees .six q _) (wideNomeEisensteinSixMap_agreement q hq)

end ComputableAnalysis.ModularForms.RationalEisenstein
