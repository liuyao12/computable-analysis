import ComputableAnalysis.ModularForms.DiskLambertLegacy
import ComputableAnalysis.ModularForms.RationalEisensteinSmallChart

/-! Normalized E2, E4 and E6 on the full open Euclidean nome disk.
 Primary samples take Q(i) arguments. Arbitrary represented evaluations are
 derived from those samples, with exact agreement on the previous chart.
 E2 is quasimodular; this construction does not change its transformation law. -/
namespace ComputableAnalysis.ModularForms.RationalEisenstein
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RationalLambert

abbrev unitDiskRationalDomain (q : QComplex) : Prop := QComplex.normSq q<1
abbrev unitDiskDomain := EisensteinUnitDisk.domain

def unitDiskRationalValue (w : Weight) (q : QComplex) (hq : unitDiskRationalDomain q) : Scalar :=
  ⟨add one (scaleRat (coefficient w) (DiskLambert.rationalValue q (degree w))),
    add_valid (ofQComplex_valid _) (scaleRat_valid (DiskLambert.rationalValue_valid q hq (degree w)))⟩

def unitDiskDerivedValue (w : Weight) (q : Scalar) (hq : unitDiskDomain q) : Scalar :=
  ⟨add one (scaleRat (coefficient w) (DiskLambert.value q hq (degree w))),
    add_valid (ofQComplex_valid _) (scaleRat_valid (DiskLambert.value_valid q hq (degree w)))⟩

def unitDiskDerivedMap (w : Weight) : DomainFunctions.Map where
  domain := unitDiskDomain
  eval := unitDiskDerivedValue w
  domain_congr := EisensteinUnitDisk.invariant
  eval_congr q z hq hz he := add_equiv (equiv_refl _ (ofQComplex_valid _))
    (scaleRat_equiv (r := coefficient w) (DiskLambert.value_congr q z hq hz he (degree w)))

def unitDiskRationalRaw (w : Weight) : FunctionRaw where
  domain := unitDiskRationalDomain
  compute q hq := (unitDiskRationalValue w q hq).val.compute

theorem unitDiskRationalRaw_valid (w : Weight) : (unitDiskRationalRaw w).Valid :=
  fun q hq => (unitDiskRationalValue w q hq).property

theorem unitDiskDerived_rational_agreement (w : Weight) (q : QComplex) (hq : unitDiskRationalDomain q) :
    (unitDiskDerivedValue w (point q) (EisensteinUnitDisk.rational_mem q hq)).val.Equiv (unitDiskRationalValue w q hq).val :=
  add_equiv (equiv_refl _ (ofQComplex_valid _))
    (scaleRat_equiv (r := coefficient w) (DiskLambert.value_rational_agreement q hq (degree w)))

theorem unitDiskDerived_smallChart_agreement (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) :
    (unitDiskDerivedValue w q (DiskLambert.wide_mem q hq)).val.Equiv (derivedValue w q hq).val := by
  have h := equiv_trans (DiskLambert.value_valid q (DiskLambert.wide_mem q hq) (degree w))
    (comparison q (LocalODE.interior_bound _ _ hq) (degree w)).property
    (RationalLambert.value_valid q hq (degree w) (degree_supported w))
    (DiskLambert.value_legacy_agreement q hq (degree w) (degree_supported w))
    (equiv_symm (RationalLambert.value_agrees q hq (degree w) (degree_supported w)))
  exact add_equiv (equiv_refl _ (ofQComplex_valid _)) (scaleRat_equiv (r := coefficient w) h)

theorem unitDiskRational_smallChart_agreement (w : Weight) (q : QComplex)
    (hq : unitDiskRationalDomain q) (hs : rationalDomain q) :
    (unitDiskRationalValue w q hq).val.Equiv (rationalValue w q hs).val := by
  have h := equiv_trans (DiskLambert.rationalValue_valid q hq (degree w))
    (comparison (point q) (rationalDomain_small q hs) (degree w)).property
    (RationalLambert.rationalValue_valid q (rationalDomain_small q hs) (degree w) (degree_supported w))
    (DiskLambert.rational_legacy_agreement q (rationalDomain_small q hs) (degree w) (degree_supported w))
    (equiv_symm (RationalLambert.rationalValue_agrees q (rationalDomain_small q hs) (degree w) (degree_supported w)))
  exact add_equiv (equiv_refl _ (ofQComplex_valid _)) (scaleRat_equiv (r := coefficient w) h)

def smallChartImplementation (w : Weight) : ComplexFunctionImplementation (unitDiskRationalRaw w) where
  raw := rationalRaw w
  valid := rationalRaw_valid w
  agrees q hq hs := unitDiskRational_smallChart_agreement w q hq hs

/-- Preferred full-disk rational sampler with the former chart as an
 explicitly proved alternative on its overlap. -/
def unitDiskRationalFunction (w : Weight) : ComplexFunction where
  preferred := unitDiskRationalRaw w
  valid := unitDiskRationalRaw_valid w
  implementations := [smallChartImplementation w]

abbrev unitDiskRationalEisensteinTwo := unitDiskRationalFunction .two
abbrev unitDiskRationalEisensteinFour := unitDiskRationalFunction .four
abbrev unitDiskRationalEisensteinSix := unitDiskRationalFunction .six
abbrev unitDiskSampledEisensteinTwo := unitDiskDerivedMap .two
abbrev unitDiskSampledEisensteinFour := unitDiskDerivedMap .four
abbrev unitDiskSampledEisensteinSix := unitDiskDerivedMap .six

abbrev rationalFunction := unitDiskRationalFunction

/-- Default elementary modular chart interfaces now cover the full unit disk. -/
abbrev rationalEisensteinTwo := unitDiskRationalEisensteinTwo
abbrev rationalEisensteinFour := unitDiskRationalEisensteinFour
abbrev rationalEisensteinSix := unitDiskRationalEisensteinSix
abbrev sampledEisensteinTwo := unitDiskSampledEisensteinTwo
abbrev sampledEisensteinFour := unitDiskSampledEisensteinFour
abbrev sampledEisensteinSix := unitDiskSampledEisensteinSix

/-- All exact small-chart clients use the same value after enlargement. -/
theorem unitDiskDerived_legacy_agreement (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) :
    (unitDiskDerivedValue w q (DiskLambert.wide_mem q hq)).val.Equiv ((legacyMap w).eval q (legacyDomain w q hq)).val :=
  equiv_trans (unitDiskDerivedValue w q _).property (derivedValue w q hq).property ((legacyMap w).eval q _).property
    (unitDiskDerived_smallChart_agreement w q hq) (derivedValue_agrees w q hq)

theorem sampledEisensteinTwo_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (sampledEisensteinTwo.eval q (DiskLambert.wide_mem q (tauEulerNomeDomain_wide_fifth_mem q hq))).val.Equiv (tauWeightTwoNomeMap.eval q hq).val :=
  equiv_trans (unitDiskDerivedValue .two q _).property (wideNomeEisensteinTwoMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property
    (tauWeightTwoNomeMap.eval q hq).property (unitDiskDerived_legacy_agreement .two q (tauEulerNomeDomain_wide_fifth_mem q hq))
    (wideNomeEisensteinTwoMap_agreement q hq)

theorem sampledEisensteinFour_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (sampledEisensteinFour.eval q (DiskLambert.wide_mem q (tauEulerNomeDomain_wide_fifth_mem q hq))).val.Equiv (nomeEisensteinFourMap.eval q hq).val :=
  equiv_trans (unitDiskDerivedValue .four q _).property (wideNomeEisensteinFourMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property
    (nomeEisensteinFourMap.eval q hq).property (unitDiskDerived_legacy_agreement .four q (tauEulerNomeDomain_wide_fifth_mem q hq))
    (wideNomeEisensteinFourMap_agreement q hq)

theorem sampledEisensteinSix_original_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (sampledEisensteinSix.eval q (DiskLambert.wide_mem q (tauEulerNomeDomain_wide_fifth_mem q hq))).val.Equiv (nomeEisensteinSixMap.eval q hq).val :=
  equiv_trans (unitDiskDerivedValue .six q _).property (wideNomeEisensteinSixMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property
    (nomeEisensteinSixMap.eval q hq).property (unitDiskDerived_legacy_agreement .six q (tauEulerNomeDomain_wide_fifth_mem q hq))
    (wideNomeEisensteinSixMap_agreement q hq)

end ComputableAnalysis.ModularForms.RationalEisenstein
