import ComputableAnalysis.EnclosureHolomorphicConstancy
import ComputableAnalysis.EnclosureHolomorphicCauchy
import ComputableAnalysis.ExponentialComputations.ComplexFunctions
import ComputableAnalysis.ElementarySineODEComparison
import ComputableAnalysis.RiemannHilbert.ScalarPolynomialQuotients
import ComputableAnalysis.ModularForms.UnitDiskEisensteinHolomorphic

/-! A portfolio for the enclosure semantics, using the actual elementary
and special-function computations. Existing quantitative witnesses are
sufficient evidence; jets and numerical candidates are not consumed here.
Primary rational agreements and convergence remain separate checked facts. -/
namespace ComputableAnalysis.EnclosureHolomorphicExamples
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Arbitrary finite polynomials, with arbitrary valid represented coefficients. -/
theorem polynomial (P : ScalarPolynomial.Polynomial) :
    IsEnclosureHolomorphic (ScalarPolynomial.function P) := (ScalarPolynomial.holomorphic P).enclosure

/-- The full pole-free domain of each represented-coefficient polynomial fraction. -/
theorem rationalFunction (r : ScalarPolynomialQuotients.Fraction) :
    IsEnclosureHolomorphic (ScalarPolynomialQuotients.function r) :=
  (ScalarPolynomialQuotients.holomorphic r).enclosure

theorem reciprocal : IsEnclosureHolomorphic ReciprocalHolomorphic.function :=
  ReciprocalHolomorphic.holomorphic.enclosure

theorem reciprocal_derivative (a : Scalar) (ha : NonzeroBoxSearch.Nonzero a) :
    HasEnclosureDerivativeAt ReciprocalHolomorphic.function a ha (ReciprocalDifference.derivative a ha) :=
  (ReciprocalHolomorphic.hasDerivativeAt a ha).enclosure

/-- The established primary exponential's derived entire evaluator. -/
theorem exponential : IsEnclosureHolomorphic ExponentialComputations.Complex.expFunction :=
  ExponentialComputations.Complex.expHolomorphic.enclosure

theorem exponential_derivative (z : Scalar) :
    HasEnclosureDerivativeAt ExponentialComputations.Complex.expFunction z trivial
      (ExponentialComputations.Complex.exp z) :=
  ((ExponentialComputations.Complex.expHolomorphic.atPoint z trivial).enclosure).congrDerivative
    (ExponentialComputations.Complex.exp_derivative z)

/-- Both oscillator coordinates are entire for every valid complex frequency,
including the computed irrational frequency used by normalized trigonometry. -/
theorem sine (a : Scalar) : IsEnclosureHolomorphic (ElementarySineODE.sine a) :=
  (ElementarySineODE.sine_holomorphic a).enclosure

theorem cosine (a : Scalar) : IsEnclosureHolomorphic (ElementarySineODE.cosine a) :=
  (ElementarySineODE.cosine_holomorphic a).enclosure

theorem sine_derivative (a z : Scalar) :
    HasEnclosureDerivativeAt (ElementarySineODE.sine a) z trivial
      (scalarProduct a ((ElementarySineODE.cosine a).eval z trivial)) :=
  ((ElementarySineODE.sine_holomorphic a).atPoint z trivial).enclosure.congrDerivative
    (ElementarySineODE.sine_derivative a z)

theorem cosine_derivative (a z : Scalar) :
    HasEnclosureDerivativeAt (ElementarySineODE.cosine a) z trivial
      (scalarNeg (scalarProduct a ((ElementarySineODE.sine a).eval z trivial))) :=
  ((ElementarySineODE.cosine_holomorphic a).atPoint z trivial).enclosure.congrDerivative
    (ElementarySineODE.cosine_derivative a z)

/-- Logarithm germs retain their actual center, normalization, and branch domain. -/
theorem logarithm (s : ExponentialComputations.Complex.LogSeed) : IsEnclosureHolomorphic s.function :=
  s.holomorphic.enclosure

theorem logarithm_derivative (s : ExponentialComputations.Complex.LogSeed) (z : Scalar)
    (hz : s.function.domain z) :
    HasEnclosureDerivativeAt s.function z hz
      (RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero _ s.nonzero z hz)) :=
  (s.holomorphic.atPoint z hz).enclosure.congrDerivative (s.derivative z hz)

/-- Every nonnegative-degree Lambert series on the full open Euclidean unit disk. -/
theorem lambert (k : Nat) : IsEnclosureHolomorphic (ModularForms.DiskLambert.map k) :=
  (ModularForms.DiskLambert.holomorphic k).enclosure

/-- The primary rational Eisenstein functions have holomorphic derived
extensions at every represented point of the full unit disk. -/
theorem eisenstein (w : ModularForms.RationalEisenstein.Weight) :
    IsEnclosureHolomorphic (ModularForms.RationalEisenstein.unitDiskDerivedMap w) :=
  (ModularForms.RationalEisenstein.unitDiskDerivedMap_holomorphic w).enclosure

/-- Actual primary-to-extension agreement, rather than restriction of a map. -/
theorem eisenstein_rational_agreement (w : ModularForms.RationalEisenstein.Weight)
    (q : QComplex) (hq : QComplex.normSq q<1) :
    (ModularForms.RationalEisenstein.unitDiskDerivedValue w (ModularForms.RationalLambert.point q)
      (ModularForms.EisensteinUnitDisk.rational_mem q hq)).val.Equiv
      (ModularForms.RationalEisenstein.unitDiskRationalValue w q hq).val :=
  ModularForms.RationalEisenstein.unitDiskDerived_rational_agreement w q hq


/-- The actual exponential computation agrees with its constructed Taylor
series at every represented center, throughout its proved local neighborhood. -/
noncomputable def exponentialTaylor (a : Scalar) : DomainFunctions.Map :=
  EnclosureCauchy.taylor ExponentialComputations.Complex.expFunction exponential a trivial

theorem exponentialTaylor_agrees (a z : Scalar) (hz : (exponentialTaylor a).domain z) :
    (exponentialTaylor a).eval z hz≈ExponentialComputations.Complex.exp z :=
  EnclosureCauchy.taylor_expansion _ exponential a trivial z hz

/-- A non-elementary application at every represented full-disk Eisenstein
center; the actual series radius and contour coefficients are constructed. -/
noncomputable def eisensteinTaylor (w : ModularForms.RationalEisenstein.Weight)
    (a : Scalar) (ha : ModularForms.RationalEisenstein.unitDiskDomain a) : DomainFunctions.Map :=
  EnclosureCauchy.taylor (ModularForms.RationalEisenstein.unitDiskDerivedMap w) (eisenstein w) a ha

theorem eisensteinTaylor_agrees (w : ModularForms.RationalEisenstein.Weight)
    (a : Scalar) (ha : ModularForms.RationalEisenstein.unitDiskDomain a) (z : Scalar)
    (hz : (eisensteinTaylor w a ha).domain z) :
    (eisensteinTaylor w a ha).eval z hz≈
      ModularForms.RationalEisenstein.unitDiskDerivedValue w z
        (EnclosureCauchy.taylor_domain _ (eisenstein w) a ha z hz) :=
  EnclosureCauchy.taylor_expansion _ (eisenstein w) a ha z hz

end ComputableAnalysis.EnclosureHolomorphicExamples
