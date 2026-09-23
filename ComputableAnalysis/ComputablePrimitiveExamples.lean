import ComputableAnalysis.ComputableFactoredPrimitives
import ComputableAnalysis.AlgebraicFunctions

/-! Irrational coefficients are actual interval algorithms in these examples.
The checked successes exercise factor separation, generated coefficient
inversion, and the represented formal-derivative identity. -/
namespace ComputableAnalysis
namespace ComputablePrimitiveExamples
open ComputableCoefficient ComputableFactoredAlgebra

/-- The repository's bisection square root, with its existing validity proof. -/
def rootTwo : Real := Real.ofRaw (sqrtRaw 2 (by unfold sqrtDomain; decide +kernel))
  (sqrtRaw_valid 2 (by unfold sqrtDomain; decide +kernel))

def r : C := .parameter rootTwo

def factors : List Factor :=
  [.linear r 0, .quadratic (r.div (.rational 2)) r 1]

def numerator : List C := [.rational 1, r]

def checked? := certifyFactors 4 factors

theorem factors_checked : checked?.isSome = true := by decide +kernel

def checked : CheckedFactors factors := checked?.get factors_checked

def poleCheck? := certify 4 (.apart (eval (denominator factors) (.rational 0)))

theorem pole_checked : poleCheck?.isSome = true := by decide +kernel

def poleCheck : SampleCertificate (fun s => (eval (denominator factors) (.rational 0)).sample s ≠ 0) :=
  poleCheck?.get pole_checked

def derivative? := ((primitive factors numerator).formalDerivative (.rational 0)).realize 4
def integrand? := (integrand factors numerator (.rational 0)).realize 4

theorem derivative_computes : derivative?.isSome = true := by decide +kernel
theorem integrand_computes : integrand?.isSome = true := by decide +kernel

def derivativeValue : Value := derivative?.get derivative_computes
def integrandValue : Value := integrand?.get integrand_computes

/-- This is raw-computation equivalence, not an equality of rational proxies. -/
theorem irrational_primitive_correct :
    derivativeValue.real.preferred.Equiv integrandValue.real.preferred := by
  apply primitive_correct factors numerator checked (.rational 0) poleCheck 4 4 derivativeValue integrandValue
  · exact (Option.some_get derivative_computes).symm
  · exact (Option.some_get integrand_computes).symm

/-- Unseparated coefficients produce a failed check, not an invented inverse. -/
theorem zero_inverse_rejected : ((.rational 0 : C).inv.realize 4).isNone = true := by decide +kernel

/-- Duplicate blocks are rejected until their multiplicities are combined. -/
theorem duplicate_irrational_pole_rejected :
    (certifyFactors 4 [.linear r 0, .linear r 0]).isNone = true := by decide +kernel

end ComputablePrimitiveExamples
end ComputableAnalysis
