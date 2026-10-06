import ComputableAnalysis.RiemannHilbert.ReciprocalAnalyticBounds
import ComputableAnalysis.RiemannHilbert.DomainFunctions

/-! The actual reciprocal is holomorphic on all nonzero valid represented
complex values. Both derivative and derivative continuity use explicit
rational moduli; no formal-jet assumption replaces the remainder proof. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
open ComplexRaw FunctionTheory NonzeroBoxSearch RepresentedReciprocal ReciprocalAnalyticBounds

def function : DomainFunctions.Map where
  domain := Nonzero
  eval := inverse
  domain_congr := nonzero_congr
  eval_congr := inverse_congr

def hasDerivativeAt (a : Scalar) (ha : Nonzero a) :
    DomainFunctions.HasDerivativeAt function a ha (ReciprocalDifference.derivative a ha) where
  delta := delta a ha (quadraticConstant a ha) (quadraticConstant_nonneg a ha)
  estimate eps H z hz hH hza := by
    have hr := Rat.le_trans hH (delta_radius a ha _ (quadraticConstant_nonneg a ha) eps)
    have hp := Rat.le_trans hH (delta_precision a ha _ (quadraticConstant_nonneg a ha) eps)
    have hs := remainder_bound a z ha hz H hr hza
    have hlin := precision_estimate _ (quadraticConstant_nonneg a ha) eps H hp
    exact hs.mono (Rat.mul_le_mul_of_nonneg_right hlin (Rat.le_of_lt H.property))

def continuousDerivative :
    DomainFunctions.ContinuousOn Nonzero ReciprocalDifference.derivative where
  delta := fun a ha => delta a ha (derivativeConstant a ha) (derivativeConstant_nonneg a ha)
  estimate a ha eps z hz hza := by
    let H := delta a ha (derivativeConstant a ha) (derivativeConstant_nonneg a ha) eps
    have hs := derivative_difference_bound a z ha hz H
      (delta_radius a ha _ (derivativeConstant_nonneg a ha) eps) hza
    exact hs.mono (precision_estimate _ (derivativeConstant_nonneg a ha) eps H
      (delta_precision a ha _ (derivativeConstant_nonneg a ha) eps))

def holomorphic : DomainFunctions.Holomorphic function where
  openDomain := {
    radius := ReciprocalLocalBounds.radius
    inside := ReciprocalLocalBounds.inside }
  derivative := ReciprocalDifference.derivative
  atPoint := hasDerivativeAt
  derivative_congr := ReciprocalDifference.derivative_congr
  continuousDerivative := continuousDerivative

end ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
