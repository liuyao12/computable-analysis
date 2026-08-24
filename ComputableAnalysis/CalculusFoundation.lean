import ComputableAnalysis.RationalCircle
import ComputableAnalysis.Calculus
import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.TurningPointIntegral
import ComputableAnalysis.AbsIntegral
import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.PolynomialFTCValues
import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.Series
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.ExpProofs
import ComputableAnalysis.Logarithm
import ComputableAnalysis.ScalarODEUniqueness
import ComputableAnalysis.PeanoBaker

/-!
# Computable calculus foundation

This is the focused public entry point for the project's calculus route.  It
collects the rational-circle, finite-integral, effective-FTC, power-series,
exponential/logarithm, Fourier, and scalar/linear-ODE interfaces without
requiring users to import the full benchmark catalogue in `ComputableAnalysis`.

The imports expose certificates and raw algorithms; they do not introduce a
completed real-number or measurable-function foundation.
-/
