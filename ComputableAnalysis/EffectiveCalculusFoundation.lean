import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.PolynomialMeanValue
import ComputableAnalysis.FiniteQuadratureMeanValue
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.FiniteGapAwareInverseSearch
import ComputableAnalysis.FinitePiecewiseAbsoluteValue

/-!
# Effective calculus foundation

This scoped entry point collects the finite secant, derivative-bound,
curvature, stabilization, inverse-search, and L'Hopital contracts that turn
an explicit interval evaluator into an effective FTC certificate.

The declarations live in their subject modules. This file deliberately adds
no aliases: importing a foundation changes availability, not theorem names.
Each special function still supplies its own domain, schedule, and finite
overlap data; no completeness theorem is introduced.
-/
