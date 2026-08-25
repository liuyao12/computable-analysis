import ComputableAnalysis.ExpProofs
import ComputableAnalysis.FiniteExponentialTaylor
import ComputableAnalysis.RotationSeries
import ComputableAnalysis.FiniteGapAwareInverseSearch
import ComputableAnalysis.IdentityInverse
import ComputableAnalysis.Logarithm

/-!
# Computable exponential and logarithm foundation

This scoped entry point collects rational Taylor-prefix evaluators, finite
tail certificates, rotation coordinates, and gap-aware inverse-search data for
the logarithm.  It exposes the computational contracts needed by later
calculus and ODE developments without postulating a completed real or complex
function space.

One representative evaluator is formalized for each pattern.  Scalar,
signed, and routine compositional variants are transported from these
certificates.
-/
