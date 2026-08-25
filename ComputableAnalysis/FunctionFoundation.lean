import ComputableAnalysis.Basic
import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.Extension
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.AlgebraicFunctions

/-!
# Computable function and representation foundation

This scoped entry point collects rational-domain complex-box functions,
partial real restrictions, interval domains, elementary evaluators, and
representation transport.  A function is introduced by its computation and
domain; continuity or analyticity is added only when a later theorem needs
the corresponding finite certificate.
-/
