import ComputableAnalysis.Continuation.Realization
import ComputableAnalysis.Continuation.Reflection
import ComputableAnalysis.Continuation.Chain
import ComputableAnalysis.Continuation.Monodromy

/-!
# Foundations for analytic continuation

Checked here: represented neighborhoods and germs, derivative uniqueness,
local holomorphic gluing, actual finite chart chains, finite geometric
homotopies, and the local-transport-to-monodromy implication. Affine germs
provide a concrete identity/transport client.

Not claimed: the identity theorem for arbitrary holomorphic functions,
continuation along every path for an arbitrary initial germ, conversion of
arbitrary continuous homotopies to the finite presentation, or the full
analytic monodromy theorem. See docs/ANALYTIC_CONTINUATION.md.
-/
