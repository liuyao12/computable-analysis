import ComputableAnalysis.FiniteCubeRootBisectionExample
import ComputableAnalysis.FiniteInverseSearchInterface

/-!
# A packaged finite cube-root inverse certificate

The stage-24 bisection for x^3 = 2 is exposed as a reusable inverse-search
certificate.  It is the computable core of the doubling-cube row; the
classical straightedge-and-compass constructibility boundary remains separate.
-/

namespace ComputableAnalysis

def cubeRootInverseCertificate : FiniteInverseSearchCertificate :=
  finiteInverseSearchCertificate cubeTarget 2 cubeTargetInitial 24
    (by native_decide) (by native_decide) (by native_decide)

theorem cubeRootInverseCertificate_output :
    cubeRootInverseCertificate.output =
      { lo := 21137967 / 16777216, hi := 1321123 / 1048576 } := by
  native_decide

theorem cubeRootInverseCertificate_output_bracket :
    cubeTarget cubeRootInverseCertificate.output.lo <= 2 /\
      2 <= cubeTarget cubeRootInverseCertificate.output.hi :=
  cubeRootInverseCertificate.output_bracket

theorem cubeRootInverseCertificate_output_width :
    cubeRootInverseCertificate.output.width = 1 / 16777216 := by
  rw [cubeRootInverseCertificate_output]
  native_decide

end ComputableAnalysis
