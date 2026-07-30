import ComputableAnalysis.PiProofs

/-!
# Canonical-logarithm transport for the pi formula

The checked finite integration-by-parts formula uses the literal reciprocal
integral for log two.  This module records the exact, finite certificate that
an inverse-exponential logarithm must supply before that endpoint can replace
the literal integral.  It does not assume an inverse-function or ODE theorem.
-/

namespace ComputableAnalysis

namespace PiProofs

/-- A certified raw presentation of the canonical logarithm at two.

The agreement field is the sole analytic transport still required from a
future inverse-exponential construction.  The existing finite reciprocal
integral is deliberately the target, so this structure contains no unstated
general integration-by-parts or completeness principle. -/
structure CanonicalLogTwoCertificate where
  raw : RealRaw
  valid : raw.Valid
  agreesWithReciprocalIntegral :
    raw.Equiv Logarithm.logTwoReciprocalIntegral

/-- The natural integration-by-parts pi formula when the logarithmic endpoint
is supplied by a certified canonical-logarithm presentation. -/
def piFromCanonicalLogTwo (logTwo : CanonicalLogTwoCertificate) : RealRaw :=
  (4 : Nat) * Logarithm.arctanIntegralTriangle + (2 : Nat) * logTwo.raw

theorem piFromCanonicalLogTwo_valid (logTwo : CanonicalLogTwoCertificate) :
    (piFromCanonicalLogTwo logTwo).Valid := by
  unfold piFromCanonicalLogTwo
  exact RealRaw.add_valid
    (RealRaw.natScale_valid 4 Logarithm.arctanIntegralTriangle_valid)
    (RealRaw.natScale_valid 2 logTwo.valid)

/-- Replacing the reciprocal-integral endpoint by a certified canonical
logarithm preserves the supplied finite integration-by-parts raw computation. -/
theorem piFromCanonicalLogTwo_equiv_reciprocalIntegral
    (logTwo : CanonicalLogTwoCertificate) :
    (piFromCanonicalLogTwo logTwo).Equiv
      Logarithm.piTriangleLogReciprocalIntegral := by
  have htriangle : ((4 : Nat) * Logarithm.arctanIntegralTriangle).Valid :=
    RealRaw.natScale_valid 4 Logarithm.arctanIntegralTriangle_valid
  have hcanonical : ((2 : Nat) * logTwo.raw).Valid :=
    RealRaw.natScale_valid 2 logTwo.valid
  have hreciprocal :
      ((2 : Nat) * Logarithm.logTwoReciprocalIntegral).Valid :=
    RealRaw.natScale_valid 2 Logarithm.logTwoReciprocalIntegral_valid
  unfold piFromCanonicalLogTwo Logarithm.piTriangleLogReciprocalIntegral
  exact RealRaw.add_equiv htriangle htriangle hcanonical hreciprocal
    (RealRaw.equiv_refl ((4 : Nat) * Logarithm.arctanIntegralTriangle)
      htriangle)
    (RealRaw.natScale_equiv 2 logTwo.agreesWithReciprocalIntegral)

/-- The canonical-logarithm version of the arctangent integration-by-parts
formula is pi whenever its endpoint certificate is supplied.  Thus the future
canonical row reduces to proving one raw equivalence at two. -/
theorem piFromCanonicalLogTwo_equiv_piCircleArea
    (logTwo : CanonicalLogTwoCertificate) :
    (piFromCanonicalLogTwo logTwo).Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    (piFromCanonicalLogTwo_valid logTwo)
    Logarithm.piTriangleLogReciprocalIntegral_valid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    (piFromCanonicalLogTwo_equiv_reciprocalIntegral logTwo)
    piTriangleLogReciprocalIntegral_equiv_piCircleArea

end PiProofs

end ComputableAnalysis
