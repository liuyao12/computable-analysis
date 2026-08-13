import ComputableAnalysis.Logarithm

/-!
# Reusable finite harmonic-growth interface

The divergence core is a finite reachability statement: a requested natural
target is exceeded at an explicit dyadic stage.  No infinite sum is formed.
-/

namespace ComputableAnalysis

structure FiniteHarmonicGrowthCertificate where
  target : Nat
  stage : Nat
  stage_eq : stage = 2 ^ (2 * target)
  target_reached : (target : Rat) ≤ Logarithm.harmonicSum stage

theorem FiniteHarmonicGrowthCertificate.explicit_stage
    (certificate : FiniteHarmonicGrowthCertificate) :
    (certificate.target : Rat) ≤
      Logarithm.harmonicSum (2 ^ (2 * certificate.target)) := by
  rw [← certificate.stage_eq]
  exact certificate.target_reached

def finiteHarmonicGrowthCertificate (target : Nat) :
    FiniteHarmonicGrowthCertificate where
  target := target
  stage := 2 ^ (2 * target)
  stage_eq := rfl
  target_reached := Logarithm.harmonicSum_two_pow_reaches target

end ComputableAnalysis
