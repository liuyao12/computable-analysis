import ComputableAnalysis.ZetaReal

namespace ComputableAnalysis.ZetaReal.Tests

/-- A genuinely nonintegral exponent is in the public domain. -/
theorem threeHalves_domain : AboveOne (Real.ofRat (3/2)) := ⟨0, by change (1 : Rat) < 3/2; grind [Rat.div_def]⟩

def zetaThreeHalves : Real := zeta (Real.ofRat (3/2)) threeHalves_domain

theorem threeHalves_valid : zetaThreeHalves.preferred.Valid := zetaThreeHalves.valid

/-- Exact nonintegral coefficient and finite Dirichlet computation. -/
theorem threeHalves_coefficient : coefficient (3/2) 2=3/8 := by simp [coefficient]; grind [Rat.div_def]

theorem threeHalves_rectangle : rectangle (3/2) 3 2=171/128 := by
  simp [rectangle, moment, FormalPowerSeries.sumBelow_succ, coefficient, kernel, node, reciprocal, Rat.pow_succ, Rat.pow_zero]
  grind [Rat.div_def]

/-- Zero-width rational input can also be represented with a different stage schedule. -/
def delayedThree : Real := Real.ofRaw
  (RealRaw.schedule RealRaw.StageSchedule.id (RealRaw.ofRat 3))
  (RealRaw.schedule_valid _ (RealRaw.ofRat_valid 3) _)

theorem delayedThree_domain : AboveOne delayedThree := ⟨0, by decide⟩

theorem delayedThree_same_zeta :
    (zeta delayedThree delayedThree_domain).Equiv (zeta (Real.ofRat 3) ⟨0, by decide⟩) := by
  apply zeta_equiv
  exact RealRaw.equiv_symm (RealRaw.schedule_equiv _ (RealRaw.ofRat_valid 3) _)

/-- The public constructor accepts arbitrary valid algorithms, not only rational constants. -/
theorem arbitrary_input (s : Real) (hs : AboveOne s) : (zeta s hs).preferred.Valid := zeta_valid s hs

end ComputableAnalysis.ZetaReal.Tests
