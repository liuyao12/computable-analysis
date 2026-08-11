import ComputableAnalysis.DirichletSeries

/-!
# A finite strengthening of the Basel-series evaluator

This module exposes the exact finite decomposition used by the interval
algorithm: a later partial sum is the earlier partial sum plus the explicitly
computed finite tail.  It is an identity in `Rat`; it does not invoke a
completed zeta value or Euler's Basel identity.
-/

namespace ComputableAnalysis

namespace DirichletSeries

/-- Exact decomposition of a later finite Basel partial sum into an earlier
partial sum and the intervening finite tail. -/
theorem zetaTwoPartial_add_finiteTail_eq (n count : Nat) :
    zetaTwoPartial (n + count) =
      zetaTwoPartial n + zetaTwoFiniteTail n count := by
  induction count with
  | zero => simp [zetaTwoFiniteTail, Rat.add_zero]
  | succ count ih =>
      rw [show n + (count + 1) = (n + count) + 1 by omega]
      rw [zetaTwoPartial_succ, ih, zetaTwoFiniteTail_succ]
      grind [Rat.add_assoc]

end DirichletSeries

end ComputableAnalysis
