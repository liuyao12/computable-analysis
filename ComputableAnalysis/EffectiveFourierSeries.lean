import ComputableAnalysis.FiniteFourierFoundation

/-!
# Effective Fourier-stage interface

An infinite Fourier object is exposed here as a certified family of finite
rational-complex stages.  The limit is obtained by the existing finite-prefix
complex-box stabilization theorem; no completed `Real`, topology, or rate of
convergence is built into the interface.
-/

namespace ComputableAnalysis

structure EffectiveFourierSeries where
  root : QComplex
  mode : Nat
  stage : Nat -> List QComplex
  candidate : ComplexRaw
  radius : Nat -> Rat
  candidate_stage : forall n,
    candidate.compute n =
      QBox.point (finiteFourierSum root mode (stage n))
  candidate_ordered : forall n, (candidate.compute n).Ordered
  candidate_shrinks : ComplexRaw.WidthsShrinkToZero candidate.compute
  future_containment : forall k n, k <= n ->
    (candidate.compute n).NestedIn
      (QBox.expand (candidate.compute k) (radius k))
  radius_shrinks : ShrinksToZero radius

def EffectiveFourierSeries.stabilized
    (F : EffectiveFourierSeries) : ComplexRaw :=
  ComplexRaw.cauchyStabilize F.candidate F.radius

theorem EffectiveFourierSeries.stabilized_valid
    (F : EffectiveFourierSeries) : F.stabilized.Valid := by
  exact ComplexRaw.cauchyStabilize_valid
    F.candidate_ordered F.candidate_shrinks
    F.future_containment F.radius_shrinks

theorem EffectiveFourierSeries.stage_contained
    (F : EffectiveFourierSeries) (n : Nat) :
    (QBox.point (finiteFourierSum F.root F.mode (F.stage n))).NestedIn
      (F.stabilized.compute n) := by
  rw [← F.candidate_stage n]
  exact ComplexRaw.cauchyStabilize_contains_current F.future_containment n

end ComputableAnalysis
