import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.Series

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
    (QBox.point (finiteFourierSum root mode (stage n))).NestedIn
      (candidate.compute n)
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
  exact QBox.nested_trans (F.candidate_stage n)
    (ComplexRaw.cauchyStabilize_contains_current F.future_containment n)

/-! Every finite Fourier computation is an effective series with finite
support: the stage is already stable, so its radius and all box widths are
zero.  This is a useful sanity-check instance before adding genuinely
infinite coefficient tails. -/
def finiteSupportFourierSeries
    (root : QComplex) (mode : Nat) (samples : List QComplex) :
    EffectiveFourierSeries where
  root := root
  mode := mode
  stage := fun _ => samples
  candidate := ComplexRaw.ofQComplex (finiteFourierSum root mode samples)
  radius := fun _ => 0
  candidate_stage := by
    intro n
    unfold ComplexRaw.ofQComplex QBox.point QBox.NestedIn
    exact ⟨⟨Rat.le_refl, Rat.le_refl⟩, ⟨Rat.le_refl, Rat.le_refl⟩⟩
  candidate_ordered := by
    intro n
    change (QBox.point (finiteFourierSum root mode samples)).Ordered
    unfold QBox.point QBox.Ordered
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  candidate_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [ComplexRaw.ofQComplex, QBox.point, QBox.width, QBox.height]
    constructor <;> grind
  future_containment := by
    intro k n hkn
    change (QBox.point (finiteFourierSum root mode samples)).NestedIn
      (QBox.expand (QBox.point (finiteFourierSum root mode samples)) 0)
    simp [QBox.point, QBox.expand, QBox.NestedIn]
    constructor <;> grind
  radius_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    exact Rat.le_of_lt eps.property

/-! A first genuinely infinite instance: the zero-frequency partial sums of
the geometric coefficient family `1, r, r^2, ...`.  The candidate boxes use
the exact rational prefix and the exact geometric-series upper endpoint.
Their widths shrink by the existing effective geometric-series theorem. -/
def geometricFourierZeroModeSeries
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) : EffectiveFourierSeries where
  root := QComplex.one
  mode := 0
  stage := fun n =>
    [QComplex.ofRat (Series.geometricSum r n)]
  candidate := {
    compute := fun n =>
      { lo := { re := Series.geometricSum r n, im := 0 },
        hi := { re := 1 / (1 - r), im := 0 } }
  }
  radius := fun _ => 0
  candidate_stage := by
    intro n
    dsimp
    change (QBox.point
      (finiteFourierSum QComplex.one 0
        [QComplex.ofRat (Series.geometricSum r n)])).NestedIn _
    simp [finiteFourierSum_singleton, QComplex.natPow,
      QComplex.mul, QComplex.one, QComplex.ofRat,
      QBox.point, QBox.NestedIn]
    constructor
    · exact ⟨by grind [Rat.add_zero], by native_decide⟩
    · exact ⟨by simpa [Rat.add_zero, Rat.sub_eq_add_neg] using
          Series.geometricSum_le_inv_one_sub hr0 hr1 n,
        by native_decide⟩
  candidate_ordered := by
    intro n
    dsimp
    unfold QBox.Ordered
    simp only [QComplex.le_def]
    exact ⟨Series.geometricSum_le_inv_one_sub hr0 hr1 n,
      by native_decide⟩
  candidate_shrinks := by
    dsimp
    intro eps
    obtain ⟨N, hN⟩ :=
      (Series.geometricRaw_valid_of_le_half hr0 hrhalf hr1).2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    simp only [QBox.width, QBox.height]
    change 1 / (1 - r) - Series.geometricSum r n <= eps.val /\
      0 - 0 <= eps.val
    exact ⟨h, by grind [Rat.sub_self]⟩
  future_containment := by
    dsimp
    intro k n hkn
    change
      ({ lo := { re := Series.geometricSum r n, im := 0 },
          hi := { re := 1 / (1 - r), im := 0 } } : QBox).NestedIn
        (QBox.expand
          { lo := { re := Series.geometricSum r k, im := 0 },
            hi := { re := 1 / (1 - r), im := 0 } } 0)
    simp [QBox.expand, QBox.NestedIn]
    constructor
    · exact ⟨by simpa [Rat.add_zero, Rat.sub_eq_add_neg] using
        Series.geometricSum_le_of_le hr0 hkn, by grind⟩
    · exact ⟨by grind, by grind⟩
  radius_shrinks := by
    intro eps
    refine ⟨0, ?_⟩
    intro n hn
    exact Rat.le_of_lt eps.property

end ComputableAnalysis
