import ComputableAnalysis.RotationSeries

/-!
# Lifting a bounded represented angle through the rotation series

The factorial rotation evaluator in `RotationSeries` takes a rational input.
This module packages the finite information needed to apply one common
evaluator to the successive rational midpoints of a represented angle.  It
does not assume a completed real or complex plane: the result is a valid
`ComplexRaw`, obtained by finite prefix stabilization.

The bounds `[1, 2]` and modulus `2 / (n + 1)` are chosen for the later
input `pi / 2`.  Keeping this lifting step generic means that the complex
calculation is checked without importing a particular pi registry.
-/

namespace ComputableAnalysis

namespace RotationLift

/-- A represented angle suitable for the common imaginary-axis rotation
series.  Its finite boxes are nested by `valid`, lie in `[1,2]`, and carry the
explicit modulus used to budget the error caused by replacing the represented
input with a rational midpoint. -/
structure HalfPiInput where
  raw : RealRaw
  valid : raw.Valid
  bounds : forall n : Nat,
    (1 : Rat) <= (raw.compute n).lo /\
      (raw.compute n).hi <= 2
  width_le_two_div_succ : forall n : Nat,
    (raw.compute n).width <= 2 / (((n + 1 : Nat) : Rat))

namespace HalfPiInput

/-- Every rational midpoint of the input boxes has absolute value at most
two, so it lies in the uniform factorial domain. -/
theorem midpoint_qabs_le_two (A : HalfPiInput) (n : Nat) :
    qabs ((A.raw.compute n).midpoint) <= 2 := by
  have hwidth := A.valid.1 n
  have hordered : (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hmid := QInterval.midpoint_mem hordered
  have hbounds := A.bounds n
  have hnonneg : 0 <= (A.raw.compute n).midpoint :=
    Rat.le_trans (Rat.le_of_lt (by native_decide : (0 : Rat) < 1))
      (Rat.le_trans hbounds.1 hmid.1)
  rw [qabs_eq_self_of_nonneg hnonneg]
  exact Rat.le_trans hmid.2 hbounds.2

/-- Later midpoint samples remain in the earlier certified input box. -/
theorem midpoint_sub_le_width (A : HalfPiInput) (k n : Nat) (hkn : k <= n) :
    qabs ((A.raw.compute n).midpoint - (A.raw.compute k).midpoint) <=
      (A.raw.compute k).width := by
  have hkwidth := A.valid.1 k
  have hkordered : (A.raw.compute k).lo <= (A.raw.compute k).hi := by
    unfold QInterval.width at hkwidth
    grind [Rat.sub_eq_add_neg]
  have hnwidth := A.valid.1 n
  have hnordered : (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    unfold QInterval.width at hnwidth
    grind [Rat.sub_eq_add_neg]
  have hmidk := QInterval.midpoint_mem hkordered
  have hmidn := QInterval.midpoint_mem hnordered
  have hnest := A.valid.2.1 k n hkn
  apply qabs_sub_le_of_common_bounds
  · exact Rat.le_trans hnest.1 hmidn.1
  · exact Rat.le_trans hmidn.2 hnest.2.2
  · exact hmidk.1
  · exact hmidk.2

/-- The direct rational-midpoint factorial candidate. -/
def rotationCandidate (A : HalfPiInput) : ComplexRaw where
  compute := fun n => RotationSeries.uniformRotationBox (A.raw.compute n).midpoint n

theorem rotationCandidate_compute (A : HalfPiInput) (n : Nat) :
    (rotationCandidate A).compute n =
      RotationSeries.uniformRotationBox (A.raw.compute n).midpoint n := rfl

theorem rotationCandidate_ordered (A : HalfPiInput) (n : Nat) :
    ((rotationCandidate A).compute n).Ordered := by
  rw [rotationCandidate_compute]
  have hvalid := RotationSeries.uniformRotationExpRaw_valid _
    (midpoint_qabs_le_two A n)
  exact ComplexRaw.valid_ordered hvalid n

theorem rotationCandidate_widths_shrink (A : HalfPiInput) :
    ComplexRaw.WidthsShrinkToZero (rotationCandidate A).compute := by
  intro eps
  obtain ⟨N, hN⟩ := RotationSeries.uniformRotationBox_widths_shrink 0 eps
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  rw [rotationCandidate_compute,
    RotationSeries.uniformRotationBox_width,
    RotationSeries.uniformRotationBox_height]
  rw [RotationSeries.uniformRotationBox_width,
    RotationSeries.uniformRotationBox_height] at h
  exact h

/-- The explicit input-error radius: the checked finite-prefix Lipschitz
budget is sixteen times the input-box width. -/
def rotationRadius (A : HalfPiInput) (n : Nat) : Rat :=
  16 * (A.raw.compute n).width

theorem rotationRadius_shrinks (A : HalfPiInput) :
    ShrinksToZero (rotationRadius A) := by
  apply shrinksToZero_of_natOverSuccBound (C := 32)
  intro n
  have hwidth := A.width_le_two_div_succ n
  unfold rotationRadius
  calc
    16 * (A.raw.compute n).width <=
        16 * (2 / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hwidth (by native_decide)
    _ = 32 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The stabilized represented-angle rotation.  It intersects a finite
prefix of widened midpoint candidates, so its validity is constructive. -/
def rotation (A : HalfPiInput) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (rotationCandidate A) (rotationRadius A)

theorem rotation_valid (A : HalfPiInput) : (rotation A).Valid := by
  unfold rotation
  apply ComplexRaw.cauchyStabilize_valid
  · exact rotationCandidate_ordered A
  · exact rotationCandidate_widths_shrink A
  · intro k n hkn
    have hfuture := RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
      (A.raw.compute n).midpoint (A.raw.compute k).midpoint
      (A.raw.compute k).width
      (midpoint_qabs_le_two A n) (midpoint_qabs_le_two A k)
      k n hkn (midpoint_sub_le_width A k n hkn)
    simpa [rotationCandidate_compute, rotationRadius] using hfuture
  · exact rotationRadius_shrinks A

/-- The stabilized box contains the direct rational-midpoint factorial box
at the same stage.  This is the finite enclosure used by a later
quarter-turn identification. -/
theorem rotation_contains_current_candidate (A : HalfPiInput) (n : Nat) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      ((rotation A).compute n) := by
  unfold rotation
  apply ComplexRaw.cauchyStabilize_contains_current
  intro k m hkm
  have hfuture := RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
    (A.raw.compute m).midpoint (A.raw.compute k).midpoint
    (A.raw.compute k).width
    (midpoint_qabs_le_two A m) (midpoint_qabs_le_two A k)
    k m hkm (midpoint_sub_le_width A k m hkm)
  simpa [rotationCandidate_compute, rotationRadius] using hfuture

end HalfPiInput

end RotationLift

end ComputableAnalysis
