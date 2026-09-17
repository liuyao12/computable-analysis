import ComputableAnalysis.CartwrightMoments

namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse SinPiIntegral IntervalSelections

/-- The frequency in quarter-turn coordinates. -/
def frequency : RealRaw := RealRaw.scaleRat (1/2) CosinePrimitive.pi

def frequencySample (q : Nat) : Rat := (piCircleArea.compute q).lo/2

theorem frequency_valid : frequency.Valid := RealRaw.scaleRat_valid CosinePrimitive.pi_valid

theorem pi_stage_bounds (q : Nat) :
    2 ≤ (piCircleArea.compute q).lo ∧ (piCircleArea.compute q).lo ≤ (piCircleArea.compute q).hi ∧
    (piCircleArea.compute q).hi ≤ 4 := by
  have h:=CauchyPi.piCircleArea_valid.2.1 0 q (Nat.zero_le q)
  have h0 : piCircleArea.compute 0=({lo:=2,hi:=4}:QInterval) := by decide +kernel
  rw [h0] at h
  exact h

theorem frequencySample_bounds (q : Nat) : 1≤frequencySample q ∧ frequencySample q≤2 := by
  have h:=pi_stage_bounds q
  unfold frequencySample
  simp only [Rat.div_def]
  constructor <;> grind only

theorem frequencySample_mem (q : Nat) : InBox (frequencySample q) (frequency.compute q) := by
  have hp : InBox (piCircleArea.compute q).lo (CosinePrimitive.pi.compute q) := by
    rw [CosinePrimitive.pi_compute]
    exact ⟨Rat.le_refl,(pi_stage_bounds q).2.1⟩
  have h:=scale_mem hp (r:=1/2) (by decide +kernel)
  have he : (1:Rat)/2*(piCircleArea.compute q).lo=frequencySample q := by
    unfold frequencySample; simp only [Rat.div_def]; grind
  rw [he] at h
  exact h


end ComputableAnalysis.CartwrightMoments
