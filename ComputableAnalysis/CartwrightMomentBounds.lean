import ComputableAnalysis.CartwrightFiniteSums

/-! Strictly positive lower bounds independent of the moment evaluation. -/
namespace ComputableAnalysis.CartwrightMoments
open CartwrightClockBounds ClosedArctanInverse ClockTrigonometry
open SinPiIntegral IntervalSelections CartwrightFiniteSums FiniteRiemannAlgebra

/-- A coarse rational cosine bound follows from the circle identity and
complementary angles, not from an integral evaluation. -/
theorem half_cosine_lower (q : Nat) (hq : 10≤q) :
    (1:Rat)/8 ≤ ((ClockTrigonometry.cosine (1/2)).compute q).lo := by
  have hu : Unit ((1:Rat)/2) := by constructor <;> decide +kernel
  have hcomp := (sample_complement hu q).1
  rw [show (1:Rat)-1/2=1/2 by decide +kernel] at hcomp
  have un := sample_unit ((1:Rat)/2) q
  have bo := sample_bounds ((1:Rat)/2) q
  have cc := Rat.mul_le_mul_of_nonneg_left bo.2.1 bo.1
  have ss := Rat.mul_le_mul_of_nonneg_left bo.2.2.2 bo.2.2.1
  have hl := neg_qabs_le_self (ClockTrigonometry.c (1/2) q-ClockTrigonometry.s (1/2) q)
  have hw := cosine_width hu q
  have hc := c_mem hu q
  have he := meshRadius_antitone hq
  have hnum : meshRadius 10=(1:Rat)/1024 := by decide +kernel
  rw [hnum] at he
  unfold QInterval.width at hw
  unfold InBox at hc
  simp only [Rat.div_def] at he ⊢
  grind

/-- Explicit lower witness for each moment; the witness is rational and nonzero. -/
def positiveBound (n : Nat) : Rat := ((3:Rat)/4)^n/16

theorem positiveBound_pos (n : Nat) : 0<positiveBound n := by
  unfold positiveBound
  rw [Rat.div_def]
  exact Rat.mul_pos (Rat.pow_pos (by decide +kernel)) ((Rat.inv_pos).2 (by decide +kernel))

theorem first_stage_positive (n : Nat) : positiveBound n ≤ ((integral n).compute 1).lo := by
  rw [integral_compute]
  have hN : cells 1=2 := rfl
  rw [hN]
  rw [sum_succ,sum_succ,sum_zero]
  have hg0 : grid 1 (0+1)=(1:Rat)/2 := by decide +kernel
  have hg1 : grid 1 (1+1)=(1:Rat) := by decide +kernel
  have hstep : step 1=(1:Rat)/2 := by decide +kernel
  rw [hg0,hg1,hstep]
  have hb := half_cosine_lower (sampleStage 1) (by decide)
  have hw := weight_bounds (t:=(1:Rat)/2) (by constructor <;> decide +kernel) n
  have hweight : weight n ((1:Rat)/2)=((3:Rat)/4)^n := by
    unfold weight; rw [show 1-(1:Rat)/2*(1/2)=3/4 by decide +kernel]
  have hmul := Rat.mul_le_mul_of_nonneg_left hb hw.1
  rw [value_compute (t:=(1:Rat)/2) (by constructor <;> decide +kernel)]
  have hz := (value_bounds (t:=1) (by constructor <;> decide +kernel) n (sampleStage 1)).1
  rw [hweight] at hmul ⊢
  unfold positiveBound
  simp only [Rat.div_def] at hmul ⊢
  grind

theorem integral_strict_lower (n : Nat) : 0<((integral n).compute 1).lo :=
  by have h:=positiveBound_pos n; have hh:=first_stage_positive n; grind

end ComputableAnalysis.CartwrightMoments
