import ComputableAnalysis.ModularForms.RepresentedRotationAgreement
import ComputableAnalysis.ModularForms.LatticeHalfFrequencyName
import ComputableAnalysis.RotationLift

/-! An executable precision schedule for the actual lattice half-frequency. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def latticeHalfFrequencyWidthStage (eps : QPos) : Nat :=
  PrecisionSearch.stage (ofRealRaw latticeHalfFrequencyName)
    (ofRealRaw_valid _ latticeHalfFrequencyName_valid) eps

theorem latticeHalfFrequencyWidthStage_spec (eps : QPos) :
    (latticeHalfFrequencyName.compute (latticeHalfFrequencyWidthStage eps)).width≤eps.val :=
  (PrecisionSearch.stage_spec (ofRealRaw latticeHalfFrequencyName)
    (ofRealRaw_valid _ latticeHalfFrequencyName_valid) eps).1

def latticeHalfFrequencyTolerance (n : Nat) : QPos :=
  ⟨2/((n+1:Nat):Rat),by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel) (Rat.inv_pos.mpr (by exact_mod_cast (show 0<n+1 by omega)))⟩

def latticeHalfFrequencyStage : Nat → Nat
  | 0 => latticeHalfFrequencyWidthStage (latticeHalfFrequencyTolerance 0)
  | n+1 => max (latticeHalfFrequencyStage n)
    (max (n+1) (latticeHalfFrequencyWidthStage (latticeHalfFrequencyTolerance (n+1))))

theorem latticeHalfFrequencyStage_step (n : Nat) :
    latticeHalfFrequencyStage n≤latticeHalfFrequencyStage (n+1) := Nat.le_max_left _ _

theorem latticeHalfFrequencyStage_monotone (n m : Nat) (h : n≤m) :
    latticeHalfFrequencyStage n≤latticeHalfFrequencyStage m := by
  induction m with
  | zero =>
    have hn : n=0 := by omega
    subst n
    exact Nat.le_refl _
  | succ m ih =>
    by_cases hn : n≤m
    · exact Nat.le_trans (ih hn) (latticeHalfFrequencyStage_step m)
    · have he : n=m+1 := by omega
      subst n
      exact Nat.le_refl _

theorem latticeHalfFrequencyStage_ge (n : Nat) : n≤latticeHalfFrequencyStage n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem latticeHalfFrequencyStage_precision (n : Nat) :
    latticeHalfFrequencyWidthStage (latticeHalfFrequencyTolerance n)≤latticeHalfFrequencyStage n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

def latticeHalfFrequencySchedule : RealRaw.StageSchedule where
  stage := latticeHalfFrequencyStage
  monotone := latticeHalfFrequencyStage_monotone
  cofinal n := ⟨n,latticeHalfFrequencyStage_ge n⟩

def latticeHalfFrequencyRotationInput : RotationLift.HalfPiInput where
  raw := RealRaw.schedule latticeHalfFrequencySchedule latticeHalfFrequencyName
  valid := RealRaw.schedule_valid _ latticeHalfFrequencyName_valid latticeHalfFrequencySchedule
  bounds n := latticeHalfFrequencyName_bounds (latticeHalfFrequencyStage n)
  width_le_two_div_succ n := by
    have hn := latticeHalfFrequencyName_valid.2.1
      (latticeHalfFrequencyWidthStage (latticeHalfFrequencyTolerance n))
      (latticeHalfFrequencyStage n) (latticeHalfFrequencyStage_precision n)
    have hw := QInterval.width_le_of_contains (⟨hn.1,hn.2.2⟩ :
      (latticeHalfFrequencyName.compute (latticeHalfFrequencyWidthStage (latticeHalfFrequencyTolerance n))).ContainsInterval
        (latticeHalfFrequencyName.compute (latticeHalfFrequencyStage n)))
    exact Rat.le_trans hw (latticeHalfFrequencyWidthStage_spec (latticeHalfFrequencyTolerance n))

theorem latticeHalfFrequencyRotationInput_agreement :
    latticeHalfFrequencyRotationInput.raw.Equiv (RealRaw.scaleRat (1/2) latticeFrequency.val.realPart) :=
  RealRaw.equiv_trans latticeHalfFrequencyRotationInput.valid latticeHalfFrequencyName_valid
    (RealRaw.scaleRat_valid (realPart_valid latticeFrequency.property))
    (RealRaw.equiv_symm (RealRaw.schedule_equiv _ latticeHalfFrequencyName_valid latticeHalfFrequencySchedule))
    latticeHalfFrequencyName_agreement

theorem latticeHalfFrequency_exponential_rotation :
    (entireExponentialValue
      ⟨imaginaryAxis latticeHalfFrequencyRotationInput.raw,
        imaginaryAxis_valid latticeHalfFrequencyRotationInput.valid⟩).val.Equiv
      (RotationLift.HalfPiInput.rotation latticeHalfFrequencyRotationInput) :=
  entireExponential_represented_rotation latticeHalfFrequencyRotationInput

end ComputableAnalysis.ModularForms
