import ComputableAnalysis.ModularForms.QuarterRotationDerivative

/-! Executable rescheduling of arbitrary valid angles on the quarter-angle chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

structure BoundedAngle where
  raw : RealRaw
  valid : raw.Valid
  bounds : ∀ n, (1:Rat)≤(raw.compute n).lo ∧ (raw.compute n).hi≤2

namespace BoundedAngle
def widthStage (A : BoundedAngle) (eps : QPos) : Nat :=
  PrecisionSearch.stage (ofRealRaw A.raw)
    (ofRealRaw_valid _ A.valid) eps

theorem widthStage_spec (A : BoundedAngle) (eps : QPos) :
    (A.raw.compute (widthStage A eps)).width≤eps.val :=
  (PrecisionSearch.stage_spec (ofRealRaw A.raw)
    (ofRealRaw_valid _ A.valid) eps).1

def tolerance (n : Nat) : QPos :=
  ⟨2/((n+1:Nat):Rat),by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel) (Rat.inv_pos.mpr (by exact_mod_cast (show 0<n+1 by omega)))⟩

def stage (A : BoundedAngle) : Nat → Nat
  | 0 => widthStage A (tolerance 0)
  | n+1 => max (stage A n)
    (max (n+1) (widthStage A (tolerance (n+1))))

theorem stage_step (A : BoundedAngle) (n : Nat) :
    stage A n≤stage A (n+1) := Nat.le_max_left _ _

theorem stage_monotone (A : BoundedAngle) (n m : Nat) (h : n≤m) :
    stage A n≤stage A m := by
  induction m with
  | zero =>
    have hn : n=0 := by omega
    subst n
    exact Nat.le_refl _
  | succ m ih =>
    by_cases hn : n≤m
    · exact Nat.le_trans (ih hn) (stage_step A m)
    · have he : n=m+1 := by omega
      subst n
      exact Nat.le_refl _

theorem stage_ge (A : BoundedAngle) (n : Nat) : n≤stage A n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem stage_precision (A : BoundedAngle) (n : Nat) :
    widthStage A (tolerance n)≤stage A n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

def schedule (A : BoundedAngle) : RealRaw.StageSchedule where
  stage := stage A
  monotone := stage_monotone A
  cofinal n := ⟨n,stage_ge A n⟩

def rotationInput (A : BoundedAngle) : RotationLift.HalfPiInput where
  raw := RealRaw.schedule (schedule A) A.raw
  valid := RealRaw.schedule_valid _ A.valid (schedule A)
  bounds n := A.bounds (stage A n)
  width_le_two_div_succ n := by
    have hn := A.valid.2.1
      (widthStage A (tolerance n))
      (stage A n) (stage_precision A n)
    have hw := QInterval.width_le_of_contains (⟨hn.1,hn.2.2⟩ :
      (A.raw.compute (widthStage A (tolerance n))).ContainsInterval
        (A.raw.compute (stage A n)))
    exact Rat.le_trans hw (widthStage_spec A (tolerance n))


theorem rotationInput_agreement (A : BoundedAngle) :
    (rotationInput A).raw.Equiv A.raw :=
  RealRaw.equiv_symm (RealRaw.schedule_equiv A.raw A.valid (schedule A))

theorem exponential_positive_imaginary (A : BoundedAngle) :
    InUpperHalfPlane (entireExponentialValue
      ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩).val := by
  let B := rotationInput A
  have hi := imaginaryAxis_equiv B.valid A.valid (rotationInput_agreement A)
  have he := entireExponentialValue_congr
    ⟨imaginaryAxis B.raw,imaginaryAxis_valid B.valid⟩
    ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩ hi
  have hr := entireExponential_represented_rotation B
  have hp := (upperHalfPlane_congr
    (entireExponentialValue ⟨imaginaryAxis B.raw,imaginaryAxis_valid B.valid⟩).property
    (RotationLift.HalfPiInput.rotation_valid B) hr).mpr
    (rotationQuarter_represented_positive B)
  exact (upperHalfPlane_congr
    (entireExponentialValue ⟨imaginaryAxis B.raw,imaginaryAxis_valid B.valid⟩).property
    (entireExponentialValue ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩).property he).mp hp

theorem rotation_derivative_negative (A : BoundedAngle) :
    (angleRotationMap_holomorphic.derivative
      ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩ ⟨trivial,trivial⟩).val.realPart.Neg := by
  let B := rotationInput A
  let x : Scalar := ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩
  let y : Scalar := ⟨ofRealRaw B.raw,ofRealRaw_valid _ B.valid⟩
  let e := angleRotationMap.eval x ⟨trivial,trivial⟩
  let d := angleRotationMap_holomorphic.derivative x ⟨trivial,trivial⟩
  have hxy : y.val.Equiv x.val :=
    ofRealRaw_equiv_of_equiv B.valid A.valid (rotationInput_agreement A)
  have hc := angleRotationMap.eval_congr y x ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ hxy
  have hr := angleRotationMap_real_input_agreement B
  have hy := (upperHalfPlane_congr
    (angleRotationMap.eval y ⟨trivial,trivial⟩).property
    (RotationLift.HalfPiInput.rotation_valid B) hr).mpr
    (rotationQuarter_represented_positive B)
  have hu : InUpperHalfPlane e.val := (upperHalfPlane_congr
    (angleRotationMap.eval y ⟨trivial,trivial⟩).property e.property hc).mp hy
  have hp := imaginary_unit_mul_negative_real e hu
  have hd := angleRotationMap_differential_identity x ⟨trivial,trivial⟩
  have hn := positive_of_equiv
    (RealRaw.neg_valid (realPart_valid (mul_valid latticeImaginaryUnit.property e.property)))
    (RealRaw.neg_valid (realPart_valid d.property))
    (RealRaw.neg_equiv (realPart_equiv (equiv_symm hd))) hp
  obtain ⟨N,hN⟩ := hn
  refine ⟨N,?_⟩
  change 0 < -(d.val.compute N).hi.re at hN
  change (d.val.compute N).hi.re < 0
  grind only

end BoundedAngle
end ComputableAnalysis.ModularForms
