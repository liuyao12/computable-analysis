import ComputableAnalysis.ModularForms.GeometricEulerExponentialProduct
import ComputableAnalysis.ArctanGeometry

/-! The literal geometric angular mesh as upper rectangles for the sector kernel. -/
namespace ComputableAnalysis.ModularForms
open ArctanGeometry

def geometricAngularCells (N : Nat) : Nat → List (Rat × Rat)
  | 0 => []
  | k+1 => geometricAngularCells N k ++
      [((k:Rat)*geometricMeshStep N,((k+1:Nat):Rat)*geometricMeshStep N)]

theorem geometricAngularCells_covers (N k : Nat) :
    CoversInterval 0 ((k:Rat)*geometricMeshStep N) (geometricAngularCells N k) := by
  induction k with
  | zero => simp [geometricAngularCells,CoversInterval]
  | succ k ih =>
    apply CoversInterval.append ih
    have hh := Rat.le_of_lt (geometricMeshStep_positive N)
    have hc : (k:Rat) ≤ ((k+1:Nat):Rat) := by exact_mod_cast Nat.le_succ k
    exact ⟨rfl,Rat.mul_le_mul_of_nonneg_right hc hh,rfl⟩

theorem geometricAngularCells_endpoint_covers (N : Nat) :
    CoversInterval 0 1 (geometricAngularCells N (N+1)) := by
  have h := geometricAngularCells_covers N (N+1)
  rw [geometricMeshStep_identity] at h
  exact h

theorem geometricMeshAngle_eq_upper_rectangles (N k : Nat) :
    geometricMeshAngle N k = 2*integralUpperSum (geometricAngularCells N k) := by
  induction k with
  | zero => simp [geometricMeshAngle,geometricAngularCells,integralUpperSum]
  | succ k ih =>
    simp only [geometricMeshAngle,geometricAngularCells,integralUpperSum_append,
      integralUpperSum,integralUpperStep,integralKernel]
    rw [ih]
    have hc : ((k+1:Nat):Rat)=(k:Rat)+1 := by
      rw [Rat.natCast_add]
      have h1 : ((1:Nat):Rat)=1 := by decide +kernel
      rw [h1]
    rw [hc]
    simp only [Rat.div_def]
    grind only

theorem geometricAngularCells_squareSum (N k : Nat) :
    intervalSquareSum (geometricAngularCells N k) =
      (k:Rat)*geometricMeshStep N*geometricMeshStep N := by
  induction k with
  | zero => simp [geometricAngularCells,intervalSquareSum]
  | succ k ih =>
    have happ (xs ys : List (Rat × Rat)) :
        intervalSquareSum (xs++ys)=intervalSquareSum xs+intervalSquareSum ys := by
      induction xs with
      | nil => simp [intervalSquareSum]; grind only
      | cons p ps hps => simp only [List.cons_append,intervalSquareSum,hps]; grind only
    rw [geometricAngularCells,happ,ih]
    simp only [intervalSquareSum,Rat.natCast_add]
    have h1 : ((1:Nat):Rat)=1 := by decide +kernel
    rw [h1]
    grind only

theorem geometricAngularRectangles_endpoint_width (N : Nat) :
    (integralSumInterval (geometricAngularCells N (N+1))).width ≤ 2*geometricMeshStep N := by
  have hc := geometricAngularCells_endpoint_covers N
  have hb := integralSumInterval_width_le_two_squareSum _
    (CoversInterval.unit (by decide) (Rat.le_refl) hc)
  rw [geometricAngularCells_squareSum] at hb
  rw [geometricMeshStep_identity,Rat.one_mul] at hb
  exact hb

theorem geometricAngularRectangles_sector_overlap (N n : Nat) :
    QInterval.Overlaps (integralSumInterval (geometricAngularCells N (N+1)))
      (positiveLoopComputeAtStage 1 n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval (by decide) n]
  exact integralSumInterval_overlaps_geometricSumInterval_of_covers (by decide) _ _
    (geometricAngularCells_endpoint_covers N)
    (arctanAreaLoopState_intervals_covers (by decide) n)

end ComputableAnalysis.ModularForms
