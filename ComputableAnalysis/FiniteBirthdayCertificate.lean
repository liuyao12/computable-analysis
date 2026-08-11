import ComputableAnalysis.Basic

/-!
# A finite birthday-problem certificate

The finite occupancy kernel counts injective assignments, all assignments,
and collision assignments exactly.  It is deliberately a combinatorial
certificate and does not introduce a general probability space.
-/

namespace ComputableAnalysis

def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | days, people + 1 => days * fallingFactorial (days - 1) people

def birthdayAllAssignments (days people : Nat) : Nat := days ^ people

def birthdayCollisionAssignments (days people : Nat) : Nat :=
  birthdayAllAssignments days people - fallingFactorial days people

theorem fallingFactorial_succ (days people : Nat) :
    fallingFactorial days (people + 1) =
      days * fallingFactorial (days - 1) people := by
  rfl

theorem birthday_stage10_people4_no_collision :
    fallingFactorial 10 4 = 5040 := by
  native_decide

theorem birthday_stage10_people4_all_assignments :
    birthdayAllAssignments 10 4 = 10000 := by
  native_decide

theorem birthday_stage10_people4_collisions :
    birthdayCollisionAssignments 10 4 = 4960 := by
  native_decide

theorem birthday_stage10_people4_no_collision_ratio :
    (fallingFactorial 10 4 : Rat) /
        (birthdayAllAssignments 10 4 : Rat) = 63 / 125 := by
  native_decide

theorem birthday_stage10_people4_collision_ratio :
    (birthdayCollisionAssignments 10 4 : Rat) /
        (birthdayAllAssignments 10 4 : Rat) = 62 / 125 := by
  native_decide

theorem birthday_stage10_people4_partition :
    (fallingFactorial 10 4 : Rat) /
          (birthdayAllAssignments 10 4 : Rat) +
        (birthdayCollisionAssignments 10 4 : Rat) /
          (birthdayAllAssignments 10 4 : Rat) = 1 := by
  rw [birthday_stage10_people4_no_collision_ratio,
    birthday_stage10_people4_collision_ratio]
  native_decide

theorem birthday_stage10_people5_no_collision :
    fallingFactorial 10 5 = 30240 := by
  native_decide

theorem birthday_stage10_people5_all_assignments :
    birthdayAllAssignments 10 5 = 100000 := by
  native_decide

theorem birthday_stage10_people5_collisions :
    birthdayCollisionAssignments 10 5 = 69760 := by
  native_decide

theorem birthday_stage10_people5_no_collision_ratio :
    (fallingFactorial 10 5 : Rat) /
        (birthdayAllAssignments 10 5 : Rat) = 189 / 625 := by
  native_decide

theorem birthday_stage10_people5_collision_ratio :
    (birthdayCollisionAssignments 10 5 : Rat) /
        (birthdayAllAssignments 10 5 : Rat) = 436 / 625 := by
  native_decide

theorem birthday_stage10_people5_partition :
    (fallingFactorial 10 5 : Rat) /
          (birthdayAllAssignments 10 5 : Rat) +
        (birthdayCollisionAssignments 10 5 : Rat) /
          (birthdayAllAssignments 10 5 : Rat) = 1 := by
  rw [birthday_stage10_people5_no_collision_ratio,
    birthday_stage10_people5_collision_ratio]
  native_decide

end ComputableAnalysis
