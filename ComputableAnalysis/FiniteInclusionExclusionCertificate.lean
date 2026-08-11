import ComputableAnalysis.Basic

/-!
# A finite inclusion--exclusion certificate

This module gives the executable two-set inclusion--exclusion law for Boolean
predicates on a finite natural-number range, together with a concrete even /
multiple-of-three computation.
-/

namespace ComputableAnalysis

def countRange (n : Nat) (p : Nat → Bool) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => countRange k p + if p k = true then 1 else 0

theorem countRange_succ (n : Nat) (p : Nat → Bool) :
    countRange (n + 1) p = countRange n p +
      if p n = true then 1 else 0 := by
  rfl

theorem countRange_inclusion_exclusion (n : Nat) (p q : Nat → Bool) :
    countRange n p + countRange n q =
      countRange n (fun k => p k || q k) +
        countRange n (fun k => p k && q k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [countRange_succ, countRange_succ, countRange_succ, countRange_succ]
      cases hp : p n <;> cases hq : q n <;>
        simp [hp, hq] at *
      all_goals omega

theorem countRange_three_set_inclusion_exclusion
    (n : Nat) (p q r : Nat → Bool) :
    countRange n p + countRange n q + countRange n r +
        countRange n (fun k => p k && q k && r k) =
      countRange n (fun k => p k || q k || r k) +
        countRange n (fun k => p k && q k) +
        countRange n (fun k => p k && r k) +
        countRange n (fun k => q k && r k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [countRange_succ, countRange_succ, countRange_succ, countRange_succ,
        countRange_succ, countRange_succ, countRange_succ, countRange_succ]
      cases hp : p n <;> cases hq : q n <;> cases hr : r n <;>
        simp [hp, hq, hr] at *
      all_goals omega

def evenIndicator (n : Nat) : Bool := decide (n % 2 = 0)
def multipleThreeIndicator (n : Nat) : Bool := decide (n % 3 = 0)
def multipleFiveIndicator (n : Nat) : Bool := decide (n % 5 = 0)

theorem countRange_even_stage12 : countRange 12 evenIndicator = 6 := by
  native_decide

theorem countRange_multipleThree_stage12 :
    countRange 12 multipleThreeIndicator = 4 := by
  native_decide

theorem countRange_even_and_multipleThree_stage12 :
    countRange 12 (fun k => evenIndicator k && multipleThreeIndicator k) = 2 := by
  native_decide

theorem countRange_even_or_multipleThree_stage12 :
    countRange 12 (fun k => evenIndicator k || multipleThreeIndicator k) = 8 := by
  native_decide

theorem finite_inclusion_exclusion_stage12 :
    countRange 12 evenIndicator + countRange 12 multipleThreeIndicator =
      countRange 12 (fun k => evenIndicator k || multipleThreeIndicator k) +
        countRange 12 (fun k => evenIndicator k && multipleThreeIndicator k) := by
  simpa using countRange_inclusion_exclusion 12 evenIndicator multipleThreeIndicator

theorem finite_three_set_inclusion_exclusion_stage12 :
    countRange 12 evenIndicator + countRange 12 multipleThreeIndicator +
        countRange 12 multipleFiveIndicator +
        countRange 12 (fun k =>
          evenIndicator k && multipleThreeIndicator k && multipleFiveIndicator k) =
      countRange 12 (fun k =>
          evenIndicator k || multipleThreeIndicator k || multipleFiveIndicator k) +
        countRange 12 (fun k => evenIndicator k && multipleThreeIndicator k) +
        countRange 12 (fun k => evenIndicator k && multipleFiveIndicator k) +
        countRange 12 (fun k => multipleThreeIndicator k && multipleFiveIndicator k) := by
  simpa using countRange_three_set_inclusion_exclusion 12 evenIndicator
    multipleThreeIndicator multipleFiveIndicator

end ComputableAnalysis
