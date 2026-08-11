import ComputableAnalysis.Basic

/-!
# A finite derangement-formula certificate

The derangement recurrence and one inclusion--exclusion evaluation are
checked as exact finite computations.  This is the algorithmic core of the
benchmark item; no asymptotic probability statement is used.
-/

namespace ComputableAnalysis

def finiteFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * finiteFactorial n

def derangements : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangements (n + 1) + derangements n)

theorem derangements_zero : derangements 0 = 1 := by
  rfl

theorem derangements_one : derangements 1 = 0 := by
  rfl

theorem derangements_succ_succ (n : Nat) :
    derangements (n + 2) = (n + 1) *
      (derangements (n + 1) + derangements n) := by
  rfl

theorem derangements_stage6 : derangements 6 = 265 := by
  native_decide

theorem derangements_stage8 : derangements 8 = 14833 := by
  native_decide

theorem derangements_stage10 : derangements 10 = 1334961 := by
  native_decide

theorem derangements_stage6_inclusion_exclusion :
    (finiteFactorial 6 : Rat) *
        (1 - 1 + 1 / 2 - 1 / 6 + 1 / 24 - 1 / 120 + 1 / 720) =
      derangements 6 := by
  native_decide

theorem derangement_formula_certificate :
    derangements 6 = 265 /\
      derangements 8 = 14833 /\
      (finiteFactorial 6 : Rat) *
          (1 - 1 + 1 / 2 - 1 / 6 + 1 / 24 - 1 / 120 + 1 / 720) =
        derangements 6 := by
  exact ⟨derangements_stage6, derangements_stage8,
    derangements_stage6_inclusion_exclusion⟩

theorem derangements_stage10_inclusion_exclusion :
    (finiteFactorial 10 : Rat) *
        (1 - 1 + 1 / 2 - 1 / 6 + 1 / 24 - 1 / 120 + 1 / 720 -
          1 / 5040 + 1 / 40320 - 1 / 362880 + 1 / 3628800) =
      derangements 10 := by
  native_decide

end ComputableAnalysis
