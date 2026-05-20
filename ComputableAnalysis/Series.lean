import ComputableAnalysis.Basic

/-!
# Iteration-style series constructions

This file starts the lower-level construction layer discussed in the design
notes: a series algorithm is indexed by an iteration count, and it later
compiles to the precision-query `RealRaw` interface.
-/

namespace ComputableAnalysis

namespace Series

def alternatingSign (n : Nat) : Rat :=
  if n % 2 = 0 then 1 else -1

def signedTerm (term : Nat -> Rat) (n : Nat) : Rat :=
  alternatingSign n * term n

def partialSum (term : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => partialSum term n + signedTerm term n

def intervalBetween (a b : Rat) : QInterval :=
  if a <= b then { lo := a, hi := b } else { lo := b, hi := a }

/-- The natural interval attached to a partial-sum algorithm:
at stage `n`, return the interval between the `2n`th and `(2n+1)`st
partial sums. -/
def evenOddInterval (partials : Nat -> Rat) (n : Nat) : QInterval :=
  intervalBetween (partials (2 * n)) (partials (2 * n + 1))

/-- Natural interval algorithm for an alternating series specified by term
magnitudes.  This deliberately uses the slow, transparent stage `n →[S_{2n}, S_{2n+1}]`; any faster convergence rate should be extra metadata,
not hidden in the representation. -/
def alternatingInterval (term : Nat -> Rat) (n : Nat) : QInterval :=
  evenOddInterval (partialSum term) n

theorem alternatingSign_even (n : Nat) :
    alternatingSign (2 * n) = 1 := by
  unfold alternatingSign
  have h : (2 * n) % 2 = 0 := by omega
  rw [h]
  rfl

theorem partialSum_even_succ (term : Nat -> Rat) (n : Nat) :
    partialSum term (2 * n + 1) = partialSum term (2 * n) + term (2 * n) := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  simp [partialSum, signedTerm, alternatingSign_even]

/-- Data for an alternating series by magnitudes.

The interval at stage `n` is the interval between the `2n`th and `(2n+1)`st
partial sums.  The monotonicity field is not needed for the width-shrinking
theorem below, but it is the structural hypothesis that will later prove
nestedness and that these intervals enclose the same limit. -/
structure AlternatingRaw where
  term : Nat -> Rat
  term_nonneg : forall n, 0 <= term n
  term_decreasing : forall n, term (n + 1) <= term n
  term_shrinks : ShrinksToZero term

namespace AlternatingRaw

def interval (S : AlternatingRaw) (n : Nat) : QInterval :=
  alternatingInterval S.term n

theorem interval_width_eq (S : AlternatingRaw) (n : Nat) :
    (S.interval n).width = S.term (2 * n) := by
  have hsucc := partialSum_even_succ S.term n
  have hle :
      partialSum S.term (2 * n) <= partialSum S.term (2 * n + 1) := by
    rw [hsucc]
    grind [S.term_nonneg (2 * n)]
  simp [interval, alternatingInterval, evenOddInterval, intervalBetween,
    QInterval.width, hsucc]
  grind [Rat.sub_eq_add_neg]

theorem interval_width_nonneg (S : AlternatingRaw) (n : Nat) :
    0 <= (S.interval n).width := by
  rw [interval_width_eq]
  exact S.term_nonneg (2 * n)

/-- The consecutive-partial-sum intervals of an alternating series shrink
whenever the term magnitudes shrink. -/
theorem intervals_shrink (S : AlternatingRaw) :
    ShrinksToZero (fun n => (S.interval n).width) := by
  intro eps
  rcases S.term_shrinks eps with ⟨N, hN⟩
  exact ⟨N, by
    intro n hn
    change (S.interval n).width <= eps.val
    rw [interval_width_eq]
    exact hN (2 * n) (by omega)⟩
end AlternatingRaw

end Series

end ComputableAnalysis
