import ComputableAnalysis.ComplexMultiplication

/-!
# Executable search for a narrow complex box

Termination uses validity's shrinking-width proof only in the proof of
accessibility. The runtime tests rational inequalities at successive stages;
it never extracts a natural number using classical choice.
-/
namespace ComputableAnalysis.RiemannHilbert.PrecisionSearch

private def Next (good : Nat → Bool) (later current : Nat) : Prop :=
  later = current + 1 ∧ good current = false

private theorem accessible (good : Nat → Bool) (steps : Nat) (n : Nat)
    (h : good (n + steps) = true) : Acc (Next good) n := by
  induction steps generalizing n with
  | zero =>
      constructor
      intro k hk
      have hg : good n = true := by simpa using h
      simp [Next, hg] at hk
  | succ steps ih =>
      constructor
      intro k hk
      rcases hk with ⟨rfl, _⟩
      apply ih
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem wellFounded (good : Nat → Bool)
    (h : ∃ N, ∀ n, N ≤ n → good n = true) : WellFounded (Next good) := by
  constructor
  intro n
  obtain ⟨N, hN⟩ := h
  exact accessible good N n (hN (n+N) (by omega))

/-- Search at consecutive stages, with erased termination evidence. -/
def firstFrom (good : Nat → Bool) (h : ∃ N, ∀ n, N ≤ n → good n = true)
    (n : Nat) : Nat :=
  (wellFounded good h).fix (fun current recurse =>
    if hg : good current = true then current
    else recurse (current+1) ⟨rfl, by cases hh : good current <;> simp_all⟩) n

theorem firstFrom_eq (good : Nat → Bool)
    (h : ∃ N, ∀ n, N ≤ n → good n = true) (n : Nat) :
    firstFrom good h n = if _hg : good n = true then n
      else firstFrom good h (n+1) := by
  unfold firstFrom
  rw [WellFounded.fix_eq]

theorem firstFrom_spec (good : Nat → Bool)
    (h : ∃ N, ∀ n, N ≤ n → good n = true) (n : Nat) :
    n ≤ firstFrom good h n ∧ good (firstFrom good h n) = true := by
  induction n using (wellFounded good h).induction with
  | h n ih =>
      rw [firstFrom_eq]
      split
      · exact ⟨Nat.le_refl _, ‹_›⟩
      · have hf : good n = false := by cases hh : good n <;> simp_all
        have hh := ih (n+1) ⟨rfl, hf⟩
        exact ⟨by omega, hh.2⟩

def adequate (z : ComplexRaw) (eps : QPos) (n : Nat) : Bool :=
  decide ((z.compute n).width ≤ eps.val ∧ (z.compute n).height ≤ eps.val)

theorem eventually_adequate (z : ComplexRaw) (hz : z.Valid) (eps : QPos) :
    ∃ N, ∀ n, N ≤ n → adequate z eps n = true := by
  obtain ⟨N, hN⟩ := hz.2.2 eps
  exact ⟨N, fun n hn => by simpa [adequate] using hN n hn⟩

def stage (z : ComplexRaw) (hz : z.Valid) (eps : QPos) : Nat :=
  firstFrom (adequate z eps) (eventually_adequate z hz eps) 0

theorem stage_spec (z : ComplexRaw) (hz : z.Valid) (eps : QPos) :
    (z.compute (stage z hz eps)).width ≤ eps.val ∧
      (z.compute (stage z hz eps)).height ≤ eps.val := by
  have h := (firstFrom_spec (adequate z eps) (eventually_adequate z hz eps) 0).2
  simpa [adequate, stage] using h

end ComputableAnalysis.RiemannHilbert.PrecisionSearch
