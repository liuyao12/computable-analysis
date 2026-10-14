import ComputableAnalysis.ComputableCoefficient

/-! Finite searches for rational accuracy of certified coefficients. -/
namespace ComputableAnalysis
namespace ComputableCoefficient

/-- Search rational interval widths. Validity proves termination; the
runtime inspects only rational endpoints. -/
def widthStageFrom (x : Real) (eps : QPos) (n : Nat) : Nat :=
  if (x.compute n).width ≤ eps.val then n else widthStageFrom x eps (n+1)
termination_by Classical.choose (x.valid.2.2 eps) - n
decreasing_by
  have h := Classical.choose_spec (x.valid.2.2 eps)
  have hn : n < Classical.choose (x.valid.2.2 eps) := by
    by_cases hn : n < Classical.choose (x.valid.2.2 eps)
    · exact hn
    · have hw := h n (by omega)
      contradiction
  omega

theorem widthStageFrom_spec (x : Real) (eps : QPos) (n : Nat) :
    n ≤ widthStageFrom x eps n ∧
      (x.compute (widthStageFrom x eps n)).width ≤ eps.val := by
  rw [widthStageFrom]
  split
  · exact ⟨Nat.le_refl _, ‹_›⟩
  · have ih := widthStageFrom_spec x eps (n+1)
    exact ⟨by omega, ih.2⟩
termination_by Classical.choose (x.valid.2.2 eps) - n
decreasing_by
  have h := Classical.choose_spec (x.valid.2.2 eps)
  have hn : n < Classical.choose (x.valid.2.2 eps) := by
    by_cases hn : n < Classical.choose (x.valid.2.2 eps)
    · exact hn
    · have hw := h n (by omega)
      contradiction
  omega

def widthStage (x : Real) (eps : QPos) : Nat := widthStageFrom x eps 0

theorem widthStage_spec (x : Real) (eps : QPos) :
    (x.compute (widthStage x eps)).width ≤ eps.val :=
  (widthStageFrom_spec x eps 0).2

end ComputableCoefficient
end ComputableAnalysis
