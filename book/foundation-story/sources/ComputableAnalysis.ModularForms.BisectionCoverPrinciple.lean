import ComputableAnalysis.ModularForms.RationalBisection

/-! The finite-cover implication behind rational bisection. No ambient real
completion is used. The path condition must be established from the actual
local neighborhoods before this theorem can remove a mesh hypothesis. -/
namespace ComputableAnalysis.ModularForms

noncomputable def badBisectionInterval (good : QInterval → Prop)
    (I : QInterval) : Nat → QInterval := by
  classical
  exact fun n => Nat.rec I (fun _ J =>
    bisectInterval J (decide (good (bisectInterval J false)))) n

theorem bisection_cover_principle (good : QInterval → Prop) (I : QInterval)
    (join : ∀ J, good (bisectInterval J false) →
      good (bisectInterval J true) → good J)
    (paths : ∀ choice : Nat → Bool, ∃ n, good (bisectionInterval I choice n)) :
    good I := by
  classical
  apply Classical.byContradiction
  intro hbad
  let choice : Nat → Bool := fun n =>
    decide (good (bisectInterval (badBisectionInterval good I n) false))
  have he : ∀ n, bisectionInterval I choice n = badBisectionInterval good I n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change bisectInterval (bisectionInterval I choice n) (choice n) = _
      rw [ih]
      rfl
  have hb : ∀ n, ¬good (badBisectionInterval good I n) := by
    intro n
    induction n with
    | zero => exact hbad
    | succ n ih =>
      change ¬good (bisectInterval (badBisectionInterval good I n)
        (decide (good (bisectInterval (badBisectionInterval good I n) false))))
      by_cases hl : good (bisectInterval (badBisectionInterval good I n) false)
      · simp only [hl, decide_true]
        intro hr
        exact ih (join _ hl hr)
      · simpa only [hl, decide_false] using hl
  obtain ⟨n,hn⟩ := paths choice
  rw [he n] at hn
  exact hb n hn

/-- Every rational point of the supplied interval lies in the represented
neighborhood. The definition includes irrational centers. -/
def intervalNear (J : QInterval) (x : RealRaw) (eps : QPos) : Prop :=
  ∀ q : Rat, J.lo≤q → q≤J.hi →
    RealRaw.Le (RealRaw.ofRat (q-eps.val)) x ∧
    RealRaw.Le x (RealRaw.ofRat (q+eps.val))

theorem represented_interval_cover (good : QInterval → Prop) (I : QInterval)
    (hI : I.lo≤I.hi)
    (join : ∀ J, good (bisectInterval J false) →
      good (bisectInterval J true) → good J)
    (hloc : ∀ x : RealRaw, x.Valid →
      RealRaw.Le (RealRaw.ofRat I.lo) x → RealRaw.Le x (RealRaw.ofRat I.hi) →
      ∃ eps : QPos, ∀ J, intervalNear J x eps → good J) : good I := by
  apply bisection_cover_principle good I join
  intro choice
  have he := bisectionReal_enclosed I hI choice 0
  obtain ⟨eps,hlocal⟩ := hloc (bisectionReal I choice)
    (bisectionReal_valid I hI choice) he.1 he.2
  obtain ⟨N,hN⟩ := bisectionReal_eventual_neighborhood I hI choice eps
  exact ⟨N, hlocal _ (hN N (Nat.le_refl N))⟩

end ComputableAnalysis.ModularForms
