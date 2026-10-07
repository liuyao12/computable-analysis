import ComputableAnalysis.ModularForms.BisectionCoverPrinciple

/-! Two-coordinate rational bisection coverage with explicit represented
coordinate names, for the pending local contour grid argument. -/
namespace ComputableAnalysis.ModularForms

def bisectRectangle (J : QInterval × QInterval) (r : Bool × Bool) : QInterval × QInterval :=
  (bisectInterval J.1 r.1, bisectInterval J.2 r.2)

def rectangleBisection (J : QInterval × QInterval) (choice : Nat → Bool × Bool) :
    Nat → QInterval × QInterval
  | 0 => J
  | n+1 => bisectRectangle (rectangleBisection J choice n) (choice n)

theorem rectangleBisection_coordinates (J : QInterval × QInterval)
    (choice : Nat → Bool × Bool) (n : Nat) :
    rectangleBisection J choice n =
      (bisectionInterval J.1 (fun k => (choice k).1) n,
        bisectionInterval J.2 (fun k => (choice k).2) n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rectangleBisection,ih]; rfl

noncomputable def failingRectangleChoice (good : QInterval × QInterval → Prop)
    (J : QInterval × QInterval) : Bool × Bool := by
  classical
  exact if good (bisectRectangle J (false,false)) then
    if good (bisectRectangle J (false,true)) then
      if good (bisectRectangle J (true,false)) then (true,true) else (true,false)
    else (false,true)
  else (false,false)

theorem failingRectangleChoice_bad (good : QInterval × QInterval → Prop)
    (join : ∀ J, good (bisectRectangle J (false,false)) →
      good (bisectRectangle J (false,true)) → good (bisectRectangle J (true,false)) →
      good (bisectRectangle J (true,true)) → good J)
    (J : QInterval × QInterval) (hbad : ¬good J) :
    ¬good (bisectRectangle J (failingRectangleChoice good J)) := by
  classical
  unfold failingRectangleChoice
  split
  · split
    · split
      · intro h
        exact hbad (join J ‹_› ‹_› ‹_› h)
      · assumption
    · assumption
  · assumption

noncomputable def failingRectangle (good : QInterval × QInterval → Prop)
    (J : QInterval × QInterval) : Nat → QInterval × QInterval
  | 0 => J
  | n+1 => bisectRectangle (failingRectangle good J n)
      (failingRectangleChoice good (failingRectangle good J n))

theorem rectangle_bisection_cover (good : QInterval × QInterval → Prop)
    (J : QInterval × QInterval)
    (join : ∀ K, good (bisectRectangle K (false,false)) →
      good (bisectRectangle K (false,true)) → good (bisectRectangle K (true,false)) →
      good (bisectRectangle K (true,true)) → good K)
    (paths : ∀ choice : Nat → Bool × Bool, ∃ n, good (rectangleBisection J choice n)) :
    good J := by
  classical
  apply Classical.byContradiction
  intro hbad
  let choice := fun n => failingRectangleChoice good (failingRectangle good J n)
  have he : ∀ n, rectangleBisection J choice n=failingRectangle good J n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [rectangleBisection,ih]; rfl
  have hb : ∀ n, ¬good (failingRectangle good J n) := by
    intro n
    induction n with
    | zero => exact hbad
    | succ n ih => exact failingRectangleChoice_bad good join _ ih
  obtain ⟨n,hn⟩ := paths choice
  rw [he n] at hn
  exact hb n hn

theorem represented_rectangle_cover (good : QInterval × QInterval → Prop)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (join : ∀ K, good (bisectRectangle K (false,false)) →
      good (bisectRectangle K (false,true)) → good (bisectRectangle K (true,false)) →
      good (bisectRectangle K (true,true)) → good K)
    (hloc : ∀ x y : RealRaw, x.Valid → y.Valid →
      RealRaw.Le (RealRaw.ofRat J.1.lo) x → RealRaw.Le x (RealRaw.ofRat J.1.hi) →
      RealRaw.Le (RealRaw.ofRat J.2.lo) y → RealRaw.Le y (RealRaw.ofRat J.2.hi) →
      ∃ eps : QPos, ∀ K : QInterval × QInterval,
        intervalNear K.1 x eps → intervalNear K.2 y eps → good K) : good J := by
  apply rectangle_bisection_cover good J join
  intro choice
  let cx := fun k => (choice k).1
  let cy := fun k => (choice k).2
  have hx := bisectionReal_enclosed J.1 hX cx 0
  have hy := bisectionReal_enclosed J.2 hY cy 0
  obtain ⟨eps,heps⟩ := hloc (bisectionReal J.1 cx) (bisectionReal J.2 cy)
    (bisectionReal_valid J.1 hX cx) (bisectionReal_valid J.2 hY cy)
    hx.1 hx.2 hy.1 hy.2
  obtain ⟨X,hNX⟩ := bisectionReal_eventual_neighborhood J.1 hX cx eps
  obtain ⟨Y,hNY⟩ := bisectionReal_eventual_neighborhood J.2 hY cy eps
  refine ⟨max X Y, ?_⟩
  rw [rectangleBisection_coordinates]
  exact heps _ (hNX _ (Nat.le_max_left _ _)) (hNY _ (Nat.le_max_right _ _))

end ComputableAnalysis.ModularForms
