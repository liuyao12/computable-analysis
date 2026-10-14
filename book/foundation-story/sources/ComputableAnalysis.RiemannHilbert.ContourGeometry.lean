import ComputableAnalysis.RiemannHilbert.ContourBisection

/-! Rational rectangle geometry and explicit finite bisection coverage. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

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
  let failingRectangleChoice (K : QInterval × QInterval) : Bool × Bool :=
    if good (bisectRectangle K (false,false)) then
      if good (bisectRectangle K (false,true)) then
        if good (bisectRectangle K (true,false)) then (true,true) else (true,false)
      else (false,true)
    else (false,false)
  have failingRectangleChoice_bad (K : QInterval × QInterval) (hk : ¬good K) :
      ¬good (bisectRectangle K (failingRectangleChoice K)) := by
    dsimp [failingRectangleChoice]
    split
    · split
      · split
        · intro h
          exact hk (join K ‹_› ‹_› ‹_› h)
        · assumption
      · assumption
    · assumption
  let failingRectangle : Nat → QInterval × QInterval := fun n =>
    Nat.rec J (fun _ K => bisectRectangle K (failingRectangleChoice K)) n
  let choice := fun n => failingRectangleChoice (failingRectangle n)
  have he : ∀ n, rectangleBisection J choice n=failingRectangle n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [rectangleBisection,ih]
  have hb : ∀ n, ¬good (failingRectangle n) := by
    intro n
    induction n with
    | zero => exact hbad
    | succ n ih => exact failingRectangleChoice_bad _ ih
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
def rationalRectangleContains (J : QInterval × QInterval) (q : QComplex) : Prop :=
  J.1.lo≤q.re ∧ q.re≤J.1.hi ∧ J.2.lo≤q.im ∧ q.im≤J.2.hi

instance rectangleContainsDecidable (J : QInterval × QInterval) (q : QComplex) :
    Decidable (rationalRectangleContains J q) :=
  inferInstanceAs (Decidable (J.1.lo≤q.re ∧ q.re≤J.1.hi ∧ J.2.lo≤q.im ∧ q.im≤J.2.hi))

theorem midpoint_mem (I : QInterval) (hI : I.lo ≤ I.hi) :
    I.lo ≤ I.midpoint ∧ I.midpoint ≤ I.hi := by
  unfold QInterval.midpoint
  grind only

def rectangleCenter (J : QInterval × QInterval) : QComplex :=
  ⟨J.1.midpoint,J.2.midpoint⟩
def rectangleHalfX (J : QInterval × QInterval) : QComplex := ⟨J.1.width/2,0⟩
def rectangleHalfY (J : QInterval × QInterval) : QComplex := ⟨0,J.2.width/2⟩
def rectangleRight (J : QInterval × QInterval) : QComplex := ⟨J.1.hi,J.2.midpoint⟩
def rectangleLeft (J : QInterval × QInterval) : QComplex := ⟨J.1.lo,J.2.midpoint⟩
def rectangleTop (J : QInterval × QInterval) : QComplex := ⟨J.1.midpoint,J.2.hi⟩
def rectangleBottom (J : QInterval × QInterval) : QComplex := ⟨J.1.midpoint,J.2.lo⟩
def rationalRectangleScalar (q : QComplex) : Scalar := ⟨ofQComplex q,ofQComplex_valid _⟩

theorem rectangleMidpoints_mem (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    rationalRectangleContains J (rectangleCenter J) ∧
    rationalRectangleContains J (rectangleRight J) ∧
    rationalRectangleContains J (rectangleLeft J) ∧
    rationalRectangleContains J (rectangleTop J) ∧
    rationalRectangleContains J (rectangleBottom J) := by
  have hx := midpoint_mem J.1 hX
  have hy := midpoint_mem J.2 hY
  unfold rationalRectangleContains rectangleCenter rectangleRight rectangleLeft rectangleTop rectangleBottom
  exact ⟨⟨hx.1,hx.2,hy.1,hy.2⟩,
    ⟨hX,Rat.le_refl,hy.1,hy.2⟩,⟨Rat.le_refl,hX,hy.1,hy.2⟩,
    ⟨hx.1,hx.2,hY,Rat.le_refl⟩,⟨hx.1,hx.2,Rat.le_refl,hY⟩⟩

theorem rectangleMidpoints_coordinates (J : QInterval × QInterval) :
    QComplex.add (rectangleCenter J) (rectangleHalfX J)=rectangleRight J ∧
    QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfX J))=rectangleLeft J ∧
    QComplex.add (rectangleCenter J) (rectangleHalfY J)=rectangleTop J ∧
    QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfY J))=rectangleBottom J := by
  simp only [rectangleCenter,rectangleHalfX,rectangleHalfY,rectangleRight,rectangleLeft,
    rectangleTop,rectangleBottom,QComplex.add,QComplex.neg,QComplex.mk.injEq,QInterval.midpoint,QInterval.width]
  grind only

theorem rationalRectangleScalar_translate (c w : QComplex) :
    (Centered.translate (rationalRectangleScalar c) (rationalRectangleScalar w)).val.Equiv
      (ofQComplex (QComplex.add c w)) := by
  have he : (Centered.translate (rationalRectangleScalar c) (rationalRectangleScalar w)).val=
      ofQComplex (QComplex.add c w) := rfl
  rw [he]
  exact equiv_refl _ (ofQComplex_valid _)

theorem rationalRectangleScalar_neg (w : QComplex) :
    (scalarNeg (rationalRectangleScalar w)).val.Equiv (ofQComplex (QComplex.neg w)) := by
  have he : (scalarNeg (rationalRectangleScalar w)).val=ofQComplex (QComplex.neg w) := rfl
  rw [he]
  exact equiv_refl _ (ofQComplex_valid _)

theorem rectangleHalfVectors_small (J : QInterval × QInterval) (H : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*H.val) (hy : J.2.width≤2*H.val) :
    Small (rationalRectangleScalar (rectangleHalfX J)).val H.val ∧
    Small (rationalRectangleScalar (rectangleHalfY J)).val H.val := by
  have hx0 : 0≤J.1.width := by unfold QInterval.width; grind only
  have hy0 : 0≤J.2.width := by unfold QInterval.width; grind only
  constructor
  · refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -H.val≤J.1.width/2; have hp := H.property; grind only
    · change J.1.width/2≤H.val; grind only
    · change -H.val≤0; have hp := H.property; grind only
    · change (0:Rat)≤H.val; exact Rat.le_of_lt H.property
  · refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -H.val≤0; have hp := H.property; grind only
    · change (0:Rat)≤H.val; exact Rat.le_of_lt H.property
    · change -H.val≤J.2.width/2; have hp := H.property; grind only
    · change J.2.width/2≤H.val; grind only

theorem rectangleMidpoints_translations (J : QInterval × QInterval) :
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (rationalRectangleScalar (rectangleHalfX J))=rationalRectangleScalar (rectangleRight J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (scalarNeg (rationalRectangleScalar (rectangleHalfX J)))=rationalRectangleScalar (rectangleLeft J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (rationalRectangleScalar (rectangleHalfY J))=rationalRectangleScalar (rectangleTop J) ∧
    Centered.translate (rationalRectangleScalar (rectangleCenter J))
      (scalarNeg (rationalRectangleScalar (rectangleHalfY J)))=rationalRectangleScalar (rectangleBottom J) := by
  have h := rectangleMidpoints_coordinates J
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (rectangleHalfX J))=ofQComplex (rectangleRight J)
    rw [h.1]
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfX J)))=ofQComplex (rectangleLeft J)
    rw [h.2.1]
  constructor
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (rectangleHalfY J))=ofQComplex (rectangleTop J)
    rw [h.2.2.1]
  · apply Subtype.ext
    change ofQComplex (QComplex.add (rectangleCenter J) (QComplex.neg (rectangleHalfY J)))=ofQComplex (rectangleBottom J)
    rw [h.2.2.2]
theorem rectangleBisection_shift (J : QInterval × QInterval)
    (choice : Nat → Bool × Bool) (n : Nat) :
    rectangleBisection J choice (n+1)=
      rectangleBisection (bisectRectangle J (choice 0)) (fun k => choice (k+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rectangleBisection,ih]; rfl

theorem rectangleBisection_contains_initial (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (choice : Nat → Bool × Bool) (n : Nat) (q : QComplex)
    (hq : rationalRectangleContains (rectangleBisection J choice n) q) :
    rationalRectangleContains J q := by
  rw [rectangleBisection_coordinates] at hq
  have hx := bisectionInterval_nested J.1 hX (fun k => (choice k).1) 0 n (Nat.zero_le n)
  have hy := bisectionInterval_nested J.2 hY (fun k => (choice k).2) 0 n (Nat.zero_le n)
  exact ⟨Rat.le_trans hx.1 hq.1,Rat.le_trans hq.2.1 hx.2.2,
    Rat.le_trans hy.1 hq.2.2.1,Rat.le_trans hq.2.2.2 hy.2.2⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
