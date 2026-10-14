import ComputableAnalysis.PowerSeries
import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments

/-! Rational bisection names and a proof-only finite-cover implication. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def bisectInterval (I : QInterval) (right : Bool) : QInterval :=
  if right then ⟨I.midpoint, I.hi⟩ else ⟨I.lo, I.midpoint⟩

def bisectionInterval (I : QInterval) (choice : Nat → Bool) : Nat → QInterval
  | 0 => I
  | n+1 => bisectInterval (bisectionInterval I choice n) (choice n)

theorem bisectInterval_bounds (I : QInterval) (hI : I.lo ≤ I.hi) (r : Bool) :
    I.lo ≤ (bisectInterval I r).lo ∧
    (bisectInterval I r).lo ≤ (bisectInterval I r).hi ∧
    (bisectInterval I r).hi ≤ I.hi := by
  cases r <;> simp [bisectInterval, QInterval.midpoint] <;> grind

theorem bisectInterval_width (I : QInterval) (r : Bool) :
    (bisectInterval I r).width = I.width * ((1:Rat)/2) := by
  cases r <;> simp [bisectInterval, QInterval.width, QInterval.midpoint] <;> grind

theorem bisectionInterval_ordered (I : QInterval) (hI : I.lo ≤ I.hi)
    (choice : Nat → Bool) (n : Nat) :
    (bisectionInterval I choice n).lo ≤ (bisectionInterval I choice n).hi := by
  induction n with
  | zero => exact hI
  | succ n ih => exact (bisectInterval_bounds _ ih _).2.1

theorem bisectionInterval_nested (I : QInterval) (hI : I.lo ≤ I.hi)
    (choice : Nat → Bool) (n m : Nat) (hnm : n ≤ m) :
    (bisectionInterval I choice n).lo ≤ (bisectionInterval I choice m).lo ∧
    (bisectionInterval I choice m).lo ≤ (bisectionInterval I choice m).hi ∧
    (bisectionInterval I choice m).hi ≤ (bisectionInterval I choice n).hi := by
  induction m with
  | zero =>
    have he : n=0 := by omega
    subst n
    exact ⟨Rat.le_refl, hI, Rat.le_refl⟩
  | succ m ih =>
    by_cases he : n=m+1
    · subst n
      exact ⟨Rat.le_refl, bisectionInterval_ordered I hI choice (m+1), Rat.le_refl⟩
    · have hp := ih (by omega : n≤m)
      have hs := bisectInterval_bounds (bisectionInterval I choice m)
        (bisectionInterval_ordered I hI choice m) (choice m)
      exact ⟨Rat.le_trans hp.1 hs.1, hs.2.1, Rat.le_trans hs.2.2 hp.2.2⟩

theorem bisectionInterval_width (I : QInterval) (choice : Nat → Bool) (n : Nat) :
    (bisectionInterval I choice n).width = I.width * ((1:Rat)/2)^n := by
  induction n with
  | zero => simp [bisectionInterval, Rat.pow_zero]
  | succ n ih =>
    rw [bisectionInterval, bisectInterval_width, ih, Rat.pow_succ, Rat.mul_assoc]

def bisectionReal (I : QInterval) (choice : Nat → Bool) : RealRaw :=
  ⟨bisectionInterval I choice, .unknown⟩

theorem bisectionInterval_shift (I : QInterval) (choice : Nat → Bool) (n : Nat) :
    bisectionInterval I choice (n+1) =
      bisectionInterval (bisectInterval I (choice 0)) (fun k => choice (k+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bisectInterval (bisectionInterval I choice (n+1)) (choice (n+1)) = _
    rw [ih]
    rfl

theorem bisectionReal_enclosed (I : QInterval) (hI : I.lo ≤ I.hi)
    (choice : Nat → Bool) (n : Nat) :
    RealRaw.Le (RealRaw.ofRat (bisectionInterval I choice n).lo)
      (bisectionReal I choice) ∧
    RealRaw.Le (bisectionReal I choice)
      (RealRaw.ofRat (bisectionInterval I choice n).hi) := by
  constructor <;> intro j k
  · change (bisectionInterval I choice n).lo ≤ (bisectionInterval I choice k).hi
    by_cases hn : n≤k
    · have h := bisectionInterval_nested I hI choice n k hn
      exact Rat.le_trans h.1 h.2.1
    · have h := bisectionInterval_nested I hI choice k n (by omega)
      exact Rat.le_trans h.2.1 h.2.2
  · change (bisectionInterval I choice j).lo ≤ (bisectionInterval I choice n).hi
    by_cases hn : n≤j
    · have h := bisectionInterval_nested I hI choice n j hn
      exact Rat.le_trans h.2.1 h.2.2
    · have h := bisectionInterval_nested I hI choice j n (by omega)
      exact Rat.le_trans h.1 h.2.1

theorem bisectionReal_valid (I : QInterval) (hI : I.lo ≤ I.hi)
    (choice : Nat → Bool) : (bisectionReal I choice).Valid := by
  have hw : 0 ≤ I.width := by unfold QInterval.width; grind
  refine ⟨?_, bisectionInterval_nested I hI choice, ?_⟩
  · intro n
    have ho := bisectionInterval_ordered I hI choice n
    change 0 ≤ (bisectionInterval I choice n).hi - (bisectionInterval I choice n).lo
    grind
  · intro eps
    refine ⟨RationalMajorant.natRateStage I.width eps, ?_⟩
    intro n hn
    change (bisectionInterval I choice n).width ≤ _
    rw [bisectionInterval_width]
    have hb := RationalMajorant.half_pow_le_one_div_succ n
    have hm := Rat.mul_le_mul_of_nonneg_left hb hw
    have hb' : I.width * ((1:Rat)/2)^n ≤ I.width / ((n+1:Nat):Rat) := by
      simpa only [Rat.div_def, Rat.one_mul] using hm
    exact Rat.le_trans hb' (RationalMajorant.natRateStage_spec_of_le hw eps hn)

theorem bisectionReal_eventual_neighborhood (I : QInterval) (hI : I.lo ≤ I.hi)
    (choice : Nat → Bool) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ q : Rat,
      (bisectionInterval I choice n).lo ≤ q →
      q ≤ (bisectionInterval I choice n).hi →
      RealRaw.Le (RealRaw.ofRat (q-eps.val)) (bisectionReal I choice) ∧
      RealRaw.Le (bisectionReal I choice) (RealRaw.ofRat (q+eps.val)) := by
  obtain ⟨N,hN⟩ := (bisectionReal_valid I hI choice).2.2 eps
  refine ⟨N, ?_⟩
  intro n hn q hqlo hqhi
  have hw := hN n hn
  change (bisectionInterval I choice n).hi -
    (bisectionInterval I choice n).lo ≤ eps.val at hw
  have he := bisectionReal_enclosed I hI choice n
  constructor <;> intro j k
  · have hl := he.1 0 k
    change (bisectionInterval I choice n).lo ≤
      (bisectionInterval I choice k).hi at hl
    change q-eps.val ≤ (bisectionInterval I choice k).hi
    grind only

  · have hh := he.2 j 0
    change (bisectionInterval I choice j).lo ≤
      (bisectionInterval I choice n).hi at hh
    change (bisectionInterval I choice j).lo ≤ q+eps.val
    grind only

theorem bisectionReal_stage_neighborhood (I : QInterval) (hI : I.lo≤I.hi)
    (choice : Nat → Bool) (n : Nat) (q : Rat)
    (hqlo : (bisectionInterval I choice n).lo≤q)
    (hqhi : q≤(bisectionInterval I choice n).hi) :
    RealRaw.Le (RealRaw.ofRat (q-(bisectionInterval I choice n).width)) (bisectionReal I choice) ∧
    RealRaw.Le (bisectionReal I choice) (RealRaw.ofRat (q+(bisectionInterval I choice n).width)) := by
  have he := bisectionReal_enclosed I hI choice n
  constructor <;> intro j k
  · have hl := he.1 0 k
    change (bisectionInterval I choice n).lo≤(bisectionInterval I choice k).hi at hl
    change q-(bisectionInterval I choice n).width≤(bisectionInterval I choice k).hi
    unfold QInterval.width
    grind only
  · have hh := he.2 j 0
    change (bisectionInterval I choice j).lo≤(bisectionInterval I choice n).hi at hh
    change (bisectionInterval I choice j).lo≤q+(bisectionInterval I choice n).width
    unfold QInterval.width
    grind only
theorem bisection_cover_principle (good : QInterval → Prop) (I : QInterval)
    (join : ∀ J, good (bisectInterval J false) →
      good (bisectInterval J true) → good J)
    (paths : ∀ choice : Nat → Bool, ∃ n, good (bisectionInterval I choice n)) :
    good I := by
  classical
  apply Classical.byContradiction
  intro hbad
  let badBisectionInterval : Nat → QInterval := fun n =>
    Nat.rec I (fun _ J => bisectInterval J (decide (good (bisectInterval J false)))) n
  let choice : Nat → Bool := fun n =>
    decide (good (bisectInterval (badBisectionInterval n) false))
  have he : ∀ n, bisectionInterval I choice n = badBisectionInterval n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change bisectInterval (bisectionInterval I choice n) (choice n) = _
      rw [ih]
  have hb : ∀ n, ¬good (badBisectionInterval n) := by
    intro n
    induction n with
    | zero => exact hbad
    | succ n ih =>
      change ¬good (bisectInterval (badBisectionInterval n)
        (decide (good (bisectInterval (badBisectionInterval n) false))))
      by_cases hl : good (bisectInterval (badBisectionInterval n) false)
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

end ComputableAnalysis.RiemannHilbert.RectangularContour
