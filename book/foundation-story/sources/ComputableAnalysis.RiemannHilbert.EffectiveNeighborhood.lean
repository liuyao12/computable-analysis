import ComputableAnalysis.RiemannHilbert.LocalSeriesFunction
import ComputableAnalysis.RiemannHilbert.PrecisionSearch

/-! Executable rational neighborhoods on the represented interior domain. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def boxCoordinateBound (B : QBox) : Rat :=
  max 0 (max (-B.lo.re) (max B.hi.re (max (-B.lo.im) B.hi.im)))

theorem boxCoordinateBound_nonneg (B : QBox) : 0 ≤ boxCoordinateBound B := by
  unfold boxCoordinateBound
  grind

theorem boxCoordinateBound_bounds (B : QBox) :
    -boxCoordinateBound B ≤ B.lo.re ∧ B.hi.re ≤ boxCoordinateBound B ∧
    -boxCoordinateBound B ≤ B.lo.im ∧ B.hi.im ≤ boxCoordinateBound B := by
  unfold boxCoordinateBound
  grind

theorem small_from_box (z : ComplexRaw) (hz : z.Valid) (n : Nat) :
    Small z (boxCoordinateBound (z.compute n)) := by
  have hb := boxCoordinateBound_bounds (z.compute n)
  have overlap : ∀ m, (z.compute n).lo.re ≤ (z.compute m).hi.re ∧
      (z.compute m).lo.re ≤ (z.compute n).hi.re ∧
      (z.compute n).lo.im ≤ (z.compute m).hi.im ∧
      (z.compute m).lo.im ≤ (z.compute n).hi.im := by
    intro m
    have hn := hz.2.1 n (max n m) (by omega)
    have hm := hz.2.1 m (max n m) (by omega)
    have ho := valid_ordered hz (max n m)
    change (z.compute (max n m)).lo.re ≤ (z.compute (max n m)).hi.re ∧
      (z.compute (max n m)).lo.im ≤ (z.compute (max n m)).hi.im at ho
    grind
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; exact Rat.le_trans hb.1 (overlap j).1
  · intro i j; exact Rat.le_trans (overlap i).2.1 hb.2.1
  · intro i j; exact Rat.le_trans hb.2.2.1 (overlap j).2.2.1
  · intro i j; exact Rat.le_trans (overlap i).2.2.2 hb.2.2.2

def boxInside (R : Rat) (z : Scalar) (n : Nat) : Bool :=
  decide (boxCoordinateBound (z.val.compute n) < R)

theorem eventually_boxInside (R : Rat) (z : Scalar) (hz : interior R z) :
    ∃ N, ∀ n, N ≤ n → boxInside R z n = true := by
  obtain ⟨r,hr,hrR,hzr⟩ := hz
  let eps : QPos := ⟨(R-r)/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩ := z.property.2.2 eps
  refine ⟨N, ?_⟩
  intro n hn
  have hw := hN n hn
  have h1 := hzr.1 n n
  have h2 := hzr.2.1 n n
  have h3 := hzr.2.2.1 n n
  have h4 := hzr.2.2.2 n n
  change -r ≤ (z.val.compute n).hi.re at h1
  change (z.val.compute n).lo.re ≤ r at h2
  change -r ≤ (z.val.compute n).hi.im at h3
  change (z.val.compute n).lo.im ≤ r at h4
  have hsmall : boxCoordinateBound (z.val.compute n) ≤ r+eps.val := by
    unfold boxCoordinateBound
    unfold QBox.width QBox.height at hw
    grind
  have hlt : r+eps.val < R := by dsimp [eps]; grind
  simp only [boxInside, decide_eq_true_eq]
  grind

def interiorStage (R : Rat) (z : Scalar) (hz : interior R z) : Nat :=
  PrecisionSearch.firstFrom (boxInside R z) (eventually_boxInside R z hz) 0

theorem interiorStage_spec (R : Rat) (z : Scalar) (hz : interior R z) :
    boxCoordinateBound (z.val.compute (interiorStage R z hz)) < R := by
  have hs := (PrecisionSearch.firstFrom_spec (boxInside R z) (eventually_boxInside R z hz) 0).2
  simpa only [boxInside, decide_eq_true_eq, interiorStage] using hs

def interiorRadius (R : Rat) (z : Scalar) (hz : interior R z) : QPos :=
  ⟨(R-boxCoordinateBound (z.val.compute (interiorStage R z hz)))/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos (by have := interiorStage_spec R z hz; grind)
      ((Rat.inv_pos).2 (by decide))⟩

theorem interiorRadius_inside (R : Rat) (a : Scalar) (ha : interior R a) (z : Scalar)
    (hz : Small (sub z.val a.val) (interiorRadius R a ha).val) : interior R z := by
  let B := boxCoordinateBound (a.val.compute (interiorStage R a ha))
  have hB : 0 ≤ B := boxCoordinateBound_nonneg _
  have haB := small_from_box a.val a.property (interiorStage R a ha)
  have hs := small_add haB hz
  have hzBound : Small z.val (B+(interiorRadius R a ha).val) := Small.congr
    (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) hs
  refine ⟨B+(interiorRadius R a ha).val,
    Rat.add_nonneg hB (Rat.le_of_lt (interiorRadius R a ha).property), ?_, hzBound⟩
  have hBR := interiorStage_spec R a ha
  change B+(R-B)/2 < R
  change B < R at hBR
  grind

end ComputableAnalysis.RiemannHilbert.LocalODE
