import ComputableAnalysis.RepresentedPositiveSquareRoot

/-!
# The inverse-square scale of represented positive time

For a represented time input uniformly separated from zero, this module
constructs the represented scale

`q = 1 / (2 * sqrt t)`.

The implementation is entirely finite: positive square-root bisection,
uniform reboxing away from zero, represented reciprocal stabilization, and
rational scaling by `1/2`.  The construction is valid and independent of the
chosen representative.  Evaluation of the Gaussian at this represented
scale is a later composition layer.
-/

namespace ComputableAnalysis
namespace RepresentedInverseSquareTime

open RepresentedPositiveSquareRoot

/-- Complex-axis implementation of `1/(2*sqrt t)`.  The intermediate complex
representation lets us reuse the certified away-from-zero reciprocal lift. -/
def scaleComplex {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw :=
  ComplexRaw.scaleRat (1 / 2) A.awayInput.reciprocal

/-- Real represented inverse-square scale `q = 1/(2*sqrt t)`. -/
def scale {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  (scaleComplex A).realPart

theorem scaleComplex_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (scaleComplex A).Valid := by
  apply ComplexRaw.scaleRat_valid_of_nonneg (by native_decide : (0 : Rat) <= 1 / 2)
  exact A.awayInput.reciprocal_valid

theorem scale_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (scale A).Valid :=
  ComplexRaw.realPart_valid (scaleComplex_valid A)

/-- A representation-independent rational bound for the inverse-square
scale.  It is intentionally generous: the reciprocal lift already proves
this bound for the unscaled reciprocal, and multiplication by `1/2` can only
decrease it. -/
def scaleBound (bound : Nat) (margin : Rat) : Rat :=
  ComplexReciprocalLift.AwayInput.inverseBound
    (PositiveInput.rootBound bound)
    (PositiveInput.awayRootMargin margin)

theorem scaleBound_nonneg {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : 0 <= scaleBound bound margin := by
  unfold scaleBound ComplexReciprocalLift.AwayInput.inverseBound
  exact Rat.mul_nonneg (Rat.le_of_lt (PositiveInput.rootBound_pos bound))
    (Rat.le_of_lt ((Rat.inv_pos).2
      (PositiveInput.awayRootMargin_pos A.margin_pos)))

theorem scaleBound_pos {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : 0 < scaleBound bound margin := by
  unfold scaleBound ComplexReciprocalLift.AwayInput.inverseBound
  exact Rat.mul_pos (PositiveInput.rootBound_pos bound)
    ((Rat.inv_pos).2 (PositiveInput.awayRootMargin_pos A.margin_pos))

/-- Nonnegative real-axis guard used to give every equivalent time input the
same explicit scale bound. -/
def scaleGuard (bound : Nat) (margin : Rat) : QInterval :=
  { lo := 0, hi := scaleBound bound margin }

/-- The inverse-square scale reboxed into a common rational interval.  This
is the preferred input to represented power-series evaluation because its
bound depends only on the public positive-time parameters, not on a raw
representative's stage-zero width. -/
def guardedScaleComplex {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw where
  compute := fun n => QBox.intersection
    ((scaleComplex A).compute n)
    (QBox.ofRealInterval (scaleGuard bound margin))

def guardedScale {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  (guardedScaleComplex A).realPart

private theorem scaleCandidate_nested_scaleComplex
    {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    (QBox.point (QComplex.scaleRat (1 / 2)
      (QComplex.inverse
        ((PositiveInput.awayRootRaw A).compute n).center))).NestedIn
      ((scaleComplex A).compute n) := by
  have hcandidate :=
    ComplexReciprocalLift.AwayInput.reciprocal_contains_current_candidate
      A.awayInput n
  have hscaled := QBox.scaleRat_contains (r := (1 / 2 : Rat))
    hcandidate.1 hcandidate.2
  exact hscaled

private theorem scaleCandidate_nested_guard
    {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    (QBox.point (QComplex.scaleRat (1 / 2)
      (QComplex.inverse
        ((PositiveInput.awayRootRaw A).compute n).center))).NestedIn
      (QBox.ofRealInterval (scaleGuard bound margin)) := by
  let z := ((PositiveInput.awayRootRaw A).compute n).center
  let w := QComplex.scaleRat (1 / 2) (QComplex.inverse z)
  have hinv := QComplex.inverse_normBound_le
    A.awayInput.bound_nonneg A.awayInput.margin_pos
    (A.awayInput.center_normBound n) (A.awayInput.center_normSq_ge n)
  have hB0 := scaleBound_nonneg A
  have hhalf0 : 0 <= (1 / 2 : Rat) := by native_decide
  have hhalf1 : (1 / 2 : Rat) <= 1 := by native_decide
  change QComplex.normBound (QComplex.inverse
      ((PositiveInput.awayRootRaw A).compute n).center) <=
    PositiveInput.rootBound bound *
      (PositiveInput.awayRootMargin margin)⁻¹ at hinv
  have hinv' : QComplex.normBound (QComplex.inverse z) <=
      scaleBound bound margin := by
    simpa [z, scaleBound,
      ComplexReciprocalLift.AwayInput.inverseBound] using hinv
  have hw : QComplex.normBound w <= scaleBound bound margin := by
    rw [show QComplex.normBound w =
        qabs (1 / 2 : Rat) * QComplex.normBound (QComplex.inverse z) by
      exact QComplex.normBound_scaleRat _ _]
    rw [qabs_eq_self_of_nonneg hhalf0]
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hinv' hhalf0)
      (by simpa using Rat.mul_le_mul_of_nonneg_right hhalf1 hB0)
  have him : w.im = 0 := by
    have hz := PositiveInput.awayRootRaw_center_bounds A n
    dsimp [w, z]
    unfold QComplex.scaleRat QComplex.inverse
    rw [hz.2.2]
    grind [Rat.div_def]
  have hre : qabs w.re <= scaleBound bound margin := by
    have himabs : qabs w.im = 0 := by rw [him]; native_decide
    unfold QComplex.normBound at hw
    rw [himabs, Rat.add_zero] at hw
    exact hw
  have hupper : w.re <= scaleBound bound margin :=
    Rat.le_trans (self_le_qabs w.re) hre
  have hnonneg : 0 <= w.re := by
    have hz := PositiveInput.awayRootRaw_center_bounds A n
    have hhalfpos : (0 : Rat) < 1 / 2 := by native_decide
    have hrePos : 0 < z.re := by
      have hmarginHalf : 0 < margin / 2 := by
        rw [Rat.div_def]
        exact Rat.mul_pos A.margin_pos
          ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))
      grind
    have hnormPos : 0 < QComplex.normSq z := by
      dsimp [z]
      unfold QComplex.normSq
      rw [hz.2.2]
      have hsquare := Rat.mul_pos hrePos hrePos
      grind
    dsimp [w]
    unfold QComplex.scaleRat QComplex.inverse
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos hhalfpos
      (Rat.mul_pos hrePos ((Rat.inv_pos).2 hnormPos)))
  unfold QBox.point QBox.ofRealInterval QBox.NestedIn scaleGuard
  simp only [QComplex.le_def]
  exact ⟨⟨hnonneg, by change 0 <= w.im; rw [him]; exact Rat.le_refl⟩,
    ⟨hupper, by change w.im <= 0; rw [him]; exact Rat.le_refl⟩⟩

theorem guardedScaleComplex_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (guardedScaleComplex A).Valid := by
  have hsource := scaleComplex_valid A
  have hcommon : forall n,
      (QBox.point (QComplex.scaleRat (1 / 2)
        (QComplex.inverse
          ((PositiveInput.awayRootRaw A).compute n).center))).NestedIn
        ((guardedScaleComplex A).compute n) := by
    intro n
    unfold guardedScaleComplex
    exact QBox.intersection_contains
      (scaleCandidate_nested_scaleComplex A n)
      (scaleCandidate_nested_guard A n)
  constructor
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1
      (QBox.ordered_of_nested (QComplex.le_refl _) (hcommon n))
  · constructor
    · intro n m hnm
      have hnested : ((guardedScaleComplex A).compute m).NestedIn
          ((guardedScaleComplex A).compute n) := by
        unfold guardedScaleComplex
        apply QBox.intersection_contains
        · apply QBox.nested_trans
          · exact QBox.intersection_contained_left _ _
          · exact ComplexRaw.valid_nestedIn hsource hnm
        · exact QBox.intersection_contained_right _ _
      exact ⟨hnested.1.1, hnested.2.1, hnested.1.2, hnested.2.2⟩
    · intro eps
      obtain ⟨N, hN⟩ := hsource.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hcontained := QBox.intersection_contained_left
        ((scaleComplex A).compute n)
        (QBox.ofRealInterval (scaleGuard bound margin))
      have hwh := QBox.width_height_le_of_nested hcontained
      exact ⟨Rat.le_trans hwh.1 (hN n hn).1,
        Rat.le_trans hwh.2 (hN n hn).2⟩

theorem guardedScale_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (guardedScale A).Valid :=
  ComplexRaw.realPart_valid (guardedScaleComplex_valid A)

theorem guardedScaleComplex_center_normBound
    {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    QComplex.normBound ((guardedScaleComplex A).compute n).center <=
      scaleBound bound margin := by
  have hordered := ComplexRaw.valid_ordered (guardedScaleComplex_valid A) n
  have hcenter := QBox.center_mem hordered
  have hguard := QBox.intersection_contained_right
    ((scaleComplex A).compute n)
    (QBox.ofRealInterval (scaleGuard bound margin))
  have hcenterGuard :
      (QBox.ofRealInterval (scaleGuard bound margin)).lo <=
          ((guardedScaleComplex A).compute n).center /\
        ((guardedScaleComplex A).compute n).center <=
          (QBox.ofRealInterval (scaleGuard bound margin)).hi :=
    ⟨QComplex.le_trans hguard.1 hcenter.1,
      QComplex.le_trans hcenter.2 hguard.2⟩
  unfold QBox.ofRealInterval scaleGuard at hcenterGuard
  simp only [QComplex.le_def] at hcenterGuard
  have him : ((guardedScaleComplex A).compute n).center.im = 0 :=
    Rat.le_antisymm hcenterGuard.2.2 hcenterGuard.1.2
  have hre : qabs ((guardedScaleComplex A).compute n).center.re <=
      scaleBound bound margin := by
    rw [qabs_eq_self_of_nonneg hcenterGuard.1.1]
    exact hcenterGuard.2.1
  unfold QComplex.normBound
  rw [him]
  change qabs ((guardedScaleComplex A).compute n).center.re + 0 <= _
  rw [Rat.add_zero]
  exact hre

theorem guardedScale_bounds {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    0 <= ((guardedScale A).compute n).lo /\
      ((guardedScale A).compute n).hi <= scaleBound bound margin := by
  have hguard := QBox.intersection_contained_right
    ((scaleComplex A).compute n)
    (QBox.ofRealInterval (scaleGuard bound margin))
  unfold guardedScale ComplexRaw.realPart
  unfold QBox.ofRealInterval scaleGuard QBox.NestedIn at hguard
  simp only [QComplex.le_def] at hguard
  exact ⟨hguard.1.1, hguard.2.1⟩

/-- The midpoint of every guarded inverse-square-scale enclosure is strictly
positive.  This is stronger than the public nonnegative guard: the enclosure
also contains the explicit positive reciprocal candidate at the same stage. -/
theorem guardedScale_midpoint_pos {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    0 < ((guardedScale A).compute n).midpoint := by
  let z := ((PositiveInput.awayRootRaw A).compute n).center
  let w := QComplex.scaleRat (1 / 2) (QComplex.inverse z)
  have hwNested : (QBox.point w).NestedIn
      ((guardedScaleComplex A).compute n) := by
    unfold guardedScaleComplex
    exact QBox.intersection_contains
      (scaleCandidate_nested_scaleComplex A n)
      (scaleCandidate_nested_guard A n)
  have hz := PositiveInput.awayRootRaw_center_bounds A n
  have hrePos : 0 < z.re := by
    have hmarginHalf : 0 < margin / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_pos A.margin_pos
        ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))
    dsimp [z]
    grind
  have hnormPos : 0 < QComplex.normSq z := by
    dsimp [z]
    unfold QComplex.normSq
    rw [hz.2.2]
    have hsquare := Rat.mul_pos hrePos hrePos
    grind
  have hwPos : 0 < w.re := by
    dsimp [w]
    unfold QComplex.scaleRat QComplex.inverse
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      (Rat.mul_pos hrePos ((Rat.inv_pos).2 hnormPos))
  have hwhi : w.re <= ((guardedScale A).compute n).hi := by
    simpa [guardedScale, ComplexRaw.realPart, QBox.point, w] using
      hwNested.2.1
  have hlo := (guardedScale_bounds A n).1
  have hhi : 0 < ((guardedScale A).compute n).hi := by grind
  unfold QInterval.midpoint
  rw [Rat.div_def]
  exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by native_decide))

/-- The guarded scale as a bounded represented input for the complex Taylor
exponential lift. -/
def boundedScaleInput {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    ComplexExponentialLift.BoundedInput (scaleBound bound margin) where
  raw := guardedScaleComplex A
  valid := guardedScaleComplex_valid A
  radius_nonneg := scaleBound_nonneg A
  center_normBound := guardedScaleComplex_center_normBound A

theorem guardedScaleComplex_equiv_scaleComplex
    {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (guardedScaleComplex A).Equiv (scaleComplex A) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    (guardedScaleComplex A) (scaleComplex A) n n).2
  have hleft := ComplexRaw.valid_ordered (guardedScaleComplex_valid A) n
  have hnested := QBox.intersection_contained_left
    ((scaleComplex A).compute n)
    (QBox.ofRealInterval (scaleGuard bound margin))
  exact ⟨QComplex.le_trans hleft hnested.2,
    QComplex.le_trans hnested.1 hleft⟩

/-- Uniform positive reboxing of square roots respects equivalent represented
time inputs. -/
theorem awayRootRaw_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (PositiveInput.awayRootRaw A).Equiv
      (PositiveInput.awayRootRaw B) := by
  have hsqrt : (PositiveInput.sqrtComplex A).Equiv
      (PositiveInput.sqrtComplex B) :=
    PositiveInput.sqrtComplex_equiv_of_input_equiv A B hAB
  have hright : (PositiveInput.sqrtComplex A).Equiv
      (PositiveInput.awayRootRaw B) :=
    ComplexRaw.equiv_trans
      (PositiveInput.sqrtComplex_valid A)
      (PositiveInput.sqrtComplex_valid B)
      (PositiveInput.awayRootRaw_valid B)
      hsqrt (ComplexRaw.equiv_symm
        (PositiveInput.awayRootRaw_equiv_sqrtComplex B))
  exact ComplexRaw.equiv_trans
    (PositiveInput.awayRootRaw_valid A)
    (PositiveInput.sqrtComplex_valid A)
    (PositiveInput.awayRootRaw_valid B)
    (PositiveInput.awayRootRaw_equiv_sqrtComplex A) hright

theorem scaleComplex_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (scaleComplex A).Equiv (scaleComplex B) := by
  have hroot := awayRootRaw_equiv_of_input_equiv A B hAB
  have hinv : A.awayInput.reciprocal.Equiv B.awayInput.reciprocal :=
    ComplexReciprocalLift.AwayInput.reciprocal_equiv_of_input_equiv
      A.awayInput B.awayInput hroot
  exact ComplexRaw.scaleRat_equiv_of_nonneg
    (by native_decide : (0 : Rat) <= 1 / 2) hinv

theorem guardedScaleComplex_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (guardedScaleComplex A).Equiv (guardedScaleComplex B) := by
  have hmiddle : (scaleComplex A).Equiv (guardedScaleComplex B) :=
    ComplexRaw.equiv_trans (scaleComplex_valid A) (scaleComplex_valid B)
      (guardedScaleComplex_valid B)
      (scaleComplex_equiv_of_input_equiv A B hAB)
      (ComplexRaw.equiv_symm (guardedScaleComplex_equiv_scaleComplex B))
  exact ComplexRaw.equiv_trans (guardedScaleComplex_valid A)
    (scaleComplex_valid A) (guardedScaleComplex_valid B)
    (guardedScaleComplex_equiv_scaleComplex A) hmiddle

/-- The direct represented scale does not depend on which valid raw name of
the positive time was supplied. -/
theorem scale_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (scale A).Equiv (scale B) := by
  exact ComplexRaw.realPart_equiv
    (scaleComplex_equiv_of_input_equiv A B hAB)

theorem guardedScale_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (guardedScale A).Equiv (guardedScale B) :=
  ComplexRaw.realPart_equiv
    (guardedScaleComplex_equiv_of_input_equiv A B hAB)

end RepresentedInverseSquareTime
end ComputableAnalysis
