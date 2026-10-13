import ComputableAnalysis.PositiveSquareRootDerivative
import ComputableAnalysis.MonotoneIntegralBounds

/-! Rational-input square root: concrete secant derivative and FTC on every
positive rational chart. Existing root and derivative evaluators are retained
and compared with the new secant computation. -/
namespace ComputableAnalysis.SqrtSecantFoundation
open PositiveSquareRootDerivative SecantFoundation
set_option maxHeartbeats 2000000

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs : Nat) : Rat) + 1) := by
      exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
    exact Rat.le_trans hqnonpos hzero

theorem root_mono (C : PositiveTimeChart) (x y : Rat)
    (hx : inDomainInterval C.lower C.upper x)
    (hy : inDomainInterval C.lower C.upper y) (hxy : x≤y) :
    (rootAt C x hx).Le (rootAt C y hy) := by
  intro n m
  have hsx := sqrtRaw_stage_spec x (sqrtDomainAt C x hx) n
  have hsy := sqrtRaw_stage_spec y (sqrtDomainAt C y hy) m
  exact hsy.le_hi_of_sq_le (Rat.le_trans hsx.2.2.1 hxy)

theorem derivative_antitone (C : PositiveTimeChart) (x y : Rat)
    (hx : inDomainInterval C.lower C.upper x)
    (hy : inDomainInterval C.lower C.upper y) (hxy : x≤y) :
    (derivativeAt C y hy).Le (derivativeAt C x hx) := by
  intro n m
  have hroot := root_mono C x y hx hy hxy m n
  have hmargin := rootLower_le_rootAt_hi C y hy n
  have hlo : maxRat2 ((rootAt C x hx).compute m).lo (rootLower C) ≤
      ((rootAt C y hy).compute n).hi := by unfold maxRat2; split <;> grind
  have hp : 0 < maxRat2 ((rootAt C x hx).compute m).lo (rootLower C) := by
    have hl := rootLower_pos C
    unfold maxRat2; split <;> grind
  have hi := RealRaw.one_div_antitone_of_pos hp hlo
  have hs := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤1/2)
  change (RealRaw.scaleRatCompute (1/2) (RealRaw.positiveReciprocal (rootAt C y hy) (rootLower C)) n).lo ≤
    (RealRaw.scaleRatCompute (1/2) (RealRaw.positiveReciprocal (rootAt C x hx) (rootLower C)) m).hi
  simp only [RealRaw.scaleRatCompute,if_pos (by decide +kernel : (0:Rat)≤1/2),
    RealRaw.positiveReciprocal_compute _ _ (rootLower_pos C)]
  exact hs

def bound (C : PositiveTimeChart) : Rat := (1/2)/rootLower C

theorem derivative_bounds (C : PositiveTimeChart) (x : Rat)
    (hx : inDomainInterval C.lower C.upper x) (n : Nat) :
    0 ≤ ((derivativeAt C x hx).compute n).lo ∧
      ((derivativeAt C x hx).compute n).hi ≤ bound C := by
  have hm := rootLower_le_rootAt_hi C x hx n
  have hp : 0 < ((rootAt C x hx).compute n).hi := by have h := rootLower_pos C; grind
  have hb := RealRaw.positiveReciprocal_compute_hi_le (rootAt C x hx) (rootLower C) (rootLower_pos C) n
  change 0 ≤ (RealRaw.scaleRatCompute (1/2) (RealRaw.positiveReciprocal (rootAt C x hx) (rootLower C)) n).lo ∧ _
  simp only [RealRaw.scaleRatCompute,if_pos (by decide +kernel : (0:Rat)≤1/2)]
  constructor
  · rw [RealRaw.positiveReciprocal_compute _ _ (rootLower_pos C)]
    simp only [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  · have h := Rat.mul_le_mul_of_nonneg_left hb (by decide +kernel : (0:Rat)≤1/2)
    change (RealRaw.scaleRatCompute (1/2) (RealRaw.positiveReciprocal (rootAt C x hx) (rootLower C)) n).hi ≤ bound C
    simp only [RealRaw.scaleRatCompute,if_pos (by decide +kernel : (0:Rat)≤1/2)]
    simpa only [bound,Rat.div_def,Rat.one_mul] using h

def derivativeWidthStage (C : PositiveTimeChart) (x : Rat) (eps : QPos) : Nat :=
  rootWidthStage x ⟨2*rootLower C*rootLower C*eps.val,by
    exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (rootLower_pos C)) (rootLower_pos C)) eps.property⟩

theorem derivative_width (C : PositiveTimeChart) (x : Rat)
    (hx : inDomainInterval C.lower C.upper x) (eps : QPos) :
    ((derivativeAt C x hx).compute (derivativeWidthStage C x eps)).width ≤ eps.val := by
  have hw := rootAt_width_le_of_rootWidthStage_le C x hx
    ⟨2*rootLower C*rootLower C*eps.val,by
      exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (rootLower_pos C)) (rootLower_pos C)) eps.property⟩
    (Nat.le_refl (derivativeWidthStage C x eps))
  have hi := RealRaw.positiveReciprocal_compute_width_le (rootAt C x hx) (rootLower C)
    (rootAt_valid C x hx) (rootLower_pos C) (rootLower_le_rootAt_hi C x hx)
    (derivativeWidthStage C x eps)
  have hl2 := Rat.mul_pos (rootLower_pos C) (rootLower_pos C)
  have hc := Rat.mul_inv_cancel (rootLower C*rootLower C) (Rat.ne_of_gt hl2)
  have hm := Rat.mul_le_mul_of_nonneg_right hw (Rat.le_of_lt (Rat.inv_pos.mpr hl2))
  change (QInterval.scaleRat (1/2) ((RealRaw.positiveReciprocal (rootAt C x hx) (rootLower C)).compute _)).width ≤ _
  rw [QInterval.scaleRat_width_of_nonneg (by decide +kernel : (0:Rat)≤1/2)]
  have hs := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤1/2)
  dsimp only at hw hm
  grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

theorem step_pos (C : PositiveTimeChart) (n : Nat) : 0 < (hasDerivativeOnInterval C).stepPrecision n :=
  Nat.pow_pos (by decide)

/-- Padding is computed from source square-root boxes, not from the closed
derivative formula. -/
def padding (C : PositiveTimeChart) (x : Rat)
    (hx : inDomainInterval C.lower C.upper x) (n : Nat) : Rat :=
  ((rootAt C x hx).compute n).width/(2*rootLower C*rootLower C)

def derivative (C : PositiveTimeChart) (x radius : Rat)
    (hx : inDomainInterval C.lower C.upper x) : RealRaw :=
  SecantFoundation.derivative (hasDerivativeOnInterval C) x radius (padding C x hx)

theorem padding_bounds (C : PositiveTimeChart) (x : Rat)
    (hx : inDomainInterval C.lower C.upper x) (n : Nat) :
    ((derivativeAt C x hx).compute n).width ≤ padding C x hx n := by
  have hi := RealRaw.positiveReciprocal_compute_width_le (rootAt C x hx) (rootLower C)
    (rootAt_valid C x hx) (rootLower_pos C) (rootLower_le_rootAt_hi C x hx) n
  change (QInterval.scaleRat (1/2) ((RealRaw.positiveReciprocal (rootAt C x hx) (rootLower C)).compute n)).width ≤ _
  rw [QInterval.scaleRat_width_of_nonneg (by decide +kernel : (0:Rat)≤1/2)]
  have hs := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤1/2)
  have hl2 := Rat.mul_pos (rootLower_pos C) (rootLower_pos C)
  have hc := Rat.mul_inv_cancel (rootLower C*rootLower C) (Rat.ne_of_gt hl2)
  have hc2 := Rat.mul_inv_cancel (2*rootLower C*rootLower C) (by have := rootLower_pos C; grind : 2*rootLower C*rootLower C≠0)
  have heq : (1/2)*(((rootAt C x hx).compute n).width/(rootLower C*rootLower C)) = padding C x hx n := by
    unfold padding
    apply Rat.le_antisymm <;> apply Rat.le_of_mul_le_mul_right
      (c:=2*rootLower C*rootLower C) _ (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (rootLower_pos C)) (rootLower_pos C))
    all_goals simp only [Rat.div_def]; grind [Rat.mul_assoc,Rat.mul_comm]
  rw [heq] at hs
  exact hs

theorem padding_shrinks (C : PositiveTimeChart) (x : Rat)
    (hx : inDomainInterval C.lower C.upper x) : ShrinksToZero (padding C x hx) := by
  intro eps
  let e : QPos := ⟨2*rootLower C*rootLower C*eps.val,by
    exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (rootLower_pos C)) (rootLower_pos C)) eps.property⟩
  obtain ⟨N,hN⟩ := (rootAt_valid C x hx).2.2 e
  refine ⟨N,fun n hn => ?_⟩
  have h := hN n hn
  unfold padding
  apply Rat.le_of_mul_le_mul_right (c:=2*rootLower C*rootLower C) _
    (Rat.mul_pos (Rat.mul_pos (by decide +kernel) (rootLower_pos C)) (rootLower_pos C))
  rw [Rat.div_mul_cancel (by have := rootLower_pos C; grind : 2*rootLower C*rootLower C≠0)]
  dsimp [e] at h
  grind

theorem derivative_valid_and_equiv (C : PositiveTimeChart) (x radius : Rat)
    (hx : inDomainInterval C.lower C.upper x) (hr : 0<radius) (hr1 : radius≤1)
    (hl : C.lower≤x-radius) (hu : x+radius≤C.upper) :
    (derivative C x radius hx).Valid ∧
      (derivative C x radius hx).Equiv (derivativeAt C x hx) := by
  have h := SecantFoundation.derivative_valid_and_equiv (hasDerivativeOnInterval C)
    (step_pos C) x radius hr hr1 hx hl hu (padding C x hx)
    (fun n => by rw [SecantFoundation.value_compute (derivativeOn C) x hx]; exact padding_bounds C x hx n)
    (padding_shrinks C x hx)
  refine ⟨h.1,?_⟩
  intro n
  have hh := h.2 n
  unfold RealRaw.compareAt at hh ⊢
  rw [SecantFoundation.value_compute (derivativeOn C) x hx] at hh
  exact hh

theorem cellBounds (C : PositiveTimeChart) :
    Integral.CellDerivativeBounds (derivativeOn C) (SecantFoundation.value (rootOn C)) := by
  apply SecantFoundation.cellDerivativeBounds (hasDerivativeOnInterval C) (step_pos C) (bound C)
  intro x hx n
  have h := derivative_bounds C x hx n
  have hp : 0≤bound C := by
    unfold bound; rw [Rat.div_def]; exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr (rootLower_pos C)))
  change -(bound C)≤((derivativeAt C x hx).compute n).lo ∧ ((derivativeAt C x hx).compute n).hi≤bound C
  constructor <;> grind

theorem tight (C : PositiveTimeChart) : Integral.HasTightBounds (derivativeOn C) := by
  apply MonotoneIntegralBounds.tight (derivativeOn C) C.ordered
    (fun x y hx hy hxy => ?_) (bound C) (by
      unfold bound; rw [Rat.div_def]; exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr (rootLower_pos C))))
    (fun x hx n => ?_) (derivativeWidthStage C) (fun x hx eps => ?_)
  · intro n m
    rw [SecantFoundation.value_compute (derivativeOn C) y hy,
      SecantFoundation.value_compute (derivativeOn C) x hx]
    exact derivative_antitone C x y hx hy hxy n m
  · rw [SecantFoundation.value_compute (derivativeOn C) x hx]
    exact derivative_bounds C x hx n
  · rw [SecantFoundation.value_compute (derivativeOn C) x hx]
    exact derivative_width C x hx eps

theorem hasIntegral (C : PositiveTimeChart) : Integral.HasIntegral (derivativeOn C)
    (SecantFoundation.value (rootOn C) C.upper-SecantFoundation.value (rootOn C) C.lower) :=
  (cellBounds C).hasIntegral C.ordered (tight C)

theorem ftc (C : PositiveTimeChart) {I : RealRaw}
    (hI : Integral.HasIntegral (derivativeOn C) I) :
    I.Equiv (SecantFoundation.value (rootOn C) C.upper-SecantFoundation.value (rootOn C) C.lower) :=
  hI.ftc (cellBounds C)

def chart (a b : Rat) (ha : 0<a) (hab : a≤b) : PositiveTimeChart where
  lower := a
  upper := b
  ordered := hab
  bound := b.num.natAbs+1
  upper_le_bound := by simpa using rat_le_num_natAbs_succ b
  margin := if a≤2 then a/2 else 1
  margin_pos := by
    split
    · rw [Rat.div_def]; exact Rat.mul_pos ha (by decide +kernel)
    · decide +kernel
  margin_sq_le_lower := by
    split
    · next h =>
      have hm := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
      change (a/2)*(a/2)≤a
      grind [Rat.div_def]
    · next h => change (1:Rat)*1≤a; grind

/-- The chart and its positive margin are constructed from the endpoints. -/
theorem positive_segment_hasIntegral (a b : Rat) (ha : 0<a) (hab : a≤b) :
    Integral.HasIntegral (derivativeOn (chart a b ha hab))
      (SecantFoundation.value (rootOn (chart a b ha hab)) b-
        SecantFoundation.value (rootOn (chart a b ha hab)) a) :=
  hasIntegral (chart a b ha hab)

end ComputableAnalysis.SqrtSecantFoundation
