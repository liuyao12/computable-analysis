import ComputableAnalysis.FiniteTransmutation
import ComputableAnalysis.LeibnizPi

/-! # A finite reconstruction of Leibniz's circle transmutation
For the circle `y² = 2x-x²`, its tangent intercept `t` gives
`x = 2t²/(1+t²)` and `y = 2t/(1+t²)`. Finite trapezoids implement
transmutation and complementation, with an explicit cubic cell error.
This is a modern reconstruction of the historical method, not a transcription.
-/
namespace ComputableAnalysis.LeibnizTransmutation
open RationalGeometry

/-- Horizontal coordinate, and the ordinate of the transmuted curve. -/
def X (t : Rat) : Rat := 2*t*t/(1+t*t)
def Y (t : Rat) : Rat := 2*t/(1+t*t)
def circlePoint (t : Rat) : Point := ⟨X t,Y t⟩

private theorem den_pos (t : Rat) : 0 < 1+t*t := by
  have h := rat_square_nonneg_basic t
  grind

private theorem den_cancel (t : Rat) : (1+t*t) * (1+t*t)⁻¹ = 1 :=
  Rat.mul_inv_cancel _ (Rat.ne_of_gt (den_pos t))

theorem circle_equation (t : Rat) : (X t-1)*(X t-1)+Y t*Y t = 1 := by
  have h := den_cancel t
  unfold X Y
  simp only [Rat.div_def]
  grind

/-- The radius-normal line through the circle point meets the vertical axis at `t`.
At `t=0` the tangent is vertical; this identity does not assert uniqueness of the intercept. -/
theorem tangent_intercept (t : Rat) : Y t*t = X t := by
  unfold X Y
  simp only [Rat.div_def]
  grind

/-- A supporting-line identity: the radius-normal line touches, without crossing, the circle. -/
theorem tangent_support (t s : Rat) :
    (X t-1)*(X s-X t)+Y t*(Y s-Y t) =
      -((X s-X t)*(X s-X t)+(Y s-Y t)*(Y s-Y t))/2 := by
  have ht := circle_equation t
  have hs := circle_equation s
  simp only [Rat.div_def]
  grind

theorem coordinate_complement (t : Rat) : Y t+t*X t = 2*t := by
  have h := den_cancel t
  unfold X Y
  simp only [Rat.div_def]
  grind

/-- The area discrepancy between a secant triangle and the tangent-intercept trapezoid. -/
def cellError (p r : Rat) : Rat :=
  (r-p)*(r-p)*(r-p)/(2*((1+p*p)*(1+r*r)))

def ordinateTrapezoid (p r : Rat) : Rat := trapezoid ⟨p,X p⟩ ⟨r,X r⟩
def interceptTrapezoid (p r : Rat) : Rat := trapezoid ⟨X p,p⟩ ⟨X r,r⟩

private theorem chord_moment (p r : Rat) :
    interceptMoment (circlePoint p) (circlePoint r) =
      interceptTrapezoid p r - 2*cellError p r := by
  have hp := den_cancel p
  have hr := den_cancel r
  have hd := Rat.mul_inv_cancel (2*((1+p*p)*(1+r*r)))
    (Rat.ne_of_gt (Rat.mul_pos (by decide) (Rat.mul_pos (den_pos p) (den_pos r))))
  unfold interceptMoment circlePoint interceptTrapezoid trapezoid cellError X Y
  simp only [Rat.div_def]
  grind

/-- Finite transmutation, with the exact replacement error rather than infinitesimals. -/
theorem circle_cell_transmutation (p r : Rat) :
    trapezoid (circlePoint p) (circlePoint r) =
      (X r*Y r-X p*Y p+interceptTrapezoid p r)/2-cellError p r := by
  have h := trapezoid_transmutation (circlePoint p) (circlePoint r)
  rw [chord_moment] at h
  simp only [circlePoint] at h
  simp only [circlePoint, Rat.div_def]
  grind

private theorem circle_trapezoid_sector (p r : Rat) :
    trapezoid (circlePoint p) (circlePoint r) =
      ArctanGeometry.geometricLowerStep p r +
        (X r*Y r-X p*Y p-(Y r-Y p))/2 := by
  have hp := den_cancel p
  have hr := den_cancel r
  have hd := Rat.mul_inv_cancel ((1+p*p)*(1+r*r))
    (Rat.ne_of_gt (Rat.mul_pos (den_pos p) (den_pos r)))
  unfold trapezoid circlePoint X Y ArctanGeometry.geometricLowerStep
  simp only [Rat.div_def]
  grind

/-- Transmutation followed by rectangle complementation gives the sector cell.
This theorem is obtained from the finite triangle/trapezoid identities above. -/
theorem sector_cell_transmutation (p r : Rat) :
    ArctanGeometry.geometricLowerStep p r =
      (r-p)-ordinateTrapezoid p r/2-cellError p r := by
  have ht := circle_cell_transmutation p r
  have hs := circle_trapezoid_sector p r
  have hc := trapezoid_complement (⟨p,X p⟩ : Point) ⟨r,X r⟩
  have hp := coordinate_complement p
  have hr := coordinate_complement r
  change ordinateTrapezoid p r+interceptTrapezoid p r = r*X r-p*X p at hc
  simp only [Rat.div_def] at *
  grind

/-- Lower and upper areas obtained by complementing endpoint rectangles of `X`. -/
def areaLowerStep (p r : Rat) : Rat := (r-p)*(1-X r/2)
def areaUpperStep (p r : Rat) : Rat := (r-p)*(1-X p/2)

private theorem coordinate_difference (p r : Rat) :
    (X r-X p)*((1+p*p)*(1+r*r)) = 2*(r-p)*(r+p) := by
  have hp := den_cancel p
  have hr := den_cancel r
  unfold X
  simp only [Rat.div_def]
  grind

private theorem error_product (p r : Rat) :
    cellError p r*(2*((1+p*p)*(1+r*r))) = (r-p)*(r-p)*(r-p) := by
  have h := Rat.inv_mul_cancel (2*((1+p*p)*(1+r*r)))
    (Rat.ne_of_gt (Rat.mul_pos (by decide) (Rat.mul_pos (den_pos p) (den_pos r))))
  unfold cellError
  simp only [Rat.div_def]
  grind

/-- The tangent replacement error is positive and controlled by the rectangle gap. -/
theorem cell_error_rectangle_bound {p r : Rat} (hp : 0 ≤ p) (hpr : p ≤ r) :
    0 ≤ cellError p r ∧ cellError p r ≤ (r-p)*(X r-X p)/4 := by
  have hd : 0 < 2*((1+p*p)*(1+r*r)) :=
    Rat.mul_pos (by decide) (Rat.mul_pos (den_pos p) (den_pos r))
  have hprod := error_product p r
  have hdiff := coordinate_difference p r
  have hdelta : 0 ≤ r-p := by grind
  have hsquare : 0 ≤ (r-p)*(r-p) := Rat.mul_nonneg hdelta hdelta
  have hcube := Rat.mul_nonneg hsquare hdelta
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := 2*((1+p*p)*(1+r*r))) _ hd
    grind
  · apply Rat.le_of_mul_le_mul_right (c := 2*((1+p*p)*(1+r*r))) _ hd
    have h := Rat.mul_le_mul_of_nonneg_left (show r-p ≤ r+p by grind) hsquare
    have hh := congrArg (fun z : Rat => (r-p)*z) hdiff
    simp only [Rat.div_def]
    grind

/-- The cubic error bound that makes finite transmutation converge. -/
theorem cell_error_bound {p r : Rat} (hp : 0 ≤ p) (hpr : p ≤ r) :
    0 ≤ cellError p r ∧ cellError p r ≤ (r-p)*(r-p)*(r-p)/2 := by
  have he := (cell_error_rectangle_bound hp hpr).1
  have hd : 1 ≤ (1+p*p)*(1+r*r) := by
    have hp2 := rat_square_nonneg_basic p
    have hr2 := rat_square_nonneg_basic r
    have h := Rat.mul_nonneg hp2 hr2
    grind
  have hm := Rat.mul_le_mul_of_nonneg_right hd he
  have heq := error_product p r
  constructor
  · exact he
  · simp only [Rat.div_def]
    grind

/-- The finite transmutation identities put each inscribed sector triangle
inside the complemented rectangles. No existing integral/geometry bridge is used. -/
theorem transmutation_brackets {p r : Rat} (hp : 0 ≤ p) (hpr : p ≤ r) :
    areaLowerStep p r ≤ ArctanGeometry.geometricLowerStep p r ∧
      ArctanGeometry.geometricLowerStep p r ≤ areaUpperStep p r := by
  rw [sector_cell_transmutation]
  have he := cell_error_rectangle_bound hp hpr
  unfold areaLowerStep areaUpperStep ordinateTrapezoid trapezoid
  simp only [Rat.div_def] at *
  constructor <;> grind

/-- The historical rational curve is the complement of the arctangent kernel. -/
theorem ordinate_complement (t : Rat) : 1-X t/2 = ArctanGeometry.integralKernel t := by
  have h := den_cancel t
  unfold X ArctanGeometry.integralKernel
  simp only [Rat.div_def]
  grind

private def sumCells (f : Rat → Rat → Rat) : List (Rat × Rat) → Rat
  | [] => 0
  | (p,r)::cs => f p r+sumCells f cs

private theorem sumCells_length {a b : Rat} {cs : List (Rat × Rat)}
    (h : ArctanGeometry.CoversInterval a b cs) :
    sumCells (fun p r => r-p) cs = b-a := by
  induction cs generalizing a with
  | nil => change a=b at h; simp only [sumCells]; grind
  | cons c cs ih =>
      rcases c with ⟨p,r⟩
      rcases h with ⟨rfl,hpr,ht⟩
      simp only [sumCells,ih ht]
      grind

/-- Literal rectangle computation of the area under the transmuted curve `X`. -/
def transmutedIntegralRaw : RealRaw where
  compute n :=
    let cs := (ArctanGeometry.arctanAreaLoopState 1 n).intervals
    {lo := sumCells (fun p r => (r-p)*X p) cs,
     hi := sumCells (fun p r => (r-p)*X r) cs}

/-- Half of the complement of the transmuted area, following Leibniz's rectangle dissection. -/
def areaRaw : RealRaw where
  compute n :=
    let cs := (ArctanGeometry.arctanAreaLoopState 1 n).intervals
    {lo := sumCells areaLowerStep cs, hi := sumCells areaUpperStep cs}

private theorem areaSums_eq (cs : List (Rat × Rat)) :
    sumCells areaLowerStep cs = ArctanGeometry.integralLowerSum cs ∧
    sumCells areaUpperStep cs = ArctanGeometry.integralUpperSum cs := by
  induction cs with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih =>
      rcases c with ⟨p,r⟩
      simp only [sumCells,areaLowerStep,areaUpperStep,ordinate_complement,
        ArctanGeometry.integralLowerSum,ArctanGeometry.integralUpperSum,
        ArctanGeometry.integralLowerStep,ArctanGeometry.integralUpperStep,ih.1,ih.2]
      trivial

/-- An exact implementation identity; geometry is established separately by transmutation. -/
theorem areaRaw_compute (n : Nat) :
    areaRaw.compute n = ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n := by
  have h := areaSums_eq (ArctanGeometry.arctanAreaLoopState 1 n).intervals
  change ({lo := _, hi := _} : QInterval) = {lo := _, hi := _}
  rw [h.1,h.2]

theorem areaRaw_valid : areaRaw.Valid := by
  have h : areaRaw.compute = ArctanGeometry.arctanIntegralRectangleRawAtOne.compute :=
    funext areaRaw_compute
  unfold RealRaw.Valid
  rw [h]
  exact ArctanGeometry.arctanIntegralRectangleRawAtOne_valid

private theorem sum_complement (cs : List (Rat × Rat)) :
    sumCells areaLowerStep cs = sumCells (fun p r => r-p) cs-
      sumCells (fun p r => (r-p)*X r) cs/2 ∧
    sumCells areaUpperStep cs = sumCells (fun p r => r-p) cs-
      sumCells (fun p r => (r-p)*X p) cs/2 := by
  induction cs with
  | nil => simp only [sumCells]; constructor <;> grind
  | cons c cs ih =>
      rcases c with ⟨p,r⟩
      simp only [sumCells,areaLowerStep,areaUpperStep,Rat.div_def] at *
      constructor <;> grind

/-- Exact finite form of `quarter-circle area = 1 - (transmuted area)/2`. -/
theorem areaRaw_complement (n : Nat) :
    (areaRaw.compute n).lo = 1-(transmutedIntegralRaw.compute n).hi/2 ∧
    (areaRaw.compute n).hi = 1-(transmutedIntegralRaw.compute n).lo/2 := by
  have h := sum_complement (ArctanGeometry.arctanAreaLoopState 1 n).intervals
  have hl := sumCells_length (ArctanGeometry.arctanAreaLoopState_intervals_covers
    (x := (1:Rat)) (by decide) n)
  change _=1-0 at hl
  rw [show (1:Rat)-0=1 by grind] at hl
  simpa only [areaRaw,transmutedIntegralRaw,hl] using h

private theorem areaSums_bracket (cs : List (Rat × Rat))
    (h : ArctanGeometry.NonnegativeIntervals cs) :
    sumCells areaLowerStep cs ≤ ArctanGeometry.geometricLowerSum cs ∧
    ArctanGeometry.geometricLowerSum cs ≤ sumCells areaUpperStep cs := by
  induction cs with
  | nil => simp [sumCells,ArctanGeometry.geometricLowerSum]
  | cons c cs ih =>
      rcases c with ⟨p,r⟩
      rcases h with ⟨hp,hpr,ht⟩
      have hc := transmutation_brackets hp hpr
      have hs := ih ht
      simp only [sumCells,ArctanGeometry.geometricLowerSum]
      constructor <;> grind

/-- The geometric bridge supplied by finite transmutation itself. -/
theorem areaRaw_equiv_geom : areaRaw.Equiv (ArctanGeometry.arctanGeom 1) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hb := areaSums_bracket (ArctanGeometry.arctanAreaLoopState 1 n).intervals
    (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative (by decide) n)
  have hg := ArctanGeometry.positiveLoopComputeAtStage_eq_geometricSumInterval
    (x := (1:Rat)) (by decide) n
  rw [ArctanGeometry.arctanGeom_one_compute_eq,hg]
  have ho := RealRaw.interval_order_of_valid _ ArctanGeometry.arctanGeom_one_valid n
  rw [ArctanGeometry.arctanGeom_one_compute_eq,hg] at ho
  change sumCells areaLowerStep _ ≤ _ ∧ _ ≤ sumCells areaUpperStep _
  change ArctanGeometry.geometricLowerSum _ ≤ ArctanGeometry.geometricUpperSum _ at ho
  exact ⟨Rat.le_trans hb.1 ho,hb.2⟩

private theorem transmutedIntegralRaw_compute (n : Nat) :
    transmutedIntegralRaw.compute n =
      (RealRaw.scaleRat 2 (RealRaw.ofRat 1-areaRaw)).compute n := by
  have h := areaRaw_complement n
  change ({lo := (transmutedIntegralRaw.compute n).lo, hi := (transmutedIntegralRaw.compute n).hi} : QInterval) =
    {lo := 2*(1-(areaRaw.compute n).hi),hi := 2*(1-(areaRaw.compute n).lo)}
  have hl : (transmutedIntegralRaw.compute n).lo = 2*(1-(areaRaw.compute n).hi) := by
    have hh := h.2; simp only [Rat.div_def] at hh; grind
  have hu : (transmutedIntegralRaw.compute n).hi = 2*(1-(areaRaw.compute n).lo) := by
    have hh := h.1; simp only [Rat.div_def] at hh; grind
  rw [← hl,← hu]

theorem transmutedIntegralRaw_valid : transmutedIntegralRaw.Valid := by
  have h := funext transmutedIntegralRaw_compute
  unfold RealRaw.Valid
  rw [h]
  exact RealRaw.scaleRat_valid (RealRaw.sub_valid (RealRaw.ofRat_valid 1) areaRaw_valid)

/-- The represented form of the historical transmutation/complement formula. -/
theorem circle_transmutation :
    (ArctanGeometry.arctanGeom 1).Equiv
      (RealRaw.ofRat 1-RealRaw.scaleRat ((1:Rat)/2) transmutedIntegralRaw) := by
  let rhs := RealRaw.ofRat 1-RealRaw.scaleRat ((1:Rat)/2) transmutedIntegralRaw
  have hr : rhs.Valid := RealRaw.sub_valid (RealRaw.ofRat_valid 1)
    (RealRaw.scaleRat_valid transmutedIntegralRaw_valid)
  have heq : rhs.compute = areaRaw.compute := by
    funext n
    have h := areaRaw_complement n
    change RealRaw.subCompute (RealRaw.ofRat 1) (RealRaw.scaleRat ((1:Rat)/2) transmutedIntegralRaw) n = _
    unfold RealRaw.subCompute RealRaw.scaleRat RealRaw.scaleRatCompute
    dsimp only
    rw [if_pos (show (0:Rat) ≤ 1/2 by
      simp only [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt (Rat.inv_pos.mpr (by decide)))]
    change ({lo := 1-((1:Rat)/2)*(transmutedIntegralRaw.compute n).hi,
             hi := 1-((1:Rat)/2)*(transmutedIntegralRaw.compute n).lo} : QInterval) = _
    have hl : 1-((1:Rat)/2)*(transmutedIntegralRaw.compute n).hi = (areaRaw.compute n).lo := by
      have hh := h.1; simp only [Rat.div_def] at *; grind
    have hu : 1-((1:Rat)/2)*(transmutedIntegralRaw.compute n).lo = (areaRaw.compute n).hi := by
      have hh := h.2; simp only [Rat.div_def] at *; grind
    rw [hl,hu]
  exact RealRaw.equiv_trans ArctanGeometry.arctanGeom_one_valid areaRaw_valid hr
    (RealRaw.equiv_symm areaRaw_equiv_geom)
    (RealRaw.equiv_symm (RealRaw.equiv_of_compute_eq hr heq))

/-- The literal transformed area has an explicit convergence budget. -/
theorem areaRaw_width (n : Nat) : (areaRaw.compute n).width ≤ 4/((n:Rat)+1) := by
  rw [areaRaw_compute]
  change (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).width ≤ _
  simpa using
    ArctanGeometry.arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n

theorem transmutedIntegralRaw_width (n : Nat) :
    (transmutedIntegralRaw.compute n).width ≤ 8/((n:Rat)+1) := by
  have h := areaRaw_complement n
  have hw := areaRaw_width n
  unfold QInterval.width at *
  simp only [Rat.div_def] at *
  grind

/-- The finite transformed-curve trapezoid sum, not a completed-real integral. -/
def transmutedTrapezoidSum (n : Nat) : Rat :=
  sumCells ordinateTrapezoid (ArctanGeometry.arctanAreaLoopState 1 n).intervals

def transmutationError (n : Nat) : Rat :=
  sumCells cellError (ArctanGeometry.arctanAreaLoopState 1 n).intervals

private theorem sector_sum_transmutation (cs : List (Rat × Rat)) :
    ArctanGeometry.geometricLowerSum cs = sumCells (fun p r => r-p) cs-
      sumCells ordinateTrapezoid cs/2-sumCells cellError cs := by
  induction cs with
  | nil => simp only [ArctanGeometry.geometricLowerSum,sumCells]; grind
  | cons c cs ih =>
      rcases c with ⟨p,r⟩
      simp only [ArctanGeometry.geometricLowerSum,sumCells]
      rw [sector_cell_transmutation,ih]
      simp only [Rat.div_def]
      grind

/-- An exact finite geometric transmutation identity at every dyadic stage. -/
theorem geometric_polygon_transmutation (n : Nat) :
    ((ArctanGeometry.arctanGeom 1).compute n).lo =
      1-transmutedTrapezoidSum n/2-transmutationError n := by
  rw [ArctanGeometry.arctanGeom_one_compute_eq,
    ArctanGeometry.positiveLoopComputeAtStage_eq_geometricSumInterval (by decide) n]
  have h := sector_sum_transmutation (ArctanGeometry.arctanAreaLoopState 1 n).intervals
  have hl := sumCells_length (ArctanGeometry.arctanAreaLoopState_intervals_covers
    (x := (1:Rat)) (by decide) n)
  change _ = _-0 at hl
  change ArctanGeometry.geometricLowerSum _ = _
  dsimp [transmutedTrapezoidSum,transmutationError]
  rw [h,hl]
  grind

private theorem error_sum_bound (cs : List (Rat × Rat)) (h : Rat)
    (hc : ∀ c ∈ cs, 0 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2-c.1 ≤ h) :
    0 ≤ sumCells cellError cs ∧ sumCells cellError cs ≤
      h*ArctanGeometry.intervalSquareSum cs/2 := by
  induction cs with
  | nil => simp only [sumCells,ArctanGeometry.intervalSquareSum]; constructor <;> grind
  | cons c cs ih =>
      have hh := hc c (by simp)
      have ht := ih (fun d hd => hc d (by simp [hd]))
      rcases c with ⟨p,r⟩
      have he := cell_error_bound hh.1 hh.2.1
      have hd : 0 ≤ r-p := by have := hh.2.1; grind
      have hm := Rat.mul_le_mul_of_nonneg_right hh.2.2 (Rat.mul_nonneg hd hd)
      simp only [sumCells,ArctanGeometry.intervalSquareSum,Rat.div_def] at *
      constructor <;> grind

/-- The total correction is bounded by half the square of the dyadic mesh. -/
theorem transmutation_error_bound (n : Nat) :
    0 ≤ transmutationError n ∧ transmutationError n ≤
      (1/((2^n:Nat):Rat))*(1/((2^n:Nat):Rat))/2 := by
  let h : Rat := 1/((2^n:Nat):Rat)
  have hn : 0 < ((2^n:Nat):Rat) := by exact_mod_cast Nat.two_pow_pos n
  have hi : 0 ≤ (((2^n:Nat):Rat))⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hn)
  have hc : ∀ c ∈ (ArctanGeometry.arctanAreaLoopState 1 n).intervals,
      0 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2-c.1 ≤ h := by
    rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform]
    intro c hc
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hc
    have hk0 : 0 ≤ (k:Rat) := Rat.natCast_nonneg
    have hs : ((Nat.succ k:Nat):Rat) = (k:Rat)+1 := by simp
    dsimp only
    rw [hs]
    simp only [Rat.div_def]
    dsimp [h]
    simp only [Rat.div_def,Rat.one_mul]
    have hz := Rat.mul_nonneg hk0 hi
    constructor
    · exact hz
    constructor <;> grind
  have hb := error_sum_bound (ArctanGeometry.arctanAreaLoopState 1 n).intervals h hc
  rw [ArctanGeometry.arctanAreaLoopState_one_squareSum] at hb
  exact hb

/-- Polynomial quadrature of the transformed curve, reusing the all-degree
finite power-integration lemmas. This does not invoke either previous π theorem. -/
theorem areaRaw_equiv_series : areaRaw.Equiv leibnizSeries := by
  have h := PiProofs.leibnizEqualsRectangleRawAtOne_of_cellBoundsUpToAll
    PiProofs.LeibnizRectangleBridge.leibnizRectangleKernelCellBoundsAtOneUpTo_all
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [areaRaw_compute]
  exact (RealRaw.compareAt_overlap_iff _ _ n n).1 ((RealRaw.equiv_symm h) n)

/-- Quadrature of the historical curve gives twice the complement of the odd-reciprocal series. -/
theorem transmuted_integral_series : transmutedIntegralRaw.Equiv
    (RealRaw.scaleRat 2 (RealRaw.ofRat 1-leibnizSeries)) := by
  have ha := RealRaw.sub_valid (RealRaw.ofRat_valid 1) areaRaw_valid
  have hs := RealRaw.sub_valid (RealRaw.ofRat_valid 1) PiProofs.leibnizSeriesValid
  have hc := RealRaw.sub_equiv (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 1)
    areaRaw_valid PiProofs.leibnizSeriesValid
    (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)) areaRaw_equiv_series
  exact RealRaw.equiv_trans transmutedIntegralRaw_valid
    (RealRaw.scaleRat_valid ha) (RealRaw.scaleRat_valid hs)
    (RealRaw.equiv_of_compute_eq transmutedIntegralRaw_valid (funext transmutedIntegralRaw_compute))
    (RealRaw.scaleRat_equiv (r := (2:Rat)) hc)

/-- The historical transformed rational curve has a finite polynomial expansion
and a signed remainder; the powers can be quadratured one at a time. -/
theorem transformed_curve_expansion (t : Rat) (N : Nat) :
    X t = 2*(1-Taylor.ArctanKernel.kernelPartial t N)-
      2*((-1:Rat)^(N+1)*t^(2*N+2)/(1+t*t)) := by
  have hf := Taylor.ArctanKernel.finite_geometric_identity t N
  have hx := ordinate_complement t
  unfold ArctanGeometry.integralKernel at hx
  simp only [Rat.div_def] at *
  grind

end ComputableAnalysis.LeibnizTransmutation

namespace ComputableAnalysis

/-- Leibniz's geometric transmutation method, reconstructed by finite rational areas. -/
theorem pi_eq_leibniz_transmutation : piCircleArea.Equiv leibnizRaw := by
  have hunit := RealRaw.equiv_trans PiProofs.leibnizSeriesValid
    LeibnizTransmutation.areaRaw_valid ArctanGeometry.arctanGeom_one_valid
    (RealRaw.equiv_symm LeibnizTransmutation.areaRaw_equiv_series)
    LeibnizTransmutation.areaRaw_equiv_geom
  have h := RealRaw.equiv_symm (RealRaw.natScale_equiv 4 hunit)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [leibnizRaw_compute_eq_piLeibniz,
    ← ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact (RealRaw.compareAt_overlap_iff _ _ n n).1 (h n)

end ComputableAnalysis
