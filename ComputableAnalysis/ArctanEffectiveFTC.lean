import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.Calculus

/-!
# Arctangent effective-FTC subgoals

This module isolates the first non-polynomial certificate inputs.  The
primitive is the existing rational rectangle arctangent representation; the
candidate derivative is the exact rational kernel `1 / (1 + x^2)`.  The full
local endpoint-control certificate will consume the finite tangent-chart
quotient theorems from `ArctanGeometry`.
-/

namespace ComputableAnalysis

namespace Integral

/-- An overlap can be converted into containment after paying the width of
the second interval.  This is the finite interval bridge needed when a
geometric transport theorem provides overlap, while the effective FTC local
certificate asks for containment. -/
theorem overlaps_implies_contains_width_padding
    {I A B : QInterval}
    (hIA : I.ContainsInterval A) (hAB : A.Overlaps B) :
    ({ lo := I.lo - B.width, hi := I.hi + B.width } : QInterval).ContainsInterval B := by
  unfold QInterval.ContainsInterval QInterval.Overlaps QInterval.width at *
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem overlaps_implies_contains_width_padding_left
    {I A B : QInterval}
    (hIB : I.ContainsInterval B) (hAB : A.Overlaps B) :
    ({ lo := I.lo - A.width, hi := I.hi + A.width } : QInterval).ContainsInterval A := by
  unfold QInterval.ContainsInterval QInterval.Overlaps QInterval.width at *
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem arctan_zero_tangent_quotient_ordered
    {h t : Rat} (hpos : 0 < h) (ht0 : 0 <= t) (n : Nat) :
    0 <= (QInterval.differenceQuotient
      (ArctanGeometry.arctanIntegralRectangleCompute t n)
      (ArctanGeometry.arctanIntegralRectangleCompute 0 n) h).width := by
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have htord := ArctanGeometry.arctanIntegralRectangleCompute_ordered ht0 n
  have hzeroord := ArctanGeometry.arctanIntegralRectangleCompute_ordered
    (by native_decide : (0 : Rat) <= 0) n
  unfold QInterval.width at htord hzeroord
  have hwidth :
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute t n)
        (ArctanGeometry.arctanIntegralRectangleCompute 0 n) h).width =
        (1 / h) *
          ((ArctanGeometry.arctanIntegralRectangleCompute t n).width +
        (ArctanGeometry.arctanIntegralRectangleCompute 0 n).width) := by
    rw [QInterval.differenceQuotient, QInterval.divRat,
      QInterval.scaleRat_width_of_nonneg hinv, QInterval.sub_width]
  rw [hwidth]
  exact Rat.mul_nonneg hinv (Rat.add_nonneg htord hzeroord)

def arctanForwardQuotientPaddedKernelBound (x h : Rat) (n : Nat) : QInterval :=
  let A := QInterval.scaleRat (1 / h)
    (ArctanGeometry.chartAddAreaLoopCompute x
      (ArctanGeometry.tangentChartIncrement x h) n)
  let D := QInterval.differenceQuotient
    (ArctanGeometry.arctanIntegralRectangleCompute (x + h) n)
    (ArctanGeometry.arctanIntegralRectangleCompute x n) h
  { lo := ArctanGeometry.integralKernel x - (h + h * h) - A.width - D.width,
    hi := ArctanGeometry.integralKernel x + A.width + D.width }

theorem arctanForwardQuotientPaddedKernelBound_contains
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (arctanForwardQuotientPaddedKernelBound x h n).ContainsInterval
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute (x + h) n)
        (ArctanGeometry.arctanIntegralRectangleCompute x n) h) := by
  let A := QInterval.scaleRat (1 / h)
    (ArctanGeometry.chartAddAreaLoopCompute x
      (ArctanGeometry.tangentChartIncrement x h) n)
  let B := QInterval.differenceQuotient
    (ArctanGeometry.arctanIntegralRectangleCompute
      (ArctanGeometry.tangentChartIncrement x h) n)
    (ArctanGeometry.arctanIntegralRectangleCompute 0 n) h
  let D := QInterval.differenceQuotient
    (ArctanGeometry.arctanIntegralRectangleCompute (x + h) n)
    (ArctanGeometry.arctanIntegralRectangleCompute x n) h
  let K : QInterval :=
    { lo := ArctanGeometry.integralKernel x - (h + h * h),
      hi := ArctanGeometry.integralKernel x }
  have hK : K.ContainsInterval B := by
    exact ArctanGeometry.arctanIntegralRectangleCompute_tangentChart_quotient_kernel_contains
      hx0 hx1 hpos n
  have hA : A.ContainsInterval B := by
    exact ArctanGeometry.tangentChart_transport_scaled_contains_chartQuotient_on_unit
      hx0 hx1 hpos hupper n
  have hBord : 0 <= B.width := by
    exact arctan_zero_tangent_quotient_ordered hpos
      (Rat.le_of_lt (ArctanGeometry.tangentChartIncrement_pos hx0 hpos)) n
  have hAB : A.Overlaps B := QInterval.overlaps_of_contains_right hA hBord
  have hAin : ({ lo := K.lo - A.width, hi := K.hi + A.width } : QInterval).ContainsInterval A :=
    overlaps_implies_contains_width_padding_left hK hAB
  have hAD : A.Overlaps D := by
    exact ArctanGeometry.tangentChart_transport_scaled_overlaps_forwardQuotient_on_unit
      hx0 hx1 hpos hupper n
  have hD := overlaps_implies_contains_width_padding hAin hAD
  simpa [arctanForwardQuotientPaddedKernelBound, A, B, D, K] using hD

theorem arctanForwardQuotient_padding_width_le
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1)
    (δ : QPos) (η : QPos) (N : Nat)
    (hη : η.val = h * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    (QInterval.scaleRat (1 / h)
      (ArctanGeometry.chartAddAreaLoopCompute x
        (ArctanGeometry.tangentChartIncrement x h) N)).width +
        (QInterval.differenceQuotient
          (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
          (ArctanGeometry.arctanIntegralRectangleCompute x N) h).width <=
      δ.val := by
  have hNrect : 4 * (η.val.den + 1) <= N := by omega
  have hchart := ArctanGeometry.tangentChartAreaLoopCompute_width_le_eps_on_unit
    hx0 hx1 hpos hupper η N hN
  have hleft := ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
    hx0 hx1 η N hNrect
  have hright := ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
    (by grind : 0 <= x + h) (by grind : x + h <= 1) η N hNrect
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscale : (1 / h) * η.val = δ.val / 3 := by
    rw [hη, Rat.div_def]
    have hcancel : h⁻¹ * h = 1 :=
      Rat.inv_mul_cancel h (Rat.ne_of_gt hpos)
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hA :
      (QInterval.scaleRat (1 / h)
        (ArctanGeometry.chartAddAreaLoopCompute x
          (ArctanGeometry.tangentChartIncrement x h) N)).width <=
        (1 / h) * η.val := by
    rw [QInterval.scaleRat_width_of_nonneg hinv]
    exact Rat.mul_le_mul_of_nonneg_left hchart hinv
  have hD :
      (QInterval.differenceQuotient
        (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
        (ArctanGeometry.arctanIntegralRectangleCompute x N) h).width <=
        2 * ((1 / h) * η.val) := by
    unfold QInterval.differenceQuotient QInterval.divRat
    rw [QInterval.scaleRat_width_of_nonneg hinv, QInterval.sub_width]
    calc
      (1 / h) *
          ((ArctanGeometry.arctanIntegralRectangleCompute (x + h) N).width +
            (ArctanGeometry.arctanIntegralRectangleCompute x N).width) <=
          (1 / h) * (η.val + η.val) :=
        Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hright hleft) hinv
      _ = 2 * ((1 / h) * η.val) := by
        grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  calc
    (QInterval.scaleRat (1 / h)
        (ArctanGeometry.chartAddAreaLoopCompute x
          (ArctanGeometry.tangentChartIncrement x h) N)).width +
        (QInterval.differenceQuotient
          (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
          (ArctanGeometry.arctanIntegralRectangleCompute x N) h).width <=
        (1 / h) * η.val + 2 * ((1 / h) * η.val) :=
      rat_add_le_add hA hD
    _ = δ.val := by
      rw [hscale]
      grind [Rat.div_def]

def arctanPrimitiveRaw : RealFunRaw where
  domain := inDomainInterval 0 1
  compute := fun x n => (ArctanGeometry.arctanIntegralRectangleRaw x).compute n

theorem arctanPrimitiveRaw_valid : arctanPrimitiveRaw.Valid := by
  intro x hx
  exact ArctanGeometry.arctanIntegralRectangleRaw_valid hx.1 hx.2

theorem arctanForwardEndpoint_scale_contains
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (N : Nat) :
    (QInterval.scaleRat h
      (arctanForwardQuotientPaddedKernelBound x h N)).ContainsInterval
      (endpointDifferenceInterval arctanPrimitiveRaw x (x + h) N) := by
  have hquotient := arctanForwardQuotientPaddedKernelBound_contains
    hx0 hx1 hpos hupper N
  have hscale := QInterval.scaleRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hquotient
  have heq :
      QInterval.scaleRat h
        (QInterval.differenceQuotient
          (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
          (ArctanGeometry.arctanIntegralRectangleCompute x N) h) =
        endpointDifferenceInterval arctanPrimitiveRaw x (x + h) N := by
    have hinv : 0 <= 1 / h := by
      rw [Rat.div_def]
      simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
    have hcancel : h * h⁻¹ = 1 :=
      Rat.mul_inv_cancel h (Rat.ne_of_gt hpos)
    change QInterval.scaleRat h
        (QInterval.differenceQuotient
          (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N)
          (ArctanGeometry.arctanIntegralRectangleCompute x N) h) =
      { lo := (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N).lo -
          (ArctanGeometry.arctanIntegralRectangleCompute x N).hi,
        hi := (ArctanGeometry.arctanIntegralRectangleCompute (x + h) N).hi -
          (ArctanGeometry.arctanIntegralRectangleCompute x N).lo }
    unfold QInterval.differenceQuotient QInterval.divRat
      QInterval.scaleRat QInterval.sub
    simp only [if_pos (Rat.le_of_lt hpos), if_pos hinv]
    apply (QInterval.mk.injEq _ _ _ _).mpr
    constructor <;> grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
      Rat.sub_eq_add_neg]
  rw [← heq]
  exact hscale

def arctanKernelRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => 1 / (1 + x * x))

theorem arctanKernel_den_pos {x : Rat} (hx : 0 <= x) :
    0 < 1 + x * x := by
  exact RationalCircle.Stage.one_add_square_pos x

theorem arctanKernel_antitone_on_unit {a b x : Rat}
    (ha : 0 <= a) (hab : a <= b) (hx : a <= x) (hxb : x <= b) :
    1 / (1 + b * b) <= 1 / (1 + x * x) ∧
      1 / (1 + x * x) <= 1 / (1 + a * a) := by
  have hx0 : 0 <= x := Rat.le_trans ha hx
  have hb0 : 0 <= b := Rat.le_trans hx0 hxb
  have hax : a * a <= x * x := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hx ha
    have h2 := Rat.mul_le_mul_of_nonneg_left hx (Rat.le_trans ha hx)
    calc
      a * a <= x * a := h1
      _ <= x * x := h2
  have hxb2 : x * x <= b * b := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hxb hx0
    have h2 := Rat.mul_le_mul_of_nonneg_left hxb hb0
    calc
      x * x <= b * x := h1
      _ <= b * b := h2
  constructor
  · exact ArctanGeometry.integralKernel_antitone_nonneg hx0 hxb
  · exact ArctanGeometry.integralKernel_antitone_nonneg ha hx

theorem arctanKernel_variation_le_step
    {a x : Rat} (ha0 : 0 <= a) (hax : a <= x) (hx1 : x <= 1) :
    1 / (1 + a * a) - 1 / (1 + x * x) <= x - a := by
  let da : Rat := 1 + a * a
  let dx : Rat := 1 + x * x
  have hda : 0 < da := by
    dsimp [da]
    exact RationalCircle.Stage.one_add_square_pos a
  have hdx : 0 < dx := by
    dsimp [dx]
    exact RationalCircle.Stage.one_add_square_pos x
  have hprod : 0 < da * dx := Rat.mul_pos hda hdx
  have hsum01 : a + x <= 1 + a * x := by
    have hnonneg : 0 <= (1 - a) * (1 - x) := by
      exact Rat.mul_nonneg (by grind) (by grind)
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hsquare := RationalCircle.Stage.ratSquare_nonneg (x - a)
  have hden : 1 + a * x <= da * dx := by
    change 1 + a * x <= (1 + a * a) * (1 + x * x)
    have hcross : a * x <= (a * a + x * x) / 2 := by
      rw [Rat.div_def]
      have htwo : 0 < (2 : Rat) := by native_decide
      apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
      · grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.sub_eq_add_neg]
      · exact htwo
    have hsqsum : 0 <= a * a + x * x := by
      exact Rat.add_nonneg (RationalCircle.Stage.ratSquare_nonneg a)
        (RationalCircle.Stage.ratSquare_nonneg x)
    have hcross' : a * x <= a * a + x * x := by
      exact Rat.le_trans hcross (by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm])
    have hprodnonneg : 0 <= a * a * (x * x) := by
      exact Rat.mul_nonneg (RationalCircle.Stage.ratSquare_nonneg a)
        (RationalCircle.Stage.ratSquare_nonneg x)
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hsumden : a + x <= da * dx := Rat.le_trans hsum01 hden
  have hnum : (x - a) * (a + x) <= (x - a) * (da * dx) :=
    Rat.mul_le_mul_of_nonneg_left hsumden (by grind)
  have hformula :
      1 / da - 1 / dx = ((x - a) * (a + x)) / (da * dx) := by
    simp only [Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
    have hcancelA : da * da⁻¹ = 1 := Rat.mul_inv_cancel da (Rat.ne_of_gt hda)
    have hcancelX : dx * dx⁻¹ = 1 := Rat.mul_inv_cancel dx (Rat.ne_of_gt hdx)
    dsimp [da, dx] at hcancelA hcancelX ⊢
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hformula, Rat.div_def]
  calc
    ((x - a) * (a + x)) * (da * dx)⁻¹ <=
        ((x - a) * (da * dx)) * (da * dx)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hnum
        (Rat.le_of_lt ((Rat.inv_pos).2 hprod))
    _ = x - a := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hprod)]
      grind

def arctanKernelBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := 1 / (1 + C.upper * C.upper),
    hi := 1 / (1 + C.lower * C.lower) }

theorem arctanKernelBound_contains
    (C : RationalSubinterval 0 1) (n : Nat)
    {x : Rat} (hx : C.contains x) :
    QInterval.ContainsInterval (arctanKernelBound C n)
      (arctanKernelRaw.compute x n) := by
  unfold arctanKernelBound arctanKernelRaw RealFunRaw.exact
    QInterval.ContainsInterval
  have h := arctanKernel_antitone_on_unit C.lower_mem C.ordered hx.1 hx.2
  simpa using h

theorem arctanKernelBound_ordered
    (C : RationalSubinterval 0 1) (n : Nat) :
    0 <= (arctanKernelBound C n).width := by
  unfold arctanKernelBound QInterval.width
  have h := arctanKernel_antitone_on_unit C.lower_mem C.ordered
    C.ordered (by exact Rat.le_refl)
  grind

def arctanKernelDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (RationalPartition.uniform 0 1 (eps.val.den + 1)
      (by omega) (by native_decide)).pieces) :
    DerivativeBoundOnSubinterval arctanKernelRaw
      ((RationalPartition.uniform 0 1 (eps.val.den + 1)
        (by omega) (by native_decide)).cell k hk) := by
  let P := RationalPartition.uniform 0 1 (eps.val.den + 1)
    (by omega) (by native_decide)
  let C := P.cell k hk
  exact {
    bound := fun n => arctanKernelBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => arctanKernelBound_ordered C n
    contains_values := fun n x hx => by
      exact arctanKernelBound_contains C n hx }

end Integral

end ComputableAnalysis
