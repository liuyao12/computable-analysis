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

def arctanPrimitiveRaw : RealFunRaw where
  domain := inDomainInterval 0 1
  compute := fun x n => (ArctanGeometry.arctanIntegralRectangleRaw x).compute n

theorem arctanPrimitiveRaw_valid : arctanPrimitiveRaw.Valid := by
  intro x hx
  exact ArctanGeometry.arctanIntegralRectangleRaw_valid hx.1 hx.2

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
