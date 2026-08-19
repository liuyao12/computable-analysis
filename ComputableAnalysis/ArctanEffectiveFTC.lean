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
