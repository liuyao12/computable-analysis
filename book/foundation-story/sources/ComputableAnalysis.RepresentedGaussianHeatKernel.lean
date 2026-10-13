import ComputableAnalysis.RepresentedInverseSquareTime
import ComputableAnalysis.ComplexExponentialLift
import ComputableAnalysis.ComplexMultiplication
import ComputableAnalysis.FiniteGaussianRadiusQuadrature

/-!
# The Gaussian and heat kernel at represented positive time

This module evaluates the normalized Gaussian at the represented scale

`q = 1 / (2 * sqrt t)`

and hence constructs the one-dimensional heat-kernel value

`q * M⁻¹ * exp (-(x*q)^2)`

for rational `x` and represented positive `t`.  Here `M⁻¹` is the already
computed reciprocal of the full-line Gaussian mass.  Every evaluator uses
only finite rational interval operations and finite Taylor prefixes.
-/

namespace ComputableAnalysis
namespace RepresentedGaussianHeatKernel

open RepresentedPositiveSquareRoot
open RepresentedInverseSquareTime

/-- The represented nonnegative square `q²`. -/
def scaleSquare {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  RealRaw.mul (guardedScale A) (guardedScale A)

theorem scaleSquare_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (scaleSquare A).Valid := by
  unfold scaleSquare
  exact RealRaw.mulSelf_valid_of_nonneg_bounded
    (guardedScale_valid A) (scaleBound_pos A) (guardedScale_bounds A)

theorem scaleSquare_bounds {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    0 <= ((scaleSquare A).compute n).lo /\
      ((scaleSquare A).compute n).hi <=
        scaleBound bound margin * scaleBound bound margin := by
  have hq := guardedScale_bounds A n
  have horder := RealRaw.interval_order_of_valid (guardedScale A)
    (guardedScale_valid A) n
  have hcompute : (scaleSquare A).compute n =
      { lo := ((guardedScale A).compute n).lo *
          ((guardedScale A).compute n).lo,
        hi := ((guardedScale A).compute n).hi *
          ((guardedScale A).compute n).hi } := by
    unfold scaleSquare RealRaw.mul RealRaw.mulCompute
    exact QBox.mulRealInterval_self_of_nonneg hq.1 horder
  rw [hcompute]
  constructor
  · exact Rat.mul_nonneg hq.1 hq.1
  · exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hq.2
        (by exact Rat.le_trans hq.1 horder))
      (Rat.mul_le_mul_of_nonneg_right hq.2 (scaleBound_nonneg A))

/-- A common bound for the negative Gaussian exponent at spatial point `x`. -/
def argumentBound (x : Rat) (bound : Nat) (margin : Rat) : Rat :=
  (x * x) * (scaleBound bound margin * scaleBound bound margin)

theorem argumentBound_nonneg (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    0 <= argumentBound x bound margin := by
  unfold argumentBound
  exact Rat.mul_nonneg (rat_square_nonneg_basic x)
    (Rat.mul_nonneg (scaleBound_nonneg A) (scaleBound_nonneg A))

/-- The represented real Taylor argument `-(x*q)²`. -/
def argumentRaw (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  RealRaw.neg (RealRaw.scaleRat (x * x) (scaleSquare A))

theorem argumentRaw_valid (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (argumentRaw x A).Valid := by
  unfold argumentRaw
  exact RealRaw.neg_valid (RealRaw.scaleRat_valid (scaleSquare_valid A))

theorem argumentRaw_bounds (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    -(argumentBound x bound margin) <= ((argumentRaw x A).compute n).lo /\
      ((argumentRaw x A).compute n).hi <= 0 := by
  have hsquare := scaleSquare_bounds A n
  have hx2 : 0 <= x * x := rat_square_nonneg_basic x
  simp only [argumentRaw, RealRaw.neg, RealRaw.negCompute,
    RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos hx2]
  change -(argumentBound x bound margin) <=
      -((x * x) * ((scaleSquare A).compute n).hi) /\
    -((x * x) * ((scaleSquare A).compute n).lo) <= 0
  constructor
  · apply Rat.neg_le_neg
    unfold argumentBound
    exact Rat.mul_le_mul_of_nonneg_left hsquare.2 hx2
  · have hproduct := Rat.mul_nonneg hx2 hsquare.1
    grind

theorem argumentComplex_center_normBound
    (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    QComplex.normBound
        ((ComplexRaw.ofRealRaw (argumentRaw x A)).compute n).center <=
      argumentBound x bound margin := by
  have hb := argumentRaw_bounds x A n
  have hC0 := argumentBound_nonneg x A
  have horder := RealRaw.interval_order_of_valid (argumentRaw x A)
    (argumentRaw_valid x A) n
  change qabs ((((argumentRaw x A).compute n).lo +
      ((argumentRaw x A).compute n).hi) / 2) + qabs ((0 + 0) / 2) <= _
  have hzero : (0 + 0 : Rat) / 2 = 0 := by native_decide
  rw [hzero, qabs_eq_self_of_nonneg (by native_decide : (0 : Rat) <= 0),
    Rat.add_zero]
  rw [qabs_eq_neg_of_nonpos]
  · rw [Rat.div_def]
    have hhalf0 : 0 <= (2 : Rat)⁻¹ := Rat.le_of_lt
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))
    have hlo : -(argumentBound x bound margin) <=
        ((argumentRaw x A).compute n).lo := hb.1
    have hhi : -(argumentBound x bound margin) <=
        ((argumentRaw x A).compute n).hi := Rat.le_trans hlo horder
    have hsum : -(2 * argumentBound x bound margin) <=
        ((argumentRaw x A).compute n).lo +
          ((argumentRaw x A).compute n).hi := by grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hsum hhalf0
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · rw [Rat.div_def]
    have hhalf0 : 0 <= (2 : Rat)⁻¹ := Rat.le_of_lt
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))
    have hsumNonpos :
        ((argumentRaw x A).compute n).lo +
          ((argumentRaw x A).compute n).hi <= 0 := by grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hsumNonpos hhalf0
    simpa using hscaled

/-- The negative Gaussian exponent packaged with the common bound needed by
the represented Taylor exponential. -/
def boundedArgumentInput (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    ComplexExponentialLift.BoundedInput (argumentBound x bound margin) where
  raw := ComplexRaw.ofRealRaw (argumentRaw x A)
  valid := ComplexRaw.ofRealRaw_valid _ (argumentRaw_valid x A)
  radius_nonneg := argumentBound_nonneg x A
  center_normBound := argumentComplex_center_normBound x A

/-- The represented Gaussian factor `exp (-(x*q)²)`. -/
def gaussianExponentialComplex (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw :=
  ComplexExponentialLift.BoundedInput.exponential (boundedArgumentInput x A)

theorem gaussianExponentialComplex_valid
    (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (gaussianExponentialComplex x A).Valid :=
  ComplexExponentialLift.BoundedInput.exponential_valid
    (boundedArgumentInput x A)

/-- The normalized represented Gaussian profile `M⁻¹ exp (-(x*q)²)`. -/
def normalizedGaussianComplex (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw :=
  ComplexRaw.mul
    (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw)
    (gaussianExponentialComplex x A)

theorem normalizedGaussianComplex_valid
    (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (normalizedGaussianComplex x A).Valid := by
  unfold normalizedGaussianComplex
  exact ComplexRaw.mul_valid
    (ComplexRaw.ofRealRaw_valid _ gaussianFullLineMassReciprocalRaw_valid)
    (gaussianExponentialComplex_valid x A)

/-- The direct represented-time heat-kernel value on the real axis. -/
def heatKernelComplex (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw :=
  ComplexRaw.mul (guardedScaleComplex A) (normalizedGaussianComplex x A)

def heatKernel (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  (heatKernelComplex x A).realPart

theorem heatKernelComplex_valid
    (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (heatKernelComplex x A).Valid := by
  unfold heatKernelComplex
  exact ComplexRaw.mul_valid (guardedScaleComplex_valid A)
    (normalizedGaussianComplex_valid x A)

theorem heatKernel_valid
    (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (heatKernel x A).Valid :=
  ComplexRaw.realPart_valid (heatKernelComplex_valid x A)

/-! ## Independence of the represented-time name -/

theorem scaleSquare_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (scaleSquare A).Equiv (scaleSquare B) := by
  unfold scaleSquare
  exact RealRaw.mul_equiv_of_nonneg
    (guardedScale_valid A) (guardedScale_valid B)
    (guardedScale_valid A) (guardedScale_valid B)
    (fun n => (guardedScale_bounds A n).1)
    (fun n => (guardedScale_bounds B n).1)
    (fun n => (guardedScale_bounds A n).1)
    (fun n => (guardedScale_bounds B n).1)
    (guardedScale_equiv_of_input_equiv A B hAB)
    (guardedScale_equiv_of_input_equiv A B hAB)

theorem argumentRaw_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (argumentRaw x A).Equiv (argumentRaw x B) := by
  unfold argumentRaw
  exact RealRaw.neg_equiv (RealRaw.scaleRat_equiv
    (scaleSquare_equiv_of_input_equiv A B hAB))

theorem boundedArgumentInput_raw_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (boundedArgumentInput x A).raw.Equiv
      (boundedArgumentInput x B).raw := by
  exact ComplexRaw.ofRealRaw_equiv_of_equiv
    (argumentRaw_valid x A) (argumentRaw_valid x B)
    (argumentRaw_equiv_of_input_equiv x A B hAB)

theorem gaussianExponentialComplex_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (gaussianExponentialComplex x A).Equiv
      (gaussianExponentialComplex x B) := by
  exact ComplexExponentialLift.BoundedInput.exponential_equiv_of_input_equiv
    (boundedArgumentInput x A) (boundedArgumentInput x B)
    (boundedArgumentInput_raw_equiv_of_input_equiv x A B hAB)

theorem normalizedGaussianComplex_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (normalizedGaussianComplex x A).Equiv
      (normalizedGaussianComplex x B) := by
  unfold normalizedGaussianComplex
  have hmassValid :
      (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw).Valid :=
    ComplexRaw.ofRealRaw_valid _ gaussianFullLineMassReciprocalRaw_valid
  exact ComplexRaw.mul_equiv
    hmassValid hmassValid
    (gaussianExponentialComplex_valid x A)
    (gaussianExponentialComplex_valid x B)
    (ComplexRaw.equiv_refl _ hmassValid)
    (gaussianExponentialComplex_equiv_of_input_equiv x A B hAB)

theorem heatKernelComplex_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (heatKernelComplex x A).Equiv (heatKernelComplex x B) := by
  unfold heatKernelComplex
  exact ComplexRaw.mul_equiv
    (guardedScaleComplex_valid A) (guardedScaleComplex_valid B)
    (normalizedGaussianComplex_valid x A)
    (normalizedGaussianComplex_valid x B)
    (guardedScaleComplex_equiv_of_input_equiv A B hAB)
    (normalizedGaussianComplex_equiv_of_input_equiv x A B hAB)

/-- The direct heat-kernel value descends to represented positive time. -/
theorem heatKernel_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (heatKernel x A).Equiv (heatKernel x B) :=
  ComplexRaw.realPart_equiv
    (heatKernelComplex_equiv_of_input_equiv x A B hAB)

end RepresentedGaussianHeatKernel
end ComputableAnalysis
