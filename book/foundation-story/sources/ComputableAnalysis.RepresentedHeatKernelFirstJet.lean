import ComputableAnalysis.RepresentedGaussianHeatKernel
import ComputableAnalysis.PositiveSquareRootJet
import ComputableAnalysis.ComplexReciprocalJet
import ComputableAnalysis.ComplexExponentialJet

/-!
# Direct represented-time first jet of the heat kernel

For a represented positive time input this module follows the complete
computational chain

`t -> sqrt t -> 1/(2*sqrt t) -> -(x/(2*sqrt t))^2 -> exp -> K`.

The value component is the existing direct represented heat-kernel evaluator.
The gradient component is an executable represented-complex candidate obtained
from the square-root, reciprocal, exponential, and product jet rules.  This is
the algebraic/analytic-approximant layer needed by a later quantitative
`HasDerivativeOnInterval` theorem; it does not by itself assert that final
finite-difference certificate.
-/

namespace ComputableAnalysis
namespace RepresentedHeatKernelFirstJet

open RepresentedPositiveSquareRoot
open RepresentedInverseSquareTime
open RepresentedGaussianHeatKernel

abbrev MultiFirstJet := RepresentedMultivariableHolomorphicJet.FirstJet

/-- Physical time as the sole coordinate of a one-variable represented jet. -/
def timeJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.timeCoordinate
    (spatialDimension := 0) (ComplexRaw.ofRealRaw A.raw)

theorem timeJet_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (timeJet A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.timeCoordinate_valid
    (ComplexRaw.ofRealRaw_valid A.raw A.valid)

@[simp] theorem timeJet_value {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (timeJet A).value = ComplexRaw.ofRealRaw A.raw := rfl

@[simp] theorem timeJet_gradient {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (timeJet A).gradient 0 = ComplexRaw.one := rfl

/-- The positive branch input connecting the numerical square-root algorithm
to the one-coordinate time jet. -/
def squareRootInput {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    PositiveSquareRootJet.Input 1 bound margin where
  positive := A
  inner := timeJet A
  innerValid := timeJet_valid A
  value_agrees := ComplexRaw.equiv_refl _
    (ComplexRaw.ofRealRaw_valid A.raw A.valid)

/-- Represented positive square-root jet of physical time. -/
def squareRootJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  PositiveSquareRootJet.Input.representedJet (squareRootInput A)

theorem squareRootJet_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (squareRootJet A).Valid :=
  PositiveSquareRootJet.Input.representedJet_valid (squareRootInput A)

@[simp] theorem squareRootJet_value {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (squareRootJet A).value = A.awayRootRaw := rfl

/-- The reciprocal square-root jet, composed with the selected positive
square-root branch. -/
def reciprocalSquareRootJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar
    (ComplexReciprocalJet.representedJet A.awayInput) (squareRootJet A)

theorem reciprocalSquareRootJet_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (reciprocalSquareRootJet A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_valid
    (ComplexReciprocalJet.representedJet_valid A.awayInput)
    (squareRootJet_valid A)

@[simp] theorem reciprocalSquareRootJet_value
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (reciprocalSquareRootJet A).value = A.awayInput.reciprocal := rfl

/-- The unguarded inverse-square scale jet `q = 1/(2*sqrt t)`. -/
def scaleJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat (1 / 2)
    (reciprocalSquareRootJet A)

theorem scaleJet_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (scaleJet A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_valid (1 / 2)
    (reciprocalSquareRootJet_valid A)

@[simp] theorem scaleJet_value {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (scaleJet A).value = scaleComplex A := rfl

/-- Rebox only the value component of the scale jet into the common public
guard.  The derivative component remains the composed square-root/reciprocal
algorithm. -/
def guardedScaleJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 where
  value := guardedScaleComplex A
  gradient := (scaleJet A).gradient

theorem guardedScaleJet_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (guardedScaleJet A).Valid :=
  ⟨guardedScaleComplex_valid A, (scaleJet_valid A).2⟩

theorem guardedScaleJet_equiv_scaleJet {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (guardedScaleJet A).Equiv (scaleJet A) := by
  constructor
  · exact guardedScaleComplex_equiv_scaleComplex A
  · intro i
    exact ComplexRaw.equiv_refl _ ((scaleJet_valid A).2 i)

/-- Algebraic argument jet obtained from the guarded represented scale. -/
def algebraicArgumentJet (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  let xq := RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat x
    (guardedScaleJet A)
  RepresentedMultivariableHolomorphicJet.FirstJet.neg
    (RepresentedMultivariableHolomorphicJet.FirstJet.mul xq xq)

theorem algebraicArgumentJet_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (algebraicArgumentJet x A).Valid := by
  let xq := RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat x
    (guardedScaleJet A)
  have hxq : xq.Valid :=
    RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_valid x
      (guardedScaleJet_valid A)
  exact RepresentedMultivariableHolomorphicJet.FirstJet.neg_valid
    (RepresentedMultivariableHolomorphicJet.FirstJet.mul_valid hxq hxq)

/-- Argument jet with the literal value evaluator already consumed by the
bounded exponential implementation. -/
def argumentJet (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 where
  value := ComplexRaw.ofRealRaw (argumentRaw x A)
  gradient := (algebraicArgumentJet x A).gradient

theorem argumentJet_valid (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (argumentJet x A).Valid :=
  ⟨ComplexRaw.ofRealRaw_valid _ (argumentRaw_valid x A),
    (algebraicArgumentJet_valid x A).2⟩

@[simp] theorem argumentJet_value (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (argumentJet x A).value = (boundedArgumentInput x A).raw := rfl

/-- Exponential composed with the direct represented Gaussian argument. -/
def exponentialJet (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar
    (ComplexExponentialJet.representedJet (boundedArgumentInput x A))
    (argumentJet x A)

theorem exponentialJet_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (exponentialJet x A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_valid
    (ComplexExponentialJet.representedJet_valid (boundedArgumentInput x A))
    (argumentJet_valid x A)

@[simp] theorem exponentialJet_value (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (exponentialJet x A).value = gaussianExponentialComplex x A := rfl

/-- The normalized Gaussian jet `M⁻¹ exp(-(x*q)^2)`. -/
def normalizedGaussianJet (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.mul
    (RepresentedMultivariableHolomorphicJet.FirstJet.constantRaw
      (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw))
    (exponentialJet x A)

theorem normalizedGaussianJet_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (normalizedGaussianJet x A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.mul_valid
    (RepresentedMultivariableHolomorphicJet.FirstJet.constantRaw_valid
      (ComplexRaw.ofRealRaw_valid _ gaussianFullLineMassReciprocalRaw_valid))
    (exponentialJet_valid x A)

@[simp] theorem normalizedGaussianJet_value (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (normalizedGaussianJet x A).value = normalizedGaussianComplex x A := rfl

/-- Direct represented-time first jet of the heat kernel. -/
def heatKernelJet (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : MultiFirstJet 1 :=
  RepresentedMultivariableHolomorphicJet.FirstJet.mul
    (guardedScaleJet A) (normalizedGaussianJet x A)

theorem heatKernelJet_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (heatKernelJet x A).Valid :=
  RepresentedMultivariableHolomorphicJet.FirstJet.mul_valid
    (guardedScaleJet_valid A) (normalizedGaussianJet_valid x A)

/-- The jet value is definitionally the existing represented-time kernel. -/
@[simp] theorem heatKernelJet_value (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (heatKernelJet x A).value = heatKernelComplex x A := rfl

/-- Executable direct-time derivative candidate. -/
def timeDerivativeComplex (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexRaw :=
  (heatKernelJet x A).gradient 0

def timeDerivative (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealRaw :=
  (timeDerivativeComplex x A).realPart

theorem timeDerivativeComplex_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (timeDerivativeComplex x A).Valid :=
  (heatKernelJet_valid x A).2 0

theorem timeDerivative_valid (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (timeDerivative x A).Valid :=
  ComplexRaw.realPart_valid (timeDerivativeComplex_valid x A)

/-- Literal represented chain/product-rule formula retained by the direct
time derivative candidate.  In particular, no derivative is inserted by
name: every factor is the output of the preceding represented jet. -/
theorem timeDerivativeComplex_formula (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    timeDerivativeComplex x A =
      ComplexRaw.add
        (ComplexRaw.mul ((guardedScaleJet A).gradient 0)
          (normalizedGaussianComplex x A))
        (ComplexRaw.mul (guardedScaleComplex A)
          (ComplexRaw.add
            (ComplexRaw.mul ComplexRaw.zero
              (gaussianExponentialComplex x A))
            (ComplexRaw.mul
              (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw)
              (ComplexRaw.mul (gaussianExponentialComplex x A)
                ((argumentJet x A).gradient 0))))) := rfl

theorem timeDerivativeComplex_compute (x : Rat)
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin)
    (stage : Nat) :
    (timeDerivativeComplex x A).compute stage =
      (ComplexRaw.add
        (ComplexRaw.mul ((guardedScaleJet A).gradient 0)
          (normalizedGaussianComplex x A))
        (ComplexRaw.mul (guardedScaleComplex A)
          (ComplexRaw.add
            (ComplexRaw.mul ComplexRaw.zero
              (gaussianExponentialComplex x A))
            (ComplexRaw.mul
              (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw)
              (ComplexRaw.mul (gaussianExponentialComplex x A)
                ((argumentJet x A).gradient 0)))))).compute stage := by
  rw [timeDerivativeComplex_formula]

/-- Public package for the executable supplied first jet.  The finite-
difference theorem remains a separate quantitative certificate. -/
structure Certificate (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : Prop where
  valid : (heatKernelJet x A).Valid
  valueFormula : (heatKernelJet x A).value = heatKernelComplex x A
  derivativeFormula : timeDerivativeComplex x A =
    (heatKernelJet x A).gradient 0

theorem certificate (x : Rat) {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : Certificate x A where
  valid := heatKernelJet_valid x A
  valueFormula := heatKernelJet_value x A
  derivativeFormula := rfl

/-! ## Independence of the represented positive-time name -/

theorem timeJet_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (timeJet A).Equiv (timeJet B) := by
  constructor
  · exact ComplexRaw.ofRealRaw_equiv_of_equiv A.valid B.valid hAB
  · intro i
    exact ComplexRaw.equiv_refl _ ((timeJet_valid A).2 i)

theorem squareRootJet_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (squareRootJet A).Equiv (squareRootJet B) := by
  exact ComplexSquareRootJet.representedJet_equiv
    (PositiveSquareRootJet.Input.toSquareRootInput (squareRootInput A))
    (PositiveSquareRootJet.Input.toSquareRootInput (squareRootInput B))
    (timeJet_equiv_of_input_equiv A B hAB)
    (RepresentedInverseSquareTime.awayRootRaw_equiv_of_input_equiv A B hAB)

theorem reciprocalSquareRootJet_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (reciprocalSquareRootJet A).Equiv (reciprocalSquareRootJet B) := by
  have hroot :=
    RepresentedInverseSquareTime.awayRootRaw_equiv_of_input_equiv A B hAB
  have houter := ComplexReciprocalJet.representedJet_equiv_of_input_equiv
    A.awayInput B.awayInput hroot
  exact RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_equiv
    (ComplexReciprocalJet.representedJet_valid A.awayInput)
    (ComplexReciprocalJet.representedJet_valid B.awayInput)
    (squareRootJet_valid A) (squareRootJet_valid B)
    houter (squareRootJet_equiv_of_input_equiv A B hAB)

theorem scaleJet_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (scaleJet A).Equiv (scaleJet B) :=
  RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_equiv (1 / 2)
    (reciprocalSquareRootJet_equiv_of_input_equiv A B hAB)

theorem guardedScaleJet_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (guardedScaleJet A).Equiv (guardedScaleJet B) := by
  constructor
  · exact guardedScaleComplex_equiv_of_input_equiv A B hAB
  · exact (scaleJet_equiv_of_input_equiv A B hAB).2

theorem algebraicArgumentJet_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (algebraicArgumentJet x A).Equiv
      (algebraicArgumentJet x B) := by
  let xqA := RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat x
    (guardedScaleJet A)
  let xqB := RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat x
    (guardedScaleJet B)
  have hxqA : xqA.Valid :=
    RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_valid x
      (guardedScaleJet_valid A)
  have hxqB : xqB.Valid :=
    RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_valid x
      (guardedScaleJet_valid B)
  have hxq : xqA.Equiv xqB :=
    RepresentedMultivariableHolomorphicJet.FirstJet.scaleRat_equiv x
      (guardedScaleJet_equiv_of_input_equiv A B hAB)
  exact RepresentedMultivariableHolomorphicJet.FirstJet.neg_equiv
    (RepresentedMultivariableHolomorphicJet.FirstJet.mul_equiv
      hxqA hxqB hxqA hxqB hxq hxq)

theorem argumentJet_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (argumentJet x A).Equiv (argumentJet x B) :=
  ⟨boundedArgumentInput_raw_equiv_of_input_equiv x A B hAB,
    (algebraicArgumentJet_equiv_of_input_equiv x A B hAB).2⟩

theorem exponentialJet_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (exponentialJet x A).Equiv (exponentialJet x B) := by
  have houter := ComplexExponentialJet.representedJet_equiv_of_input_equiv
    (boundedArgumentInput x A) (boundedArgumentInput x B)
    (boundedArgumentInput_raw_equiv_of_input_equiv x A B hAB)
  exact RepresentedMultivariableHolomorphicJet.FirstJet.composeScalar_equiv
    (ComplexExponentialJet.representedJet_valid (boundedArgumentInput x A))
    (ComplexExponentialJet.representedJet_valid (boundedArgumentInput x B))
    (argumentJet_valid x A) (argumentJet_valid x B)
    houter (argumentJet_equiv_of_input_equiv x A B hAB)

theorem normalizedGaussianJet_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (normalizedGaussianJet x A).Equiv
      (normalizedGaussianJet x B) := by
  let mass : MultiFirstJet 1 :=
    RepresentedMultivariableHolomorphicJet.FirstJet.constantRaw
      (ComplexRaw.ofRealRaw gaussianFullLineMassReciprocalRaw)
  have hmass : mass.Valid :=
    RepresentedMultivariableHolomorphicJet.FirstJet.constantRaw_valid
      (ComplexRaw.ofRealRaw_valid _ gaussianFullLineMassReciprocalRaw_valid)
  exact RepresentedMultivariableHolomorphicJet.FirstJet.mul_equiv
    hmass hmass (exponentialJet_valid x A) (exponentialJet_valid x B)
    (RepresentedMultivariableHolomorphicJet.FirstJet.equiv_refl mass hmass)
    (exponentialJet_equiv_of_input_equiv x A B hAB)

theorem heatKernelJet_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (heatKernelJet x A).Equiv (heatKernelJet x B) :=
  RepresentedMultivariableHolomorphicJet.FirstJet.mul_equiv
    (guardedScaleJet_valid A) (guardedScaleJet_valid B)
    (normalizedGaussianJet_valid x A) (normalizedGaussianJet_valid x B)
    (guardedScaleJet_equiv_of_input_equiv A B hAB)
    (normalizedGaussianJet_equiv_of_input_equiv x A B hAB)

theorem timeDerivativeComplex_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (timeDerivativeComplex x A).Equiv (timeDerivativeComplex x B) :=
  (heatKernelJet_equiv_of_input_equiv x A B hAB).2 0

theorem timeDerivative_equiv_of_input_equiv
    (x : Rat) {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (timeDerivative x A).Equiv (timeDerivative x B) :=
  ComplexRaw.realPart_equiv
    (timeDerivativeComplex_equiv_of_input_equiv x A B hAB)

/-! ## Direct rational positive-time charts -/

/-- Finite public data for a rational time chart uniformly separated from
zero and bounded above by a natural number. -/
structure PositiveTimeChart where
  lower : Rat
  upper : Rat
  ordered : lower <= upper
  bound : Nat
  upper_le_bound : upper <= (bound : Rat)
  margin : Rat
  margin_pos : 0 < margin
  margin_sq_le_lower : sq margin <= lower

namespace PositiveTimeChart

/-- Exact represented input at one rational time in the chart. -/
def inputAt (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    PositiveInput chart.bound chart.margin where
  raw := RealRaw.ofRat t
  valid := RealRaw.ofRat_valid t
  margin_pos := chart.margin_pos
  center_le_bound := by
    intro n
    change (t + t) / 2 <= (chart.bound : Rat)
    have htbound : t <= (chart.bound : Rat) :=
      Rat.le_trans ht.2 chart.upper_le_bound
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel 2 (by native_decide : (2 : Rat) ≠ 0)]
  margin_sq_le_center := by
    intro n
    change sq chart.margin <= (t + t) / 2
    have hmargin : sq chart.margin <= t :=
      Rat.le_trans chart.margin_sq_le_lower ht.1
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel 2 (by native_decide : (2 : Rat) ≠ 0)]

@[simp] theorem inputAt_raw (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    (chart.inputAt t ht).raw = RealRaw.ofRat t := rfl

/-- Direct represented heat kernel as a function of rational physical time. -/
def heatKernelOn (x : Rat) (chart : PositiveTimeChart) : FunctionOnInterval :=
  { raw :=
      { definedAt := fun t => inDomainInterval chart.lower chart.upper t
        compute := fun t ht n =>
        (RepresentedGaussianHeatKernel.heatKernel x
          (chart.inputAt t ht)).compute n }
    lower := chart.lower
    upper := chart.upper
    defined_on := fun _ ht => ht
    valid_on := fun t ht =>
      RepresentedGaussianHeatKernel.heatKernel_valid x
        (chart.inputAt t ht) }

/-- The executable direct-time derivative candidate on the same chart. -/
def timeDerivativeOn (x : Rat) (chart : PositiveTimeChart) :
    FunctionOnInterval :=
  { raw :=
      { definedAt := fun t => inDomainInterval chart.lower chart.upper t
        compute := fun t ht n =>
        (timeDerivative x (chart.inputAt t ht)).compute n }
    lower := chart.lower
    upper := chart.upper
    defined_on := fun _ ht => ht
    valid_on := fun t ht => timeDerivative_valid x (chart.inputAt t ht) }

@[simp] theorem heatKernelOn_compute (x : Rat)
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (stage : Nat) :
    (chart.heatKernelOn x).compute t ht stage =
      (RepresentedGaussianHeatKernel.heatKernel x
        (chart.inputAt t ht)).compute stage := rfl

@[simp] theorem timeDerivativeOn_compute (x : Rat)
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (stage : Nat) :
    (chart.timeDerivativeOn x).compute t ht stage =
      (timeDerivative x (chart.inputAt t ht)).compute stage := rfl

end PositiveTimeChart

end RepresentedHeatKernelFirstJet
end ComputableAnalysis
