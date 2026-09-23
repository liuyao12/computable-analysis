import ComputableAnalysis.ComputableLogarithmDerivative
import ComputableAnalysis.ComputableFactoredPrimitives

/-! Concrete elementary charts and their rational-function derivatives. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates ComputableCoefficient

/-- Identify the derivative computation with a separately evaluated rational
expression. The hypothesis is finite rational algebra, not a derivative law. -/
theorem Coefficient.derivative_equiv (m : Coefficient) (imag : Bool) (t : Rat)
    (ht : qabs t ≤ m.radius) (v : Value) (cutoff : Nat)
    (heq : ∀ n, cutoff ≤ n → ∀ s, Samples n s →
      coordinate imag (kernel ⟨m.realCoefficient.sample s, m.imagCoefficient.sample s⟩ t) = v.sample s) :
    (rawCoordinate imag (m.derivative t)).Equiv v.real.preferred := by
  intro k
  let n := max k (max cutoff (v.observation k))
  have hn : k ≤ n := Nat.le_max_left _ _
  have hs := m.index_le_stage n
  have hv := v.encloses k (m.stage n) (by dsimp [n] at *; omega) (m.samples n) (m.samples_valid n)
  have he := heq (m.stage n) (by dsimp [n] at *; omega) (m.samples n) (m.samples_valid n)
  have hd := m.derivative_coordinate_mem imag ht n
  have hh := (rawCoordinate_valid imag (m.derivative_valid ht)).2.1 k n hn
  have he' : coordinate imag (m.derivativeSample t n) = v.sample (m.samples n) := he
  rw [he'] at hd
  apply (RealRaw.compareAt_overlap_iff _ _ k k).2
  change ((rawCoordinate imag (m.derivative t)).compute k).lo ≤ (v.real.compute k).hi ∧
    (v.real.compute k).lo ≤ ((rawCoordinate imag (m.derivative t)).compute k).hi
  constructor <;> grind

namespace Value

theorem inverse_sample_apart (x y : Value) (N : Nat) (hy : x.inv? N = some y)
    (n : Nat) (hn : x.observation N ≤ n) (s : Real → Rat) (hs : Samples n s) :
    x.sample s ≠ 0 := by
  have hx := x.encloses N n hn s hs
  unfold ComputableCoefficient.Value.inv? at hy
  split at hy
  · rename_i hp
    intro hz
    rw [hz] at hx
    grind
  · split at hy
    · rename_i hm
      intro hz
      rw [hz] at hx
      grind
    · cases hy

end Value

/-- A normalized logarithm around a rational center away from an arbitrary
computable pole. The reciprocal is supplied by the finite coefficient test. -/
def simplePoleChart (inverse : Value) : Coefficient := ⟨inverse, .rational 0, .rational 1⟩

def simplePolePrimitive (inverse : Value) (center : Rat) : FunctionOnInterval :=
  (simplePoleChart inverse).valueOn false center

def simplePoleDerivative (inverse : Value) (center : Rat) : FunctionOnInterval :=
  (simplePoleChart inverse).derivativeOn false center

def simplePole_hasDerivative (inverse : Value) (center : Rat) :
    HasDerivativeOnInterval (simplePolePrimitive inverse center) (simplePoleDerivative inverse center) :=
  (simplePoleChart inverse).hasDerivative false center

/-- The constructed derivative is the original reciprocal `1/(x-pole)`,
including irrational poles. Both inversions are actual coefficient evaluators. -/
theorem simplePole_derivative_equiv (pole inverse v : Value) (center x : Rat) (N M : Nat)
    (hi : (Value.sub (.rational center) pole).inv? N = some inverse)
    (hv : (Value.sub (.rational x) pole).inv? M = some v)
    (hx : qabs (x-center) ≤ (simplePoleChart inverse).radius) :
    (rawCoordinate false ((simplePoleChart inverse).derivative (x-center))).Equiv v.real.preferred := by
  apply (simplePoleChart inverse).derivative_equiv false (x-center) hx v
    ((Value.sub (.rational center) pole).observation N)
  intro n hn s hs
  have hcenter := Value.inverse_sample_apart _ _ N hi n hn s hs
  have hreal := Value.inv?_sample _ _ N hi s
  have hvalue := Value.inv?_sample _ _ M hv s
  simp only [ComputableCoefficient.Value.sub, ComputableCoefficient.Value.add,
    ComputableCoefficient.Value.neg, ComputableCoefficient.Value.rational, ← Rat.sub_eq_add_neg] at hcenter hreal hvalue
  change coordinate false (kernel ⟨inverse.sample s, 0⟩ (x-center)) = v.sample s
  rw [hreal, hvalue]
  have hc := Rat.inv_mul_cancel (center-pole.sample s) hcenter
  have hd : 1+(x-center)*(center-pole.sample s)⁻¹ =
      (x-pole.sample s)*(center-pole.sample s)⁻¹ := by grind
  simp only [coordinate, Bool.false_eq_true, if_false, kernel, QComplex.mul,
    QComplex.inverse, QComplex.normSq, QComplex.add, QComplex.one, QComplex.scaleRat,
    Rat.mul_zero, Rat.add_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  simp only [← Rat.sub_eq_add_neg, Rat.zero_mul, Rat.neg_zero, Rat.add_zero]
  rw [hd]
  by_cases hxp : x-pole.sample s = 0
  · simp only [hxp, Rat.zero_mul, Rat.div_def, show (0 : Rat)⁻¹ = 0 by decide +kernel, Rat.mul_zero]
  · have hxc := Rat.mul_inv_cancel (x-pole.sample s) hxp
    simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
    grind

/-- Arctangent is the imaginary logarithm coordinate. The coefficient itself
may be irrational; its derivative is computed by the rational kernel. -/
def arctanChart (scale : Value) : Coefficient := ⟨.rational 0, scale, .rational 1⟩

def arctanPrimitive (scale : Value) (center : Rat) : FunctionOnInterval :=
  (arctanChart scale).valueOn true center

def arctanDerivative (scale : Value) (center : Rat) : FunctionOnInterval :=
  (arctanChart scale).derivativeOn true center

def arctan_hasDerivative (scale : Value) (center : Rat) :
    HasDerivativeOnInterval (arctanPrimitive scale center) (arctanDerivative scale center) :=
  (arctanChart scale).hasDerivative true center

theorem arctan_kernel (s t : Rat) : coordinate true (kernel ⟨0,s⟩ t) = s/(1+(s*t)*(s*t)) := by
  simp only [coordinate, if_true, kernel, QComplex.mul, QComplex.inverse, QComplex.normSq,
    QComplex.add, QComplex.one, QComplex.scaleRat, Rat.mul_zero, Rat.zero_mul, Rat.add_zero,
    Rat.zero_add, Rat.one_mul, Rat.mul_one, Rat.neg_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.div_def]
  grind

/-- The concrete derivative has the familiar arctangent rational expression. -/
theorem arctan_derivative_equiv (scale v : Value) (center x : Rat)
    (hx : qabs (x-center) ≤ (arctanChart scale).radius)
    (he : ∀ s, v.sample s = scale.sample s / (1+(scale.sample s*(x-center))*(scale.sample s*(x-center)))) :
    (rawCoordinate true ((arctanChart scale).derivative (x-center))).Equiv v.real.preferred := by
  apply (arctanChart scale).derivative_equiv true (x-center) hx v 0
  intro n hn s hs
  change coordinate true (kernel ⟨0, scale.sample s⟩ (x-center)) = v.sample s
  rw [arctan_kernel, he]

end ComputableLogarithmChart
end ComputableAnalysis
