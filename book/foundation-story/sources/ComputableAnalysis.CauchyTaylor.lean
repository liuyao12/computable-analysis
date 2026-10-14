import ComputableAnalysis.CauchyTaylorKernel
import ComputableAnalysis.CertifiedComplexApproximation

/-!
# Exact reconstruction from certified Cauchy quadrature

The hypothesis is a Cauchy representation of an independently given function,
not a Taylor representation. Each finite rule consists of rational points on
the unit circle and rational complex weights (including the boundary values,
the contour differential and normalization). The conclusion is `ComplexRaw.Equiv`.

This module does NOT prove the Cauchy integral formula from complex
differentiability. That bridge, and identification of the moment coefficients
with iterated derivatives divided by factorials, are separate obligations.
-/

namespace ComputableAnalysis.CauchyTaylor

open QComplex
open CertifiedComplexApproximation (rate)

private theorem mul_zero (z : QComplex) : mul z zero = zero := by
  cases z; simp [mul, zero, Rat.sub_eq_add_neg, Rat.add_zero]

private theorem zero_mul (z : QComplex) : mul zero z = zero := by
  rw [mul_comm_cert]; exact mul_zero z

theorem l1_nonneg (z : QComplex) : 0 ≤ normBound z :=
  Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _)

theorem l1_add (z w : QComplex) : normBound (add z w) ≤ normBound z + normBound w := by
  have hr := qabs_add_le z.re w.re
  have hi := qabs_add_le z.im w.im
  unfold normBound add
  grind only

theorem l1_mul (z w : QComplex) : normBound (mul z w) ≤ normBound z * normBound w := by
  have hr := qabs_sub_le (z.re*w.re) (z.im*w.im)
  have hi := qabs_add_le (z.re*w.im) (z.im*w.re)
  rw [qabs_mul, qabs_mul] at hr hi
  unfold normBound mul
  grind only

theorem l1_coordinates {z : QComplex} {B : Rat} (h : normBound z ≤ B) :
    -B ≤ z.re ∧ z.re ≤ B ∧ -B ≤ z.im ∧ z.im ≤ B := by
  have hr0 := qabs_nonneg z.re
  have hi0 := qabs_nonneg z.im
  have hr := self_le_qabs z.re
  have hi := self_le_qabs z.im
  have hr' := neg_qabs_le_self z.re
  have hi' := neg_qabs_le_self z.im
  unfold normBound at h
  grind only

structure Node where
  direction : QComplex
  unit : normSq direction = 1
  weight : QComplex

abbrev Rule := List Node

def mass : Rule → Rat
  | [] => 0
  | p :: ps => normBound p.weight + mass ps

theorem mass_nonneg (ps : Rule) : 0 ≤ mass ps := by
  induction ps with
  | nil => exact Rat.le_refl
  | cons p ps ih => exact Rat.add_nonneg (l1_nonneg _) ih

def cauchySample (ps : Rule) (z : QComplex) : QComplex :=
  ps.foldr (fun p acc => add (mul p.weight (kernel (mul z p.direction))) acc) zero

def polynomialSample (ps : Rule) (z : QComplex) (N : Nat) : QComplex :=
  ps.foldr (fun p acc => add (mul p.weight (geometric (mul z p.direction) N)) acc) zero

/-- The Cauchy moment, independent of the evaluation point. -/
def coefficientSample (ps : Rule) (k : Nat) : QComplex :=
  ps.foldr (fun p acc => add (mul p.weight (natPow p.direction k)) acc) zero

def powerPrefix (a : Nat → QComplex) (z : QComplex) : Nat → QComplex
  | 0 => zero
  | n+1 => add (powerPrefix a z n) (mul (a n) (natPow z n))

theorem geometric_succ (z : QComplex) (n : Nat) :
    geometric z (n+1) = add (geometric z n) (natPow z n) := by
  induction n with
  | zero =>
      simp only [geometric, natPow, mul_zero, add_zero_cert, zero_add_cert]
  | succ n ih =>
      change add one (mul z (geometric z (n+1))) =
        add (add one (mul z (geometric z n))) (mul (natPow z n) z)
      rw [ih]
      simp only [add, mul, QComplex.mk.injEq]
      constructor <;> grind only

theorem polynomialSample_zero (ps : Rule) (z : QComplex) : polynomialSample ps z 0 = zero := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change add (mul p.weight zero) (polynomialSample ps z 0) = zero
      rw [ih, mul_zero, add_zero_cert]

theorem polynomialSample_succ (ps : Rule) (z : QComplex) (n : Nat) :
    polynomialSample ps z (n+1) =
      add (polynomialSample ps z n) (mul (coefficientSample ps n) (natPow z n)) := by
  induction ps with
  | nil =>
      change zero = add zero (mul zero (natPow z n))
      rw [zero_mul, add_zero_cert]
  | cons p ps ih =>
      change add (mul p.weight (geometric (mul z p.direction) (n+1)))
          (polynomialSample ps z (n+1)) =
        add (add (mul p.weight (geometric (mul z p.direction) n)) (polynomialSample ps z n))
          (mul (add (mul p.weight (natPow p.direction n)) (coefficientSample ps n)) (natPow z n))
      rw [geometric_succ, natPow_mul, ih]
      simp only [add, mul, QComplex.mk.injEq]
      constructor <;> grind only

/-- These are actual finite power-series prefixes, with Cauchy moment coefficients. -/
theorem polynomialSample_eq_prefix (ps : Rule) (z : QComplex) (N : Nat) :
    polynomialSample ps z N = powerPrefix (coefficientSample ps) z N := by
  induction N with
  | zero => exact polynomialSample_zero ps z
  | succ N ih => rw [polynomialSample_succ, powerPrefix, ih]

theorem rule_remainder {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) (ps : Rule) (N : Nat) :
    normBound (sub (cauchySample ps z) (polynomialSample ps z N)) ≤
      mass ps * (2 * (r^N * (1-r)⁻¹)) := by
  have ht : 0 ≤ r^N * (1-r)⁻¹ :=
    Rat.mul_nonneg (Rat.pow_nonneg hr) (Rat.le_of_lt ((Rat.inv_pos).2 (by grind)))
  induction ps with
  | nil => simp [cauchySample, polynomialSample, mass, normBound, sub, zero, add, neg, qabs, Rat.add_zero]
  | cons p ps ih =>
      have hu : InDisk (mul z p.direction) r := by
        unfold InDisk
        rw [normSq_mul, p.unit, Rat.mul_one]
        exact hz
      have he := kernel_remainder_coordinates hr hr1 hu N
      have hl : normBound (sub (kernel (mul z p.direction)) (geometric (mul z p.direction) N)) ≤
          2*(r^N*(1-r)⁻¹) := by
        have hre := qabs_le_of_neg_le_le he.1 he.2.1
        have him := qabs_le_of_neg_le_le he.2.2.1 he.2.2.2
        unfold normBound
        grind only
      have hmul := Rat.le_trans (l1_mul p.weight _)
        (Rat.mul_le_mul_of_nonneg_left hl (l1_nonneg _))
      have hsplit : sub (cauchySample (p::ps) z) (polynomialSample (p::ps) z N) =
          add (mul p.weight (sub (kernel (mul z p.direction)) (geometric (mul z p.direction) N)))
            (sub (cauchySample ps z) (polynomialSample ps z N)) := by
        simp only [cauchySample, polynomialSample, List.foldr_cons, sub, add, neg, mul, QComplex.mk.injEq]
        constructor <;> grind only
      rw [hsplit]
      have hs := l1_add (mul p.weight (sub (kernel (mul z p.direction))
        (geometric (mul z p.direction) N))) (sub (cauchySample ps z) (polynomialSample ps z N))
      change _ ≤ (normBound p.weight + mass ps) * _
      grind only

/-- A quantitative Cauchy integral formula on the normalized unit disk.
`encloses` concerns only the Cauchy kernel, not Taylor sums or derivatives.
The independently given function may have non-rational values. -/
structure Representation (f : QComplex → ComplexRaw) where
  rules : Nat → Rule
  massBound : Rat
  mass_nonneg : 0 ≤ massBound
  mass_le : ∀ n, mass (rules n) ≤ massBound
  quadratureBound : Rat → Rat
  quadrature_nonneg : ∀ r, 0 ≤ quadratureBound r
  valid : ∀ z r, 0 ≤ r → r < 1 → InDisk z r → (f z).Valid
  encloses : ∀ z r, 0 ≤ r → r < 1 → InDisk z r → ∀ n,
    ((f z).compute n).NestedIn
      (QBox.expand (QBox.point (cauchySample (rules n) z)) (rate (quadratureBound r) n))

namespace Representation

def errorConstant {f : QComplex → ComplexRaw} (c : Representation f) (r : Rat) : Rat :=
  c.quadratureBound r + 2*c.massBound*((1-r)⁻¹*(1-r)⁻¹)

theorem errorConstant_nonneg {f : QComplex → ComplexRaw} (c : Representation f) (r : Rat) :
    0 ≤ c.errorConstant r := by
  exact Rat.add_nonneg (c.quadrature_nonneg r)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) c.mass_nonneg) (rat_square_nonneg_basic _))

theorem polynomial_encloses {f : QComplex → ComplexRaw} (c : Representation f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) (n : Nat) :
    ((f z).compute n).NestedIn
      (QBox.expand (QBox.point (polynomialSample (c.rules n) z n)) (rate (c.errorConstant r) n)) := by
  have he := c.encloses z r hr hr1 hz n
  have hb := rule_remainder hr hr1 hz (c.rules n) n
  have hi : 0 ≤ (1-r)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (by grind))
  have ht : 0 ≤ 2*(r^n*(1-r)⁻¹) := Rat.mul_nonneg (by decide) (Rat.mul_nonneg (Rat.pow_nonneg hr) hi)
  have hm := Rat.mul_le_mul_of_nonneg_right (c.mass_le n) ht
  have hp := Rat.mul_le_mul_of_nonneg_right (power_nat_bound hr hr1 n) hi
  have hmp := Rat.mul_le_mul_of_nonneg_left hp (Rat.mul_nonneg (by decide : (0:Rat)≤2) c.mass_nonneg)
  have hc := l1_coordinates (Rat.le_trans hb hm)
  simp only [QBox.NestedIn, QBox.expand, QBox.point, QComplex.le_def, sub, add, neg,
    errorConstant, rate, Rat.div_def] at *
  constructor <;> constructor <;> grind only

/-- The runtime evaluates finite coefficient prefixes and intersects their
certified boxes. It does not evaluate the function `f`. -/
def series {f : QComplex → ComplexRaw} (c : Representation f) (z : QComplex) (r : Rat) : ComplexRaw :=
  CertifiedComplexApproximation.raw (fun n => polynomialSample (c.rules n) z n) (c.errorConstant r)

theorem series_valid {f : QComplex → ComplexRaw} (c : Representation f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    (c.series z r).Valid :=
  CertifiedComplexApproximation.valid (c.errorConstant_nonneg r)
    (c.valid z r hr hr1 hz) (c.polynomial_encloses hr hr1 hz)

/-- Exact equality of computations on every smaller Euclidean disk.
This is conditional on a certified Cauchy representation. -/
theorem eq_series {f : QComplex → ComplexRaw} (c : Representation f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    (f z).Equiv (c.series z r) :=
  ComplexRaw.equiv_symm (CertifiedComplexApproximation.equiv_anchor
    (c.errorConstant_nonneg r) (c.valid z r hr hr1 hz) (c.polynomial_encloses hr hr1 hz))

theorem realPart_eq_series {f : QComplex → ComplexRaw} (c : Representation f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    (f z).realPart.Equiv (c.series z r).realPart :=
  ComplexRaw.realPart_equiv (c.eq_series hr hr1 hz)

theorem imagPart_eq_series {f : QComplex → ComplexRaw} (c : Representation f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    (f z).imagPart.Equiv (c.series z r).imagPart :=
  ComplexRaw.imagPart_equiv (c.eq_series hr hr1 hz)

end Representation
end ComputableAnalysis.CauchyTaylor
