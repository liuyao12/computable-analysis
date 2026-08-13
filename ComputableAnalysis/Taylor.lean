import ComputableAnalysis.Calculus
import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.Series

/-!
# Taylor expansions by iterated FTC

Taylor's formula is meant to be generated from repeated definite-integral FTC
steps:

`F(x) = F(a) + integral_a^x F'(t) dt`,

then the same statement is applied to `F'`, then to `F''`, and so on.  This
file records that shape without introducing completed real numbers or
standalone indefinite-integral objects.
-/

namespace ComputableAnalysis

namespace Taylor

/-- One definite-integral FTC step, stated as equality of computable real
numbers.

The integral is over the concrete interval `[a,b]`; equality means
`RealRaw.Equiv`, i.e. interval overlap at every requested precision. -/
def FTCStepAt (F dF : RealFunRaw) (a b : Rat) : Prop :=
  Exists fun c : Integral.Construction dF a b =>
  Exists fun hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b) =>
    DefiniteIntegralEqualsEndpointDifference F dF a b c hendpoint

/-- The data needed to expand by iterated FTC from a base point `a`.

`F 0` is the original function, `F 1` its derivative, `F 2` the next
derivative, etc.  The field says that every adjacent pair has the definite
FTC equality from `a` to any rational endpoint needed by a nested integral. -/
def IteratedFTCChain (F : Nat -> RealFunRaw) (a : Rat) (order : Nat) : Prop :=
  forall k, k < order -> forall x, FTCStepAt (F k) (F (k + 1)) a x

/-- Coefficient-level shadow of one iterated-FTC step from `0`.

Given the coefficient stream of `F'` and the value `F(0)`, this constructs the
coefficient stream of `F`.  The theorem
`FormalPowerSeries.coeffsFromDerivativeAtZero_hasFormalDerivative` proves that
differentiating the constructed stream really returns the supplied derivative
stream. -/
def coeffStepFromDerivativeAtZero :=
  FormalPowerSeries.coeffsFromDerivativeAtZero

/-- The rational function that drives the arctangent Taylor route, certified on
any rational interval by the denominator-apartness proof
`1 <= |1+x^2|`. -/
def arctanKernelOnInterval (a b : Rat) : FunctionOnInterval :=
  RatFun.oneOverOnePlusSquareOnInterval a b

def ArctanKernelRegularOnEveryInterval : Type :=
  forall a b, RatFun.DenominatorApartOnInterval RatFun.oneOverOnePlusSquare a b

def arctanKernel_regular_on_every_interval :
    ArctanKernelRegularOnEveryInterval :=
  fun a b => RatFun.oneOverOnePlusSquare_denominator_apart_on_interval a b

namespace ArctanKernel

/-- Finite alternating geometric sum
`1 - u + u^2 - ... + (-u)^n`. -/
def altGeomPartial (u : Rat) : Nat -> Rat
  | 0 => 1
  | n + 1 => altGeomPartial u n + (-u) ^ (n + 1)

def remainderNumerator (u : Rat) (n : Nat) : Rat :=
  (-u) ^ (n + 1)

/-- Finite division identity before dividing by `1+u`:
`(1+u) * (1 - u + ... + (-u)^n) + (-u)^(n+1) = 1`. -/
theorem one_add_mul_altGeomPartial_add_remainder (u : Rat) (n : Nat) :
    (1 + u) * altGeomPartial u n + remainderNumerator u n = 1 := by
  induction n with
  | zero =>
      unfold altGeomPartial remainderNumerator
      rw [Rat.pow_succ]
      simp
      grind [Rat.mul_assoc, Rat.mul_comm]
  | succ n ih =>
      unfold altGeomPartial remainderNumerator
      change (1 + u) * (altGeomPartial u n + (-u) ^ (n + 1)) +
          (-u) ^ (n + 1 + 1) = 1
      have htail :
          (1 + u) * ((-u) ^ (n + 1)) + (-u) ^ (n + 1 + 1) =
            (-u) ^ (n + 1) := by
        rw [Rat.pow_succ]
        grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
      calc
        (1 + u) * (altGeomPartial u n + (-u) ^ (n + 1)) +
            (-u) ^ (n + 1 + 1)
            = (1 + u) * altGeomPartial u n +
                ((1 + u) * ((-u) ^ (n + 1)) + (-u) ^ (n + 1 + 1)) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                Rat.mul_assoc, Rat.mul_comm]
        _ = (1 + u) * altGeomPartial u n + remainderNumerator u n := by
              rw [htail]
              rfl
        _ = 1 := ih

def kernelPartial (x : Rat) (n : Nat) : Rat :=
  altGeomPartial (x * x) n

def kernelRemainder (x : Rat) (n : Nat) : Rat :=
  remainderNumerator (x * x) n / (1 + x * x)

/-- Integral over `[0,1]` of the `j`-th monomial in the arctangent-kernel
finite expansion. -/
def kernelTermIntegralAtOne (j : Nat) : Rat :=
  (-1 : Rat) ^ j / (2 * (j : Rat) + 1)

/-- Integral over `[p,r]` of the `j`-th monomial in the arctangent-kernel
finite expansion. -/
def kernelTermIntegralBetween (p r : Rat) (j : Nat) : Rat :=
  (-1 : Rat) ^ j * (r ^ (2 * j + 1) - p ^ (2 * j + 1)) /
    (2 * (j : Rat) + 1)

/-- Integral over `[0,1]` of the finite arctangent-kernel truncation
`1 - x^2 + x^4 - ... + (-x^2)^n`. -/
def kernelPartialIntegralAtOne : Nat -> Rat
  | 0 => 1
  | n + 1 => kernelPartialIntegralAtOne n + kernelTermIntegralAtOne (n + 1)

/-- Integral over `[p,r]` of the finite arctangent-kernel truncation
`1 - x^2 + x^4 - ... + (-x^2)^n`. -/
def kernelPartialIntegralBetween (p r : Rat) : Nat -> Rat
  | 0 => r - p
  | n + 1 => kernelPartialIntegralBetween p r n +
      kernelTermIntegralBetween p r (n + 1)

private theorem neg_one_pow_even (n : Nat) :
    (-1 : Rat) ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      rw [Rat.pow_succ, Rat.pow_succ, ih]
      native_decide

private theorem neg_one_pow_odd (n : Nat) :
    (-1 : Rat) ^ (2 * n + 1) = -1 := by
  rw [show 2 * n + 1 = 2 * n + 1 by omega]
  rw [Rat.pow_succ, neg_one_pow_even]
  native_decide

/-- Advancing from an even arctangent-kernel truncation to the next odd one
subtracts the next Leibniz denominator. -/
theorem kernelPartialIntegralAtOne_odd_succ (n : Nat) :
    kernelPartialIntegralAtOne (2 * n + 1) =
      kernelPartialIntegralAtOne (2 * n) - 1 / (4 * (n : Rat) + 3) := by
  rw [show 2 * n + 1 = 2 * n + 1 by omega]
  simp [kernelPartialIntegralAtOne, kernelTermIntegralAtOne]
  rw [neg_one_pow_odd]
  have hden : 2 * (2 * (n : Rat) + 1) + 1 = 4 * (n : Rat) + 3 := by
    grind
  rw [hden]
  grind [Rat.sub_eq_add_neg]

/-- Advancing from an odd arctangent-kernel truncation to the next even one
adds the next Leibniz denominator. -/
theorem kernelPartialIntegralAtOne_even_succ (n : Nat) :
    kernelPartialIntegralAtOne (2 * n + 2) =
      kernelPartialIntegralAtOne (2 * n + 1) + 1 / (4 * (n : Rat) + 5) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp [kernelPartialIntegralAtOne, kernelTermIntegralAtOne]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  rw [neg_one_pow_even]
  have hden : 2 * (2 * (n : Rat) + 1 + 1) + 1 = 4 * (n : Rat) + 5 := by
    grind
  rw [hden]

/-- Advancing from an even kernel truncation to the next odd truncation over
`[0,y]` subtracts its next finite arctangent-series term. -/
theorem kernelPartialIntegralBetween_zero_odd_succ (y : Rat) (n : Nat) :
    kernelPartialIntegralBetween 0 y (2 * n + 1) =
      kernelPartialIntegralBetween 0 y (2 * n) -
        y ^ (4 * n + 3) / (4 * (n : Rat) + 3) := by
  rw [show 2 * n + 1 = 2 * n + 1 by omega]
  simp [kernelPartialIntegralBetween, kernelTermIntegralBetween]
  rw [neg_one_pow_odd]
  have hpow : 2 * (2 * n + 1) + 1 = 4 * n + 3 := by omega
  have hden : 2 * (2 * (n : Rat) + 1) + 1 = 4 * (n : Rat) + 3 := by
    grind
  rw [hpow, hden]
  grind [Rat.sub_eq_add_neg]

/-- Advancing from an odd kernel truncation to the next even truncation over
`[0,y]` adds its next finite arctangent-series term. -/
theorem kernelPartialIntegralBetween_zero_even_succ (y : Rat) (n : Nat) :
    kernelPartialIntegralBetween 0 y (2 * n + 2) =
      kernelPartialIntegralBetween 0 y (2 * n + 1) +
        y ^ (4 * n + 5) / (4 * (n : Rat) + 5) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp [kernelPartialIntegralBetween, kernelTermIntegralBetween]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  rw [neg_one_pow_even]
  have hpow : 2 * (2 * (n + 1)) + 1 = 4 * n + 5 := by omega
  have hden : 2 * (2 * (n : Rat) + 1 + 1) + 1 = 4 * (n : Rat) + 5 := by
    grind
  rw [hpow, hden]
  simp
  grind [Rat.sub_eq_add_neg]

/-! On the half interval, the consecutive even/odd primitive prefixes differ
by exactly the omitted alternating monomial.  This is the finite enclosure
width used by the computable arctangent primitive; it is not an attained
integral or an infinite-series limit. -/

theorem kernelPartialIntegralBetween_half_even_odd_gap (n : Nat) :
    kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n + 1) -
        kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n) =
      -((1 : Rat) / 2) ^ (4 * n + 3) / (4 * (n : Rat) + 3) := by
  have h := kernelPartialIntegralBetween_zero_odd_succ (1 / 2) n
  grind [Rat.sub_eq_add_neg]

theorem kernelPartialIntegralBetween_half_even_odd_gap_width (n : Nat) :
    qabs (kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n + 1) -
        kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n)) =
      ((1 : Rat) / 2) ^ (4 * n + 3) / (4 * (n : Rat) + 3) := by
  rw [kernelPartialIntegralBetween_half_even_odd_gap]
  have hpow : 0 <= ((1 : Rat) / 2) ^ (4 * n + 3) := by
    exact Rat.pow_nonneg (by native_decide)
  have hden : 0 < (4 * (n : Rat) + 3) := by
    have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
    grind
  have hneg : -(1 / 2) ^ (4 * n + 3) / (4 * (n : Rat) + 3) <= 0 := by
    rw [Rat.div_def]
    have hmul := Rat.mul_nonneg hpow
      (Rat.le_of_lt ((Rat.inv_pos).2 hden))
    grind
  rw [qabs_eq_neg_of_nonpos hneg]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem kernelPartialIntegralBetween_half_even_odd_gap_le_one_div
    (n : Nat) :
    qabs (kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n + 1) -
        kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n)) <=
      1 / (((4 * n + 3 : Nat) : Rat)) := by
  rw [kernelPartialIntegralBetween_half_even_odd_gap_width]
  have hpow : ((1 : Rat) / 2) ^ (4 * n + 3) <= 1 := by
    have hbase : ((1 : Rat) / 2) <= 1 := by native_decide
    have hnonneg : 0 <= ((1 : Rat) / 2) := by native_decide
    induction 4 * n + 3 with
    | zero => simp
    | succ k ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ k * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ k * 1 :=
            Rat.mul_le_mul_of_nonneg_left hbase (Rat.pow_nonneg hnonneg)
          _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
          _ <= 1 := ih
  have hbound := Rat.mul_le_mul_of_nonneg_right hpow
    (Rat.le_of_lt ((Rat.inv_pos).2 (by
      have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
      have : 0 < (4 : Rat) * (n : Rat) + 3 := by grind
      exact this)))
  simpa [Rat.div_def, Rat.mul_one] using hbound

theorem kernelPartialIntegralBetween_half_alternating_enclosure
    (n : Nat) :
    kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n + 1) <=
        kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n) /\
      kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n) -
          kernelPartialIntegralBetween 0 ((1 : Rat) / 2) (2 * n + 1) <=
        1 / (((4 * n + 3 : Nat) : Rat)) := by
  constructor
  · have hgap := kernelPartialIntegralBetween_half_even_odd_gap n
    have hpow : 0 <= ((1 : Rat) / 2) ^ (4 * n + 3) := by
      exact Rat.pow_nonneg (by native_decide)
    have hden : 0 < (4 * (n : Rat) + 3) := by
      have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
      grind
    have hmul := Rat.mul_nonneg hpow
      (Rat.le_of_lt ((Rat.inv_pos).2 hden))
    have hnonpos :
        -((1 : Rat) / 2) ^ (4 * n + 3) / (4 * (n : Rat) + 3) <= 0 := by
      rw [Rat.div_def]
      grind
    grind [Rat.sub_eq_add_neg]
  · have hwidth := kernelPartialIntegralBetween_half_even_odd_gap_le_one_div n
    rw [qabs_eq_neg_of_nonpos] at hwidth
    · grind
    · have hgap := kernelPartialIntegralBetween_half_even_odd_gap n
      have hpow : 0 <= ((1 : Rat) / 2) ^ (4 * n + 3) := by
        exact Rat.pow_nonneg (by native_decide)
      have hden : 0 < (4 * (n : Rat) + 3) := by
        have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
        grind
      rw [hgap, Rat.div_def]
      have hmul := Rat.mul_nonneg hpow
        (Rat.le_of_lt ((Rat.inv_pos).2 hden))
      grind

private theorem one_pow_rat (m : Nat) : (1 : Rat) ^ m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Rat.pow_succ, ih]
      grind

private theorem zero_pow_rat_succ (m : Nat) : (0 : Rat) ^ (m + 1) = 0 := by
  rw [Rat.pow_succ]
  simp

theorem kernelTermIntegralBetween_zero_one (j : Nat) :
    kernelTermIntegralBetween 0 1 j = kernelTermIntegralAtOne j := by
  unfold kernelTermIntegralBetween kernelTermIntegralAtOne
  rw [one_pow_rat]
  rw [show 2 * j + 1 = 2 * j + 1 by omega]
  rw [zero_pow_rat_succ]
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem kernelPartialIntegralBetween_zero_one (n : Nat) :
    kernelPartialIntegralBetween 0 1 n = kernelPartialIntegralAtOne n := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      simp [kernelPartialIntegralBetween, kernelPartialIntegralAtOne]
      rw [ih, kernelTermIntegralBetween_zero_one]

/-- Finite monomial integrals add across an intermediate point. -/
theorem kernelTermIntegralBetween_split (p q r : Rat) (j : Nat) :
    kernelTermIntegralBetween p r j =
      kernelTermIntegralBetween p q j +
        kernelTermIntegralBetween q r j := by
  unfold kernelTermIntegralBetween
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Finite arctangent-kernel truncation integrals add across an intermediate
point. -/
theorem kernelPartialIntegralBetween_split (p q r : Rat) (n : Nat) :
    kernelPartialIntegralBetween p r n =
      kernelPartialIntegralBetween p q n +
        kernelPartialIntegralBetween q r n := by
  induction n with
  | zero =>
      simp [kernelPartialIntegralBetween]
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      simp [kernelPartialIntegralBetween]
      rw [ih, kernelTermIntegralBetween_split p q r (n + 1)]
      grind [Rat.add_assoc, Rat.add_comm]

theorem pow_mono_nonneg
    {p r : Rat} (hp : 0 <= p) (hpr : p <= r) (n : Nat) :
    p ^ n <= r ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hr : 0 <= r := Rat.le_trans hp hpr
      calc
        p ^ n * p <= r ^ n * p :=
          Rat.mul_le_mul_of_nonneg_right ih hp
        _ <= r ^ n * r :=
          Rat.mul_le_mul_of_nonneg_left hpr (Rat.pow_nonneg hr)

/-- The finite geometric factor in the difference of two powers.

It is defined by a recurrence instead of importing a polynomial factorization.
This is the algebraic core of the rational Riemann-error estimates used for
finite kernel polynomials. -/
def powDifferenceFactor (p r : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => r ^ n + p * powDifferenceFactor p r n

/-- Difference of powers factored into a cell length and a finite rational
geometric sum. -/
theorem pow_sub_pow_eq_sub_mul_powDifferenceFactor
    (p r : Rat) (n : Nat) :
    r ^ n - p ^ n = (r - p) * powDifferenceFactor p r n := by
  induction n with
  | zero =>
      simp [powDifferenceFactor]
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ, powDifferenceFactor]
      calc
        r ^ n * r - p ^ n * p =
            (r - p) * r ^ n + p * (r ^ n - p ^ n) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ = (r - p) * r ^ n +
              p * ((r - p) * powDifferenceFactor p r n) := by
              rw [ih]
        _ = (r - p) * (r ^ n + p * powDifferenceFactor p r n) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- A nonnegative rational in the unit interval stays below one under every
natural power. -/
theorem pow_le_one_of_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    x ^ n <= 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Rat.pow_succ]
      calc
        x ^ n * x <= x ^ n * 1 :=
          Rat.mul_le_mul_of_nonneg_left hx1 (Rat.pow_nonneg hx0)
        _ = x ^ n := by rw [Rat.mul_one]
        _ <= 1 := ih

/-- The finite difference factor is nonnegative when both endpoints are. -/
theorem powDifferenceFactor_nonneg
    {p r : Rat} (hp0 : 0 <= p) (hr0 : 0 <= r) (n : Nat) :
    0 <= powDifferenceFactor p r n := by
  induction n with
  | zero =>
      simp [powDifferenceFactor]
  | succ n ih =>
      rw [powDifferenceFactor]
      exact Rat.add_nonneg (Rat.pow_nonneg hr0) (Rat.mul_nonneg hp0 ih)

/-- On the unit interval, the finite difference factor for the n-th power is
at most n.  This deliberately elementary estimate is enough to make all
finite Riemann-error constants explicit. -/
theorem powDifferenceFactor_le_nat_of_unit
    {p r : Rat}
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (n : Nat) :
    powDifferenceFactor p r n <= (n : Rat) := by
  induction n with
  | zero =>
      simp [powDifferenceFactor]
  | succ n ih =>
      rw [powDifferenceFactor]
      calc
        r ^ n + p * powDifferenceFactor p r n
            <= 1 + p * powDifferenceFactor p r n :=
          (Rat.add_le_add_right).2
            (pow_le_one_of_unit hr0 hr1 n)
        _ <= 1 + 1 * powDifferenceFactor p r n :=
          (Rat.add_le_add_left).2
            (Rat.mul_le_mul_of_nonneg_right hp1
              (powDifferenceFactor_nonneg hp0 hr0 n))
        _ = 1 + powDifferenceFactor p r n := by
          rw [Rat.one_mul]
        _ <= 1 + (n : Rat) := (Rat.add_le_add_left).2 ih
        _ = ((n + 1 : Nat) : Rat) := by
          exact_mod_cast (by omega : 1 + n = n + 1)

/-- The geometric difference factor is bracketed by its endpoint powers.
Equivalently, its average lies between the endpoint values of the monomial.
This is the exact finite substitute for monotonicity of a monomial integral. -/
theorem powDifferenceFactor_average_bounds
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (n : Nat) :
    ((n + 1 : Nat) : Rat) * p ^ n <= powDifferenceFactor p r (n + 1) /\
      powDifferenceFactor p r (n + 1) <= ((n + 1 : Nat) : Rat) * r ^ n := by
  induction n with
  | zero =>
      constructor <;> simp [powDifferenceFactor] <;>
        grind [Rat.add_zero, Rat.zero_add]
  | succ n ih =>
      rcases ih with ⟨ihlow, ihhigh⟩
      have hr0 : 0 <= r := Rat.le_trans hp0 hpr
      have hfactor0 :
          0 <= powDifferenceFactor p r (n + 1) :=
        powDifferenceFactor_nonneg hp0 hr0 (n + 1)
      have hpowlow : p ^ (n + 1) <= r ^ (n + 1) :=
        pow_mono_nonneg hp0 hpr (n + 1)
      have hmul_low :
          p * (((n + 1 : Nat) : Rat) * p ^ n) <=
            p * powDifferenceFactor p r (n + 1) :=
        Rat.mul_le_mul_of_nonneg_left ihlow hp0
      have hmul_middle :
          p * powDifferenceFactor p r (n + 1) <=
            r * powDifferenceFactor p r (n + 1) :=
        Rat.mul_le_mul_of_nonneg_right hpr hfactor0
      have hmul_high :
          r * powDifferenceFactor p r (n + 1) <=
            r * (((n + 1 : Nat) : Rat) * r ^ n) :=
        Rat.mul_le_mul_of_nonneg_left ihhigh hr0
      constructor
      · change
          ((n + 1 + 1 : Nat) : Rat) * p ^ (n + 1) <=
            r ^ (n + 1) + p * powDifferenceFactor p r (n + 1)
        calc
          ((n + 1 + 1 : Nat) : Rat) * p ^ (n + 1)
              = p ^ (n + 1) +
                  p * (((n + 1 : Nat) : Rat) * p ^ n) := by
                    rw [Rat.pow_succ]
                    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
                      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
          _ <= r ^ (n + 1) +
                p * (((n + 1 : Nat) : Rat) * p ^ n) :=
              (Rat.add_le_add_right).2 hpowlow
          _ <= r ^ (n + 1) +
                p * powDifferenceFactor p r (n + 1) :=
              (Rat.add_le_add_left).2 hmul_low
      · change
          r ^ (n + 1) + p * powDifferenceFactor p r (n + 1) <=
            ((n + 1 + 1 : Nat) : Rat) * r ^ (n + 1)
        calc
          r ^ (n + 1) + p * powDifferenceFactor p r (n + 1)
              <= r ^ (n + 1) +
                  r * powDifferenceFactor p r (n + 1) :=
              (Rat.add_le_add_left).2 hmul_middle
          _ <= r ^ (n + 1) +
                r * (((n + 1 : Nat) : Rat) * r ^ n) :=
              (Rat.add_le_add_left).2 hmul_high
          _ = ((n + 1 + 1 : Nat) : Rat) * r ^ (n + 1) := by
              rw [Rat.pow_succ]
              grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
                Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The exact rational primitive of a nonnegative monomial lies between its
left and right endpoint rectangles.  This is proved only from the finite
difference-of-powers identity, with no appeal to completed-real integration. -/
theorem monomialIntegralBetween_endpoint_bounds
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (k : Nat) :
    (r - p) * p ^ k <=
        (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) /\
      (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) <=
        (r - p) * r ^ k := by
  let N : Rat := ((k + 1 : Nat) : Rat)
  have hNpos : 0 < N := by
    dsimp [N]
    exact (Rat.natCast_pos).2 (by omega : 0 < k + 1)
  have hd0 : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  have hfactor := powDifferenceFactor_average_bounds hp0 hpr k
  have hpow := pow_sub_pow_eq_sub_mul_powDifferenceFactor p r (k + 1)
  change
    (r - p) * p ^ k <= (r ^ (k + 1) - p ^ (k + 1)) / N /\
      (r ^ (k + 1) - p ^ (k + 1)) / N <= (r - p) * r ^ k
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := N)
    · calc
        ((r - p) * p ^ k) * N =
            (r - p) * (N * p ^ k) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (r - p) * powDifferenceFactor p r (k + 1) :=
            Rat.mul_le_mul_of_nonneg_left hfactor.1 hd0
        _ = r ^ (k + 1) - p ^ (k + 1) := by
            rw [← hpow]
        _ = ((r ^ (k + 1) - p ^ (k + 1)) / N) * N := by
            rw [Rat.div_def]
            have hNne : N ≠ 0 := Rat.ne_of_gt hNpos
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hNpos
  · apply Rat.le_of_mul_le_mul_right (c := N)
    · calc
        ((r ^ (k + 1) - p ^ (k + 1)) / N) * N =
            r ^ (k + 1) - p ^ (k + 1) := by
              rw [Rat.div_def]
              have hNne : N ≠ 0 := Rat.ne_of_gt hNpos
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ = (r - p) * powDifferenceFactor p r (k + 1) := hpow
        _ <= (r - p) * (N * r ^ k) :=
            Rat.mul_le_mul_of_nonneg_left hfactor.2 hd0
        _ = ((r - p) * r ^ k) * N := by
            grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hNpos

/-- On a rational cell in the unit interval, each endpoint rectangle for the
monomial x^k differs from its exact primitive by at most
k times the squared cell length. -/
theorem monomialIntegralBetween_endpoint_error_le
    {p r : Rat}
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hpr : p <= r) (hr1 : r <= 1)
    (k : Nat) :
    0 <= (r - p) * r ^ k -
          (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) /\
      (r - p) * r ^ k -
          (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) <=
        (k : Rat) * (r - p) * (r - p) /\
      0 <= (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) -
          (r - p) * p ^ k /\
      (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) -
          (r - p) * p ^ k <=
        (k : Rat) * (r - p) * (r - p) := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hd0 : 0 <= r - p := by
    grind [Rat.sub_eq_add_neg]
  have hbracket := monomialIntegralBetween_endpoint_bounds hp0 hpr k
  have hfactor := powDifferenceFactor_le_nat_of_unit hp0 hp1 hr0 hr1 k
  have hpow := pow_sub_pow_eq_sub_mul_powDifferenceFactor p r k
  have hpowerGap :
      r ^ k - p ^ k <= (r - p) * (k : Rat) := by
    calc
      r ^ k - p ^ k =
          (r - p) * powDifferenceFactor p r k := hpow
      _ <= (r - p) * (k : Rat) :=
          Rat.mul_le_mul_of_nonneg_left hfactor hd0
  have hcellGap :
      (r - p) * (r ^ k - p ^ k) <=
        (k : Rat) * (r - p) * (r - p) := by
    calc
      (r - p) * (r ^ k - p ^ k)
          <= (r - p) * ((r - p) * (k : Rat)) :=
        Rat.mul_le_mul_of_nonneg_left hpowerGap hd0
      _ = (k : Rat) * (r - p) * (r - p) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · calc
      (r - p) * r ^ k -
          (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat))
          <= (r - p) * r ^ k - (r - p) * p ^ k := by
            grind [Rat.sub_eq_add_neg]
      _ = (r - p) * (r ^ k - p ^ k) := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= (k : Rat) * (r - p) * (r - p) := hcellGap
  constructor
  · grind [Rat.sub_eq_add_neg]
  · calc
      (r ^ (k + 1) - p ^ (k + 1)) / (((k + 1 : Nat) : Rat)) -
          (r - p) * p ^ k
          <= (r - p) * r ^ k - (r - p) * p ^ k := by
            grind [Rat.sub_eq_add_neg]
      _ = (r - p) * (r ^ k - p ^ k) := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= (k : Rat) * (r - p) * (r - p) := hcellGap

private theorem kernelTermDen_pos (j : Nat) :
    0 < 2 * (j : Rat) + 1 := by
  have hj : 0 <= (j : Rat) := Rat.natCast_nonneg
  grind

theorem kernelTermIntegralBetween_nonneg_even
    {p r : Rat} (hp : 0 <= p) (hpr : p <= r) (n : Nat) :
    0 <= kernelTermIntegralBetween p r (2 * n) := by
  have hpow :
      p ^ (2 * (2 * n) + 1) <= r ^ (2 * (2 * n) + 1) :=
    pow_mono_nonneg hp hpr _
  have hdiff :
      0 <= r ^ (2 * (2 * n) + 1) - p ^ (2 * (2 * n) + 1) := by
    grind [Rat.sub_eq_add_neg]
  have hdenpos : 0 < 2 * ((2 * n : Nat) : Rat) + 1 :=
    kernelTermDen_pos (2 * n)
  unfold kernelTermIntegralBetween
  rw [neg_one_pow_even]
  rw [Rat.div_def]
  simpa [Rat.mul_assoc, Rat.mul_comm] using
    Rat.mul_nonneg hdiff (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

private theorem rat_mul_nonpos_of_nonpos_of_nonneg'
    {a b : Rat} (ha : a <= 0) (hb : 0 <= b) :
    a * b <= 0 := by
  have h := Rat.mul_nonneg (by grind : 0 <= -a) hb
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem kernelTermIntegralBetween_nonpos_odd
    {p r : Rat} (hp : 0 <= p) (hpr : p <= r) (n : Nat) :
    kernelTermIntegralBetween p r (2 * n + 1) <= 0 := by
  have hpow :
      p ^ (2 * (2 * n + 1) + 1) <=
        r ^ (2 * (2 * n + 1) + 1) :=
    pow_mono_nonneg hp hpr _
  have hdiff :
      0 <= r ^ (2 * (2 * n + 1) + 1) -
        p ^ (2 * (2 * n + 1) + 1) := by
    grind [Rat.sub_eq_add_neg]
  have hdenpos : 0 < 2 * ((2 * n + 1 : Nat) : Rat) + 1 :=
    kernelTermDen_pos (2 * n + 1)
  have hnum :
      (-1 : Rat) *
          (r ^ (2 * (2 * n + 1) + 1) -
            p ^ (2 * (2 * n + 1) + 1)) <= 0 := by
    have h := Rat.mul_nonneg (by native_decide : (0 : Rat) <= 1) hdiff
    grind
  unfold kernelTermIntegralBetween
  rw [neg_one_pow_odd]
  rw [Rat.div_def]
  exact rat_mul_nonpos_of_nonpos_of_nonneg'
    hnum (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem kernelPartialIntegralBetween_odd_succ_le_even
    {p r : Rat} (hp : 0 <= p) (hpr : p <= r) (n : Nat) :
    kernelPartialIntegralBetween p r (2 * n + 1) <=
      kernelPartialIntegralBetween p r (2 * n) := by
  rw [show 2 * n + 1 = 2 * n + 1 by omega]
  simp [kernelPartialIntegralBetween]
  have hterm := kernelTermIntegralBetween_nonpos_odd hp hpr n
  grind

theorem kernelPartialIntegralBetween_odd_le_even_succ
    {p r : Rat} (hp : 0 <= p) (hpr : p <= r) (n : Nat) :
    kernelPartialIntegralBetween p r (2 * n + 1) <=
      kernelPartialIntegralBetween p r (2 * n + 2) := by
  rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega]
  simp [kernelPartialIntegralBetween]
  have hterm := kernelTermIntegralBetween_nonneg_even hp hpr (n + 1)
  grind

theorem qabs_le_of_between {r b : Rat}
    (hlo : -b <= r) (hhi : r <= b) :
    qabs r <= b := by
  unfold qabs
  by_cases hneg : r < 0
  · simp [hneg]
    grind
  · simp [hneg]
    exact hhi

theorem neg_pow_between_pow {u : Rat} (hu : 0 <= u) (m : Nat) :
    -(u ^ m) <= (-u) ^ m /\ (-u) ^ m <= u ^ m := by
  induction m with
  | zero =>
      simp
      native_decide
  | succ m ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hleft := Rat.mul_le_mul_of_nonneg_right ih.1 hu
      have hright := Rat.mul_le_mul_of_nonneg_right ih.2 hu
      constructor
      · -- lower bound follows from the upper bound at the previous stage
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg,
          Rat.mul_assoc, Rat.mul_comm]
      · -- upper bound follows from the lower bound at the previous stage
        grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg,
          Rat.mul_assoc, Rat.mul_comm]

private theorem neg_square_pow_eq_sign_mul_even_pow (r : Rat) (j : Nat) :
    (- (r * r)) ^ j = (-1 : Rat) ^ j * r ^ (2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
      rw [Rat.pow_succ, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) : a + c <= b + d := by
  grind

/-- The signed right-endpoint error of one arctangent-kernel monomial is
bounded in magnitude by its unsigned monomial error. -/
theorem signed_kernelTerm_rightRectangle_error_bound
    {p r : Rat}
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hpr : p <= r) (hr1 : r <= 1)
    (j : Nat) :
    -((2 * (j : Rat)) * (r - p) * (r - p)) <=
        (r - p) * (- (r * r)) ^ j - kernelTermIntegralBetween p r j /\
      (r - p) * (- (r * r)) ^ j - kernelTermIntegralBetween p r j <=
        (2 * (j : Rat)) * (r - p) * (r - p) := by
  have hmono := monomialIntegralBetween_endpoint_error_le hp0 hp1 hpr hr1 (2 * j)
  let D : Rat := (r - p) * r ^ (2 * j) -
    (r ^ (2 * j + 1) - p ^ (2 * j + 1)) / (((2 * j + 1 : Nat) : Rat))
  let E : Rat := (2 * (j : Rat)) * (r - p) * (r - p)
  have hD0 : 0 <= D := by
    dsimp [D]
    exact hmono.1
  have hDE : D <= E := by
    dsimp [D, E]
    simpa using hmono.2.1
  have hsign := neg_pow_between_pow (u := (1 : Rat)) (by native_decide) j
  have hsign' : -1 <= (-1 : Rat) ^ j /\ (-1 : Rat) ^ j <= 1 := by
    constructor
    · change -(1 : Rat) <= (-1 : Rat) ^ j
      calc
        -(1 : Rat) = -((1 : Rat) ^ j) := by rw [one_pow_rat]
        _ <= (-1 : Rat) ^ j := hsign.1
    · change (-1 : Rat) ^ j <= (1 : Rat)
      calc
        (-1 : Rat) ^ j <= (1 : Rat) ^ j := hsign.2
        _ = (1 : Rat) := one_pow_rat j
  have hnegD : -D <= (-1 : Rat) ^ j * D := by
    have h := Rat.mul_le_mul_of_nonneg_right hsign'.1 hD0
    simpa [Rat.neg_mul] using h
  have hsignD : (-1 : Rat) ^ j * D <= D := by
    simpa using Rat.mul_le_mul_of_nonneg_right hsign'.2 hD0
  have hterm :
      (r - p) * (- (r * r)) ^ j - kernelTermIntegralBetween p r j =
        (-1 : Rat) ^ j * D := by
    unfold kernelTermIntegralBetween
    rw [neg_square_pow_eq_sign_mul_even_pow]
    dsimp [D]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hterm]
  constructor
  · calc
      -((2 * (j : Rat)) * (r - p) * (r - p)) = -E := by rfl
      _ <= -D := by grind
      _ <= (-1 : Rat) ^ j * D := hnegD
  · calc
      (-1 : Rat) ^ j * D <= D := hsignD
      _ <= E := hDE
      _ = (2 * (j : Rat)) * (r - p) * (r - p) := by rfl

/-- A finite arctangent-kernel polynomial has a right-endpoint Riemann error
at most `n(n+1)` times the squared length of a unit cell.  This is a wholly
finite rational estimate: it sums the signed monomial bounds above. -/
theorem kernelPartial_rightRectangle_error_bound
    {p r : Rat}
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hpr : p <= r) (hr1 : r <= 1)
    (n : Nat) :
    -((n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p)) <=
        (r - p) * kernelPartial r n - kernelPartialIntegralBetween p r n /\
      (r - p) * kernelPartial r n - kernelPartialIntegralBetween p r n <=
        (n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p) := by
  induction n with
  | zero =>
      constructor <;>
        simp [kernelPartial, altGeomPartial, kernelPartialIntegralBetween] <;>
        grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      have hterm := signed_kernelTerm_rightRectangle_error_bound
        hp0 hp1 hpr hr1 (n + 1)
      have hrec :
          (r - p) * kernelPartial r (n + 1) -
              kernelPartialIntegralBetween p r (n + 1) =
            ((r - p) * kernelPartial r n -
              kernelPartialIntegralBetween p r n) +
            ((r - p) * (- (r * r)) ^ (n + 1) -
              kernelTermIntegralBetween p r (n + 1)) := by
        simp only [kernelPartial, altGeomPartial, kernelPartialIntegralBetween]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      rw [hrec]
      constructor
      · calc
          -(((n + 1 : Nat) : Rat) * ((n +1 + 1 : Nat) : Rat) *
              (r - p) * (r - p)) =
              -((n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p)) +
                -((2 * ((n + 1 : Nat) : Rat)) * (r - p) * (r - p)) := by
                  push_cast
                  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
          _ <= ((r - p) * kernelPartial r n -
              kernelPartialIntegralBetween p r n) +
              ((r - p) * (- (r * r)) ^ (n + 1) -
                kernelTermIntegralBetween p r (n + 1)) :=
              rat_add_le_add ih.1 hterm.1
      · calc
          ((r - p) * kernelPartial r n -
              kernelPartialIntegralBetween p r n) +
              ((r - p) * (- (r * r)) ^ (n + 1) -
                kernelTermIntegralBetween p r (n + 1)) <=
              (n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p) +
                (2 * ((n + 1 : Nat) : Rat)) * (r - p) * (r - p) :=
              rat_add_le_add ih.2 hterm.2
          _ = ((n + 1 : Nat) : Rat) * ((n + 1 + 1 : Nat) : Rat) *
              (r - p) * (r - p) := by
                push_cast
                grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                  Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem div_between_of_between {a p d : Rat}
    (hp : 0 <= p) (hd : 1 <= d)
    (hlo : -p <= a) (hhi : a <= p) :
    -p <= a / d /\ a / d <= p := by
  have hdpos : 0 < d := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hp_le_pd : p <= p * d := by
    have h := Rat.mul_le_mul_of_nonneg_left hd hp
    rwa [Rat.mul_one] at h
  have hdiv_cancel : (a / d) * d = a := by
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := d)
    · have hneg_pd_le_neg_p : -(p * d) <= -p := by grind
      calc
        (-p) * d = -(p * d) := by rw [Rat.neg_mul]
        _ <= -p := hneg_pd_le_neg_p
        _ <= a := hlo
        _ = (a / d) * d := by rw [hdiv_cancel]
    · exact hdpos
  · apply Rat.le_of_mul_le_mul_right (c := d)
    · calc
        (a / d) * d = a := hdiv_cancel
        _ <= p := hhi
        _ <= p * d := hp_le_pd
    · exact hdpos

/-- The finite rational identity behind the arctangent series:
`1/(1+x^2)` is a finite alternating polynomial plus an explicit rational
remainder. -/
theorem one_div_one_add_square_eq_partial_add_remainder (x : Rat) (n : Nat) :
    1 / (1 + x * x) = kernelPartial x n + kernelRemainder x n := by
  unfold kernelPartial kernelRemainder
  let d : Rat := 1 + x * x
  have hdpos : 0 < d := by
    dsimp [d]
    have h := RatFun.rat_square_nonneg x
    grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hfinite := one_add_mul_altGeomPartial_add_remainder (x * x) n
  dsimp [remainderNumerator] at hfinite
  change 1 / d = altGeomPartial (x * x) n + (- (x * x)) ^ (n + 1) / d
  rw [Rat.div_def]
  calc
    1 * d⁻¹=
        (d * altGeomPartial (x * x) n + (- (x * x)) ^ (n + 1)) * d⁻¹:= by
          rw [←hfinite]
    _ = altGeomPartial (x * x) n + (- (x * x)) ^ (n + 1) * d⁻¹:= by
          have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
          grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]

/-- Pointwise rational remainder estimate for the arctangent-kernel expansion.

The important feature is what is *not* present: no higher derivatives of
`1/(1+x^2)` appear.  The finite division identity leaves a remainder whose
absolute value is bounded directly by `(x*x)^(n+1)`. -/
theorem qabs_kernelRemainder_le_power (x : Rat) (n : Nat) :
    qabs (kernelRemainder x n) <= (x * x) ^ (n + 1) := by
  unfold kernelRemainder remainderNumerator
  let u : Rat := x * x
  let p : Rat := u ^ (n + 1)
  let d : Rat := 1 + x * x
  have hu : 0 <= u := by
    dsimp [u]
    exact RatFun.rat_square_nonneg x
  have hp : 0 <= p := by
    dsimp [p]
    exact Rat.pow_nonneg hu
  have hd : 1 <= d := by
    dsimp [d]
    grind [RatFun.rat_square_nonneg x]
  have hpow := neg_pow_between_pow hu (n + 1)
  have hdiv := div_between_of_between hp hd hpow.1 hpow.2
  exact qabs_le_of_between hdiv.1 hdiv.2

/-- A finite error-budget certificate for the arctangent-kernel expansion.

If a supplied rational power check bounds the next omitted finite power by
`eps`, then the division identity and the kernel remainder are certified at
that same explicit budget.  This is a finite rational implication: `eps` is
not a limiting parameter and no completed value is introduced. -/
theorem finite_remainder_error_budget
    (x eps : Rat) (n : Nat)
    (hbudget : (x * x) ^ (n + 1) <= eps) :
    1 / (1 + x * x) = kernelPartial x n + kernelRemainder x n /\
      qabs (kernelRemainder x n) <= eps := by
  constructor
  · exact one_div_one_add_square_eq_partial_add_remainder x n
  · exact Rat.le_trans (qabs_kernelRemainder_le_power x n) hbudget

/-- A fully executable remainder budget on the rational half-interval.

For `0 <= x <= 1/2`, the omitted power is dominated by a half-power, so the
generic finite remainder route reaches the explicit stage error `1/(n+2)`.
This is a finite Taylor certificate; it does not use a limiting argument. -/
theorem finite_remainder_half_interval_budget
    {x : Rat} (hx0 : 0 <= x) (hxhalf : x <= (1 : Rat) / 2) (n : Nat) :
    1 / (1 + x * x) = kernelPartial x n + kernelRemainder x n /\
      qabs (kernelRemainder x n) <=
        1 / (((n + 2 : Nat) : Rat)) := by
  have hxx0 : 0 <= x * x := Rat.mul_nonneg hx0 hx0
  have hxxhalf : x * x <= (1 : Rat) / 2 := by
    have hleft : x * x <= x * ((1 : Rat) / 2) :=
      Rat.mul_le_mul_of_nonneg_left hxhalf hx0
    have hright : x * ((1 : Rat) / 2) <=
        ((1 : Rat) / 2) * ((1 : Rat) / 2) :=
      Rat.mul_le_mul_of_nonneg_right hxhalf (by native_decide)
    have hquarter : ((1 : Rat) / 2) * ((1 : Rat) / 2) <=
        (1 : Rat) / 2 := by native_decide
    exact Rat.le_trans hleft (Rat.le_trans hright hquarter)
  have hpow := Series.pow_le_half_pow hxx0 hxxhalf (n + 1)
  have hhalf := Series.half_pow_le_one_div_succ (n + 1)
  exact finite_remainder_error_budget x
    (1 / (((n + 2 : Nat) : Rat))) n
    (Rat.le_trans hpow hhalf)

private theorem rat_mul_nonpos_of_nonneg_of_nonpos {a b : Rat}
    (ha : 0 <= a) (hb : b <= 0) : a * b <= 0 := by
  have hnb : 0 <= -b := by grind
  have h := Rat.mul_nonneg ha hnb
  grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem rat_mul_nonpos_of_nonpos_of_nonneg {a b : Rat}
    (ha : a <= 0) (hb : 0 <= b) : a * b <= 0 := by
  have h := rat_mul_nonpos_of_nonneg_of_nonpos hb ha
  grind [Rat.mul_comm]

private theorem rat_mul_nonneg_of_nonpos_of_nonpos {a b : Rat}
    (ha : a <= 0) (hb : b <= 0) : 0 <= a * b := by
  have hna : 0 <= -a := by grind
  have hnb : 0 <= -b := by grind
  have h := Rat.mul_nonneg hna hnb
  grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]

private theorem neg_pow_even_nonneg_and_odd_nonpos {u : Rat}
    (hu : 0 <= u) (k : Nat) :
    0 <= (-u) ^ (2 * k) /\ (-u) ^ (2 * k + 1) <= 0 := by
  induction k with
  | zero =>
      constructor
      · simp
        native_decide
      · rw [show 2 * 0 + 1 = 0 + 1 by omega]
        rw [Rat.pow_succ]
        simp
        grind
  | succ k ih =>
      have hneg : -u <= 0 := by grind
      have hevenSucc : 0 <= (-u) ^ (2 * (k + 1)) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
        rw [Rat.pow_succ]
        exact rat_mul_nonneg_of_nonpos_of_nonpos ih.2 hneg
      constructor
      · exact hevenSucc
      · rw [show 2 * (k + 1) + 1 = 2 * (k + 1) + 1 by omega]
        rw [Rat.pow_succ]
        exact rat_mul_nonpos_of_nonneg_of_nonpos hevenSucc hneg

private theorem neg_pow_even_nonneg {u : Rat}
    (hu : 0 <= u) (k : Nat) : 0 <= (-u) ^ (2 * k) :=
  (neg_pow_even_nonneg_and_odd_nonpos hu k).1

private theorem neg_pow_odd_nonpos {u : Rat}
    (hu : 0 <= u) (k : Nat) : (-u) ^ (2 * k + 1) <= 0 :=
  (neg_pow_even_nonneg_and_odd_nonpos hu k).2

/-- Odd finite truncations leave a nonnegative arctangent-kernel remainder. -/
theorem kernelRemainder_nonneg_oddPartial (x : Rat) (k : Nat) :
    0 <= kernelRemainder x (2 * k + 1) := by
  unfold kernelRemainder remainderNumerator
  let d : Rat := 1 + x * x
  have hu : 0 <= x * x := RatFun.rat_square_nonneg x
  have hnum : 0 <= (- (x * x)) ^ (2 * k + 1 + 1) := by
    simpa [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      using neg_pow_even_nonneg hu (k + 1)
  have hdpos : 0 < d := by
    dsimp [d]
    grind [RatFun.rat_square_nonneg x]
  have hinv : 0 <= Inv.inv d := Rat.le_of_lt ((Rat.inv_pos).2 hdpos)
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum hinv

/-- Even finite truncations leave a nonpositive arctangent-kernel remainder. -/
theorem kernelRemainder_nonpos_evenPartial (x : Rat) (k : Nat) :
    kernelRemainder x (2 * k) <= 0 := by
  unfold kernelRemainder remainderNumerator
  let d : Rat := 1 + x * x
  have hu : 0 <= x * x := RatFun.rat_square_nonneg x
  have hnum : (- (x * x)) ^ (2 * k + 1) <= 0 :=
    neg_pow_odd_nonpos hu k
  have hdpos : 0 < d := by
    dsimp [d]
    grind [RatFun.rat_square_nonneg x]
  have hinv : 0 <= Inv.inv d := Rat.le_of_lt ((Rat.inv_pos).2 hdpos)
  rw [Rat.div_def]
  exact rat_mul_nonpos_of_nonpos_of_nonneg hnum hinv

/-- Odd arctangent-kernel truncations are lower bounds for `1/(1+x^2)`. -/
theorem kernelPartial_odd_le_kernel (x : Rat) (k : Nat) :
    kernelPartial x (2 * k + 1) <= 1 / (1 + x * x) := by
  have hrem := kernelRemainder_nonneg_oddPartial x k
  have hbase := (Rat.add_le_add_left
    (a := (0 : Rat))
    (b := kernelRemainder x (2 * k + 1))
    (c := kernelPartial x (2 * k + 1))).mpr hrem
  rw [Rat.add_zero] at hbase
  calc
    kernelPartial x (2 * k + 1) <=
        kernelPartial x (2 * k + 1) +
          kernelRemainder x (2 * k + 1) := hbase
    _ = 1 / (1 + x * x) := by
      rw [←one_div_one_add_square_eq_partial_add_remainder]

/-- Even arctangent-kernel truncations are upper bounds for `1/(1+x^2)`. -/
theorem kernel_le_kernelPartial_even (x : Rat) (k : Nat) :
    1 / (1 + x * x) <= kernelPartial x (2 * k) := by
  have hrem := kernelRemainder_nonpos_evenPartial x k
  have hbase := (Rat.add_le_add_left
    (a := kernelRemainder x (2 * k))
    (b := (0 : Rat))
    (c := kernelPartial x (2 * k))).mpr hrem
  rw [Rat.add_zero] at hbase
  calc
    1 / (1 + x * x) =
        kernelPartial x (2 * k) + kernelRemainder x (2 * k) :=
      one_div_one_add_square_eq_partial_add_remainder x (2 * k)
    _ <= kernelPartial x (2 * k) := hbase

/-- Combined finite-division route for arctangent's kernel.

For each finite stage, `1/(1+x^2)` is a finite alternating polynomial plus a
remainder bounded directly by `(x*x)^(n+1)`.  This is the theorem that replaces
any attempt to compute high derivatives of the rational function. -/
def FiniteRemainderRoute : Prop :=
  forall x n,
    1 / (1 + x * x) = kernelPartial x n + kernelRemainder x n /\
    qabs (kernelRemainder x n) <= (x * x) ^ (n + 1)

theorem finiteRemainderRoute :
    FiniteRemainderRoute := by
  intro x n
  exact ⟨one_div_one_add_square_eq_partial_add_remainder x n,
    qabs_kernelRemainder_le_power x n⟩
end ArctanKernel

/-- Arctangent Taylor coefficients generated from
`atan' = 1/(1+x^2)` and `atan(0)=0`.

This is the formal algebraic endpoint for the later analytic proof that the
definite-integral arctangent agrees with the interval power-series algorithm. -/
def ArctanTaylorCoefficientRoute : Prop :=
  FormalPowerSeries.HasFormalDerivative
    FormalPowerSeries.atanTaylorCoeff
    FormalPowerSeries.oneOverOnePlusSquareCoeff /\
  FormalPowerSeries.atanTaylorCoeff 0 = 0 /\
  forall k,
    FormalPowerSeries.atanTaylorCoeff (2 * k + 1) =
      FormalPowerSeries.atanOddCoeff k

theorem arctanTaylorCoefficientRoute :
    ArctanTaylorCoefficientRoute := by
  constructor
  · exact FormalPowerSeries.atanTaylorCoeff_hasFormalDerivative
  constructor
  · exact FormalPowerSeries.atanTaylorCoeff_zero
  · intro k
    exact FormalPowerSeries.atanTaylorCoeff_odd k

namespace ArctanComparison

/-!
Comparison route between power-series arctangent and geometric arctangent.

Both definitions should agree with the oriented integral of `1 / (1 + t^2)`
from `0` to `x`.  The power-series side uses the finite remainder route above;
the geometric side uses the sector-area derivative with respect to slope.
-/

def unitDomain (x : Rat) : Prop :=
  Elementary.Arctan.powerSeriesDomain x

/-- The rational kernel `1/(1+t^2)` on the positively oriented interval needed
for integrating from `0` to `x`. For negative `x`, we integrate from `x` to
`0` and negate the result below. -/
def orientedKernelInterval (x : Rat) : FunctionOnInterval :=
  if 0 <= x then
    arctanKernelOnInterval 0 x
  else
    arctanKernelOnInterval x 0

structure KernelIntegralAt (x : Rat) where
  construction : Integral.ConstructionFor (orientedKernelInterval x)

def positiveKernelIntegralRaw (x : Rat) (c : KernelIntegralAt x) : RealRaw :=
  Integral.integralFor (orientedKernelInterval x) c.construction

def kernelIntegralRaw (x : Rat) (c : KernelIntegralAt x) : RealRaw :=
  if 0 <= x then
    positiveKernelIntegralRaw x c
  else
    -positiveKernelIntegralRaw x c

theorem positiveKernelIntegralRaw_valid
    (x : Rat) (c : KernelIntegralAt x) :
    (positiveKernelIntegralRaw x c).Valid :=
  Integral.integralFor_valid (orientedKernelInterval x) c.construction

theorem kernelIntegralRaw_valid
    (x : Rat) (c : KernelIntegralAt x) :
    (kernelIntegralRaw x c).Valid := by
  unfold kernelIntegralRaw
  by_cases hx : 0 <= x
  · simp [hx, positiveKernelIntegralRaw_valid x c]
  · simp [hx]
    exact RealRaw.neg_valid (positiveKernelIntegralRaw_valid x c)

structure KernelIntegralData where
  integralAt : forall x, unitDomain x -> KernelIntegralAt x

/-- Power-series arctangent agrees with the oriented kernel integral.  This is
where `ArctanKernel.finiteRemainderRoute` and
`arctanTaylorCoefficientRoute` should ultimately be used. -/
def PowerSeriesEqualsKernelIntegral (data : KernelIntegralData) : Prop :=
  forall (x : Rat) (hx : unitDomain x),
    (arctan x).Equiv (kernelIntegralRaw x (data.integralAt x hx))

/-- Geometric sector-area arctangent agrees with the oriented kernel integral.
This is the geometric derivative statement: sector area differentiated with
respect to slope is `1/(1+x^2)`. -/
def GeometryEqualsKernelIntegral (data : KernelIntegralData) : Prop :=
  forall (x : Rat) (hx : unitDomain x),
    (ArctanGeometry.arctanGeom x).Equiv
      (kernelIntegralRaw x (data.integralAt x hx))

structure KernelComparisonAt (x : Rat) where
  domain : unitDomain x
  integral : KernelIntegralAt x
  powerSeries_valid : (arctan x).Valid
  powerSeries_eq_kernel : (arctan x).Equiv (kernelIntegralRaw x integral)
  geometric_eq_kernel :
    (ArctanGeometry.arctanGeom x).Equiv (kernelIntegralRaw x integral)

theorem powerSeriesAgreesAt_of_kernelComparisonAt
    {x : Rat} (route : KernelComparisonAt x) :
    ArctanGeometry.PowerSeriesAgreesAt x := by
  have hkValid : (kernelIntegralRaw x route.integral).Valid :=
    kernelIntegralRaw_valid x route.integral
  have hgeomValid : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain route.domain
  exact RealRaw.equiv_trans
    route.powerSeries_valid hkValid hgeomValid
    route.powerSeries_eq_kernel
    (RealRaw.equiv_symm route.geometric_eq_kernel)

structure KernelComparisonRoute where
  data : KernelIntegralData
  powerSeries_valid : forall (x : Rat) (_hx : unitDomain x), (arctan x).Valid
  powerSeries_eq_kernel : PowerSeriesEqualsKernelIntegral data
  geometric_eq_kernel : GeometryEqualsKernelIntegral data

theorem powerSeriesAgreesOnUnit_of_kernelComparisonRoute
    (route : KernelComparisonRoute) :
    ArctanGeometry.PowerSeriesAgreesOnUnit := by
  intro x hx _hgeom
  have hpsValid : (arctan x).Valid :=
    route.powerSeries_valid x hx
  have hkValid : (kernelIntegralRaw x (route.data.integralAt x hx)).Valid :=
    kernelIntegralRaw_valid x (route.data.integralAt x hx)
  have hgeomValid : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain hx
  exact RealRaw.equiv_trans
    hpsValid hkValid hgeomValid
    (route.powerSeries_eq_kernel x hx)
    (RealRaw.equiv_symm (route.geometric_eq_kernel x hx))

theorem powerSeriesAgreesAt_of_kernelComparisonRoute
    (route : KernelComparisonRoute) {x : Rat} (hx : unitDomain x) :
    ArctanGeometry.PowerSeriesAgreesAt x :=
  powerSeriesAgreesAt_of_kernelComparisonAt
    { domain := hx
      integral := route.data.integralAt x hx
      powerSeries_valid := route.powerSeries_valid x hx
      powerSeries_eq_kernel := route.powerSeries_eq_kernel x hx
      geometric_eq_kernel := route.geometric_eq_kernel x hx }

theorem geometricAgreesWithPowerSeriesOnUnit_of_kernelComparisonRoute
    (route : KernelComparisonRoute) :
    forall (x : Rat) (_hx : unitDomain x),
      (ArctanGeometry.arctanGeom x).Equiv (arctan x) := by
  intro x hx
  exact ArctanGeometry.geometric_equiv_powerSeries_of_agreement
    (powerSeriesAgreesOnUnit_of_kernelComparisonRoute route)
    hx

/-- The finite algebra already available for the power-series half of the
comparison.  This records that the needed Taylor bricks are present before we
build the analytic interval proof. -/
theorem powerSeriesKernelFiniteData :
    ArctanKernel.FiniteRemainderRoute /\ ArctanTaylorCoefficientRoute := by
  exact ⟨ArctanKernel.finiteRemainderRoute,
    arctanTaylorCoefficientRoute⟩

end ArctanComparison

end Taylor

end ComputableAnalysis
