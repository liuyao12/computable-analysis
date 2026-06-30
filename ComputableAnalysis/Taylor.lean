import ComputableAnalysis.Calculus
import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.PowerSeries

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
    (positiveKernelIntegralRaw x c).Valid := by
  change RealRaw.ValidCompute
    (Integral.integralFor (orientedKernelInterval x) c.construction).compute
  unfold Integral.integralFor
  exact c.construction.certificate

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
