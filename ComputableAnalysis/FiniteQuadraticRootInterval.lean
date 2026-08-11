import ComputableAnalysis.AlgebraicFunctions

namespace ComputableAnalysis

/-!
# Finite quadratic-formula branch intervals

This file is deliberately a boundary certificate.  It approximates the
square-root part at an explicit finite stage and transports that interval
through the affine map appearing in the quadratic formula.  It does not
introduce an exact completed square root, nor does it assert a quartic formula.
-/

/-- The interval image of `I` under the rational affine map `x ↦ c + k*x`.

Taking the min and max makes this definition sound for either orientation of
the affine map; in particular it also covers the minus quadratic branch.
-/
def affineQInterval (c k : Rat) (I : QInterval) : QInterval :=
  { lo := min (c + k * I.lo) (c + k * I.hi)
    hi := max (c + k * I.lo) (c + k * I.hi) }

theorem affineQInterval_ordered (c k : Rat) (I : QInterval) :
    (affineQInterval c k I).lo <= (affineQInterval c k I).hi := by
  unfold affineQInterval
  grind

/-- Finite affine transport: every point in `I` maps into its finite image. -/
theorem affineQInterval_mem
    (c k : Rat) {I : QInterval} {x : Rat}
    (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    (affineQInterval c k I).lo <= c + k * x /\
      c + k * x <= (affineQInterval c k I).hi := by
  unfold affineQInterval
  by_cases hk : 0 <= k
  · have hlo : c + k * I.lo <= c + k * x := by
      exact (Rat.add_le_add_left).2 (Rat.mul_le_mul_of_nonneg_left hxlo hk)
    have hhi : c + k * x <= c + k * I.hi := by
      exact (Rat.add_le_add_left).2 (Rat.mul_le_mul_of_nonneg_left hxhi hk)
    constructor <;> grind
  · have hk' : k <= 0 := by grind
    have hhi : c + k * I.hi <= c + k * x := by
      have h := Rat.mul_le_mul_of_nonneg_left hxhi (show 0 <= -k by grind)
      have h' : -((-k) * I.hi) <= -((-k) * x) := Rat.neg_le_neg h
      have h'' : k * I.hi <= k * x := by
        simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using h'
      exact (Rat.add_le_add_left).2 h''
    have hlo : c + k * x <= c + k * I.lo := by
      have h := Rat.mul_le_mul_of_nonneg_left hxlo (show 0 <= -k by grind)
      have h' : -((-k) * x) <= -((-k) * I.lo) := Rat.neg_le_neg h
      have h'' : k * x <= k * I.lo := by
        simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using h'
      exact (Rat.add_le_add_left).2 h''
    constructor <;> grind

/-- The finite square-root interval used by a quadratic branch. -/
def finiteQuadraticRootSqrtInterval
    (D : Rat) (hD : sqrtDomain D) (stage : Nat) : QInterval :=
  sqrtApproxOnDomain D hD stage

/-- The `s`-signed quadratic-formula branch, with `s = 1` or `s = -1`.

The denominator is intentionally left as rational arithmetic.  The caller's
`a > 0` hypothesis supplies its positivity in the certificate theorem below.
-/
def finiteQuadraticRootInterval
    (a b D s : Rat) (hD : sqrtDomain D) (stage : Nat) : QInterval :=
  affineQInterval (-b / (2 * a)) (s / (2 * a))
    (finiteQuadraticRootSqrtInterval D hD stage)

theorem finiteQuadraticRootInterval_spec
    {a b D s : Rat} (ha : 0 < a) (hD : sqrtDomain D)
    (hs : s = 1 \/ s = -1) (stage : Nat) :
    SqrtIntervalSpec D (finiteQuadraticRootSqrtInterval D hD stage) /\
      (forall y : Rat,
        (finiteQuadraticRootSqrtInterval D hD stage).lo <= y ->
        y <= (finiteQuadraticRootSqrtInterval D hD stage).hi ->
        (finiteQuadraticRootInterval a b D s hD stage).lo <=
            -b / (2 * a) + (s / (2 * a)) * y /\
          -b / (2 * a) + (s / (2 * a)) * y <=
            (finiteQuadraticRootInterval a b D s hD stage).hi) := by
  constructor
  · exact sqrtApproxOnDomain_spec D hD stage
  · intro y hylo hyhi
    exact affineQInterval_mem (-b / (2 * a)) (s / (2 * a)) hylo hyhi

end ComputableAnalysis
