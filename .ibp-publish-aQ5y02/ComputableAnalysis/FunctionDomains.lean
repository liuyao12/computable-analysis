import ComputableAnalysis.Calculus
import ComputableAnalysis.Polynomial

namespace ComputableAnalysis

namespace RatFun

/-- A rational function as a partial computable real-valued function.

The domain is exactly the set of rational inputs where the denominator is
nonzero.  There is no default value at poles. -/
def asPartialRealFunRaw (f : RatFun) : PartialRealFunRaw where
  definedAt := f.DefinedAt
  compute := fun x h n => (RealRaw.ofRat (f.evalOnDomain x h)).compute n

theorem asPartialRealFunRaw_valid (f : RatFun) :
    forall x h, RealRaw.ValidCompute ((f.asPartialRealFunRaw).compute x h) := by
  intro x h
  exact RealRaw.ofRat_valid (f.evalOnDomain x h)

/-- Certify a rational function on a whole interval by proving its denominator
does not vanish anywhere on that interval. -/
def onInterval (f : RatFun) (a b : Rat)
    (hdef : forall x, inDomainInterval a b x -> f.DefinedAt x) :
    FunctionOnInterval where
  raw := f.asPartialRealFunRaw
  lower := a
  upper := b
  defined_on := hdef
  valid_on := f.asPartialRealFunRaw_valid

/-- The useful interval-level certificate for rational functions.

For calculus, pointwise nonvanishing of the denominator is not enough.  We need
an explicit positive lower bound on its absolute value throughout the interval;
that is one formula-specific way to prove the generic interval-regularity
condition. -/
structure DenominatorApartOnInterval (f : RatFun) (a b : Rat) where
  bound : QPos
  defined_on : forall x, inDomainInterval a b x -> f.DefinedAt x
  apart_on : forall x, inDomainInterval a b x -> bound.val <= qabs (f.denominator x)

/-- A rational-function singularity can be invisible at rational points but
still visible to interval calculus.  This proposition says that no positive
denominator-apartness bound exists on the interval. -/
def NoDenominatorApartOnInterval (f : RatFun) (a b : Rat) : Prop :=
  DenominatorApartOnInterval f a b -> False

def onRegularInterval (f : RatFun) (a b : Rat)
    (h : DenominatorApartOnInterval f a b) :
    FunctionOnInterval :=
  f.onInterval a b h.defined_on

theorem rat_square_nonneg (x : Rat) : 0 <= x * x := by
  rcases (Rat.le_total : (0 : Rat) <= x ∨ x <= 0) with hx | hx
  · exact Rat.mul_nonneg hx hx
  · have hneg : 0 <= -x := by grind
    have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
    have heq : (-x) * (-x) = x * x := by
      grind [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]
    rwa [heq] at hsq

theorem oneOverOnePlusSquare_denominator_eq (x : Rat) :
    oneOverOnePlusSquare.denominator x = 1 + x * x := by
  unfold denominator oneOverOnePlusSquare Polynomial.eval
  simp
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem oneOverOnePlusSquare_denominator_ge_one (x : Rat) :
    1 <= oneOverOnePlusSquare.denominator x := by
  rw [oneOverOnePlusSquare_denominator_eq]
  grind [rat_square_nonneg x]

theorem oneOverOnePlusSquare_denominator_pos (x : Rat) :
    0 < oneOverOnePlusSquare.denominator x := by
  have h := oneOverOnePlusSquare_denominator_ge_one x
  grind

theorem oneOverOnePlusSquare_numerator_eq (x : Rat) :
    oneOverOnePlusSquare.numerator x = 1 := by
  unfold numerator oneOverOnePlusSquare Polynomial.eval
  simp
  rw [Rat.add_zero]

theorem oneOverOnePlusSquare_evalOnDomain_eq (x : Rat)
    (h : oneOverOnePlusSquare.DefinedAt x) :
    oneOverOnePlusSquare.evalOnDomain x h = 1 / (1 + x * x) := by
  unfold evalOnDomain
  rw [oneOverOnePlusSquare_numerator_eq]
  rw [oneOverOnePlusSquare_denominator_eq]

theorem oneOverOnePlusSquare_defined_all (x : Rat) :
    oneOverOnePlusSquare.DefinedAt x := by
  change ((oneOverOnePlusSquare.denominator x != 0) = true)
  have hne : oneOverOnePlusSquare.denominator x ≠ 0 :=
    Rat.ne_of_gt (oneOverOnePlusSquare_denominator_pos x)
  simp [hne]

def oneOverOnePlusSquare_denominator_apart_on_interval (a b : Rat) :
    DenominatorApartOnInterval oneOverOnePlusSquare a b where
  bound := ⟨1, by native_decide⟩
  defined_on := by
    intro x _hx
    exact oneOverOnePlusSquare_defined_all x
  apart_on := by
    intro x _hx
    rw [oneOverOnePlusSquare_denominator_eq]
    have hge : 1 <= 1 + x * x := by
      grind [rat_square_nonneg x]
    unfold qabs
    have hnot : ¬1 + x * x < 0 := by grind
    simp [hnot]
    exact hge

def oneOverOnePlusSquareOnInterval (a b : Rat) : FunctionOnInterval :=
  oneOverOnePlusSquare.onRegularInterval a b
    (oneOverOnePlusSquare_denominator_apart_on_interval a b)

theorem oneOverOnePlusSquareOnInterval_compute_eq
    (a b x : Rat) (hx : inDomainInterval a b x) (n : Nat) :
    (oneOverOnePlusSquareOnInterval a b).compute x hx n =
      { lo := 1 / (1 + x * x), hi := 1 / (1 + x * x) } := by
  unfold oneOverOnePlusSquareOnInterval onRegularInterval onInterval FunctionOnInterval.compute
  unfold asPartialRealFunRaw
  change (RealRaw.ofRat
      (oneOverOnePlusSquare.evalOnDomain x (oneOverOnePlusSquare_defined_all x))).compute n =
    { lo := 1 / (1 + x * x), hi := 1 / (1 + x * x) }
  rw [oneOverOnePlusSquare_evalOnDomain_eq]
  rfl

theorem oneOverX_not_defined_at_zero :
    ¬ oneOverX.DefinedAt 0 := by
  intro h
  change ((oneOverX.denominator 0 != 0) = true) at h
  have hz : oneOverX.denominator 0 = 0 := by native_decide
  rw [hz] at h
  contradiction

/-- The domain certificate correctly rejects `1/x` on `[-1,1]`, because the
interval contains the pole at `0`. -/
theorem oneOverX_cannot_be_defined_on_minus_one_one :
    ¬ (forall x, inDomainInterval (-1 : Rat) 1 x -> oneOverX.DefinedAt x) := by
  intro h
  have hleft : (-1 : Rat) <= 0 := by decide
  have hright : (0 : Rat) <= 1 := by decide
  exact oneOverX_not_defined_at_zero (h 0 ⟨hleft, hright⟩)

/-- The stronger continuity-facing certificate also rejects `1/x` on `[-1,1]`:
there is no positive lower bound for `|x|` on an interval containing `0`. -/
theorem oneOverX_no_denominator_apart_on_minus_one_one :
    NoDenominatorApartOnInterval oneOverX (-1 : Rat) 1 := by
  intro h
  have hleft : (-1 : Rat) <= 0 := by decide
  have hright : (0 : Rat) <= 1 := by decide
  have hbound := h.apart_on 0 ⟨hleft, hright⟩
  have hz : qabs (oneOverX.denominator 0) = 0 := by native_decide
  rw [hz] at hbound
  grind

theorem oneOverX_denominator_eq (x : Rat) :
    oneOverX.denominator x = x := by
  unfold denominator oneOverX Polynomial.eval
  simp
  grind

theorem oneOverX_numerator_eq (x : Rat) :
    oneOverX.numerator x = 1 := by
  unfold numerator oneOverX Polynomial.eval
  simp
  rw [Rat.add_zero]

theorem oneOverX_defined_of_pos {x : Rat} (hx : 0 < x) :
    oneOverX.DefinedAt x := by
  change ((oneOverX.denominator x != 0) = true)
  rw [oneOverX_denominator_eq]
  simp [Rat.ne_of_gt hx]

theorem oneOverX_evalOnDomain_eq (x : Rat)
    (h : oneOverX.DefinedAt x) :
    oneOverX.evalOnDomain x h = 1 / x := by
  unfold evalOnDomain
  rw [oneOverX_numerator_eq, oneOverX_denominator_eq]

/-- On `[a,b]` with `0 < a`, the denominator of `1/x` is uniformly apart
from zero by the rational bound `a`. -/
def oneOverX_denominator_apart_on_pos_interval (a b : Rat) (ha : 0 < a) :
    DenominatorApartOnInterval oneOverX a b where
  bound := ⟨a, ha⟩
  defined_on := by
    intro x hx
    rcases hx with ⟨hax, _hxb⟩
    have hxpos : 0 < x := by grind
    exact oneOverX_defined_of_pos hxpos
  apart_on := by
    intro x hx
    rw [oneOverX_denominator_eq]
    unfold qabs
    rcases hx with ⟨hax, _hxb⟩
    have hxpos : 0 < x := by grind
    have hxnonneg : ¬ x < 0 := by grind
    simp [hxnonneg]
    exact hax

/-- The rational function `1/x`, certified on a positive rational interval. -/
def oneOverXOnPositiveInterval (a b : Rat) (ha : 0 < a) : FunctionOnInterval :=
  oneOverX.onRegularInterval a b
    (oneOverX_denominator_apart_on_pos_interval a b ha)

theorem oneOverXOnPositiveInterval_compute_eq
    (a b : Rat) (ha : 0 < a)
    (x : Rat) (hx : inDomainInterval a b x) (n : Nat) :
    (oneOverXOnPositiveInterval a b ha).compute x hx n =
      { lo := 1 / x, hi := 1 / x } := by
  unfold oneOverXOnPositiveInterval onRegularInterval onInterval FunctionOnInterval.compute
  unfold asPartialRealFunRaw
  rcases hx with ⟨hax, hxb⟩
  have hxpos : 0 < x := by grind
  change (RealRaw.ofRat
      (oneOverX.evalOnDomain x (oneOverX_defined_of_pos hxpos))).compute n =
    { lo := 1 / x, hi := 1 / x }
  rw [oneOverX_evalOnDomain_eq]
  rfl

/-- `1 / (x^2 - 2)` has no rational pole, but on `[1,2]` it
should fail interval regularity because rationals can approximate `sqrt 2`
arbitrarily well.  Proving this constructively is a useful next theorem. -/
def oneOverXSquareMinusTwoNoDenominatorApartOnOneTwo : Prop :=
  NoDenominatorApartOnInterval oneOverXSquareMinusTwo 1 2

end RatFun

end ComputableAnalysis
