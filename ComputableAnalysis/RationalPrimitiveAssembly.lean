import ComputableAnalysis.RationalPrimitivePolynomial
import ComputableAnalysis.RationalPrimitiveLogarithm
import ComputableAnalysis.RationalPrimitivePowers
import ComputableAnalysis.RationalPartialFractions

/-!
# Actual elementary primitives for rationally split denominators

The elementary witness describes the evaluator itself: rational polynomials,
reciprocal powers, normalized logarithms, restriction, addition, and scaling.
-/

namespace ComputableAnalysis

namespace FunctionOnInterval

def restrictTo (F : FunctionOnInterval) (a b : Rat)
    (hmap : ∀ x, inDomainInterval a b x → inDomainInterval F.lower F.upper x) :
    FunctionOnInterval where
  raw := F.raw
  lower := a
  upper := b
  defined_on := fun x hx => F.defined_on x (hmap x hx)
  valid_on := F.valid_on

end FunctionOnInterval

namespace HasDerivativeOnInterval

/-- Replace a derivative evaluator by literally equal boxes on its domain. -/
def replaceDerivative {F G H : FunctionOnInterval} (D : HasDerivativeOnInterval F G)
    (hlo : H.lower = G.lower) (hhi : H.upper = G.upper)
    (heq : ∀ x hx hy n, G.compute x hx n = H.compute x hy n) :
    HasDerivativeOnInterval F H where
  same_lower := hlo.trans D.same_lower
  same_upper := hhi.trans D.same_upper
  stepPrecision := D.stepPrecision
  evalPrecision := D.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hs
    have hg : inDomainInterval G.lower G.upper x := by simpa only [hlo, hhi] using hdx
    rw [← heq x hg hdx]
    exact D.close x h n hx hxh hg hh hs

end HasDerivativeOnInterval

namespace RationalPrimitiveAssembly

/-- A syntax witness tied to its valid represented evaluator. -/
inductive Elementary : FunctionOnInterval → Prop where
  | polynomial (p : List Rat) (a b : Rat) : Elementary (FunctionOnInterval.exactRat (Polynomial.eval p) a b)
  | reciprocalPower (pole a b : Rat) (n : Nat) :
      Elementary (FunctionOnInterval.exactRat (RationalPrimitivePowers.primitive pole n) a b)
  | logarithm (pole center : Rat) (hc : center ≠ pole) :
      Elementary (RationalPrimitiveLogarithm.simplePolePrimitive pole center hc)
  | restrict {F : FunctionOnInterval} (hF : Elementary F) (a b : Rat)
      (hmap : ∀ x, inDomainInterval a b x → inDomainInterval F.lower F.upper x) :
      Elementary (F.restrictTo a b hmap)
  | scale (r : Rat) {F : FunctionOnInterval} (hF : Elementary F) :
      Elementary (FunctionOnInterval.scaleRat r F)
  | add {F G : FunctionOnInterval} (hF : Elementary F) (hG : Elementary G)
      (hlo : F.lower = G.lower) (hhi : F.upper = G.upper) :
      Elementary (FunctionOnInterval.add F G hlo hhi)

structure PrimitiveOn (f : Rat → Rat) (a b : Rat) where
  function : FunctionOnInterval
  elementary : Elementary function
  derivative : HasDerivativeOnInterval function (FunctionOnInterval.exactRat f a b)

namespace PrimitiveOn

def congr {f g : Rat → Rat} {a b : Rat} (P : PrimitiveOn f a b)
    (heq : ∀ x, inDomainInterval a b x → f x = g x) : PrimitiveOn g a b where
  function := P.function
  elementary := P.elementary
  derivative := P.derivative.replaceDerivative rfl rfl (by
    intro x hx hy n
    change ({lo := f x, hi := f x} : QInterval) = {lo := g x, hi := g x}
    rw [heq x hx])

def scale (c : Rat) {f : Rat → Rat} {a b : Rat} (P : PrimitiveOn f a b) :
    PrimitiveOn (fun x => c * f x) a b where
  function := FunctionOnInterval.scaleRat c P.function
  elementary := .scale c P.elementary
  derivative := (P.derivative.scale c).replaceDerivative rfl rfl (by
    intro x hx hy n
    change QInterval.scaleRat c {lo := f x, hi := f x} = {lo := c * f x, hi := c * f x}
    unfold QInterval.scaleRat
    split <;> rfl)

def add {f g : Rat → Rat} {a b : Rat} (P : PrimitiveOn f a b) (Q : PrimitiveOn g a b) :
    PrimitiveOn (fun x => f x + g x) a b := by
  have hlo : P.function.lower = Q.function.lower := P.derivative.same_lower.symm.trans Q.derivative.same_lower
  have hhi : P.function.upper = Q.function.upper := P.derivative.same_upper.symm.trans Q.derivative.same_upper
  exact {
    function := FunctionOnInterval.add P.function Q.function hlo hhi
    elementary := .add P.elementary Q.elementary hlo hhi
    derivative := (P.derivative.add Q.derivative hlo hhi).replaceDerivative rfl rfl (by
      intro x hx hy n
      rfl) }

end PrimitiveOn

open RationalPrimitiveFormula RationalPrimitiveLogarithm

def polynomial (p : List Rat) (a b : Rat) : PrimitiveOn (Polynomial.eval p) a b where
  function := FunctionOnInterval.exactRat (Polynomial.eval (polynomialPrimitive p)) a b
  elementary := .polynomial _ _ _
  derivative := RationalPrimitivePolynomial.hasDerivative p a b

/-- An explicit common logarithm chart also separates all reciprocal powers. -/
theorem chart_apart (pole center r x : Rat) (hr : r <= poleRadius pole center)
    (hx : inDomainInterval (center - r) (center + r) x) :
    poleRadius pole center <= qabs (x - pole) := by
  have hxc : qabs (center - x) <= r := by
    change center - r <= x ∧ x <= center + r at hx
    unfold qabs
    split <;> grind
  have ht := qabs_add_le (center - x) (x - pole)
  have he : center - x + (x - pole) = center - pole := by grind
  rw [he] at ht
  unfold poleRadius at *
  grind

def linear (c pole center r : Rat) (hc : center ≠ pole)
    (hr : r <= poleRadius pole center) (n : Nat) :
    PrimitiveOn (fun x => Term.eval x (.linear c pole n)) (center - r) (center + r) := by
  cases n with
  | zero =>
      let L := simplePolePrimitive pole center hc
      have hmap : ∀ x, inDomainInterval (center - r) (center + r) x →
          inDomainInterval L.lower L.upper x := by
        intro x hx
        change center - r <= x ∧ x <= center + r at hx
        change center - poleRadius pole center <= x ∧ x <= center + poleRadius pole center
        grind
      let D := simplePole_hasDerivative pole center hc
      let P : PrimitiveOn (fun x => 1 / (x - pole)) (center - r) (center + r) := {
        function := L.restrictTo (center - r) (center + r) hmap
        elementary := .restrict (.logarithm pole center hc) _ _ hmap
        derivative := {
          same_lower := rfl
          same_upper := rfl
          stepPrecision := D.stepPrecision
          evalPrecision := D.evalPrecision
          close := by
            intro x h n hx hxh hdx hh hs
            exact D.close x h n (hmap x hx) (hmap (x+h) hxh) (hmap x hdx) hh hs } }
      exact (P.scale c).congr (by
        intro x hx
        simp only [Term.eval, Nat.zero_add, Rat.pow_one, Rat.div_def, Rat.one_mul])
  | succ n =>
      let delta : QPos := ⟨poleRadius pole center, poleRadius_pos hc⟩
      let P : PrimitiveOn (fun x => (x-pole)⁻¹ ^ (n+2)) (center-r) (center+r) := {
        function := FunctionOnInterval.exactRat (RationalPrimitivePowers.primitive pole n) _ _
        elementary := .reciprocalPower _ _ _ _
        derivative := RationalPrimitivePowers.hasDerivative pole _ _ delta
          (fun x hx => chart_apart pole center r x hr hx) n }
      exact (P.scale c).congr (by
        intro x hx
        change c * (x-pole)⁻¹ ^ (n+2) = c / (x-pole) ^ (n+2)
        have hinv : ∀ k : Nat, (x-pole)⁻¹ ^ k = ((x-pole)^k)⁻¹ := by
          intro k
          induction k with
          | zero => simp only [Rat.pow_zero]; exact (show (1 : Rat)⁻¹ = 1 by decide +kernel).symm
          | succ k ih => rw [Rat.pow_succ, Rat.pow_succ, Rat.inv_mul_rev, ih, Rat.mul_comm]
        rw [Rat.div_def, hinv])

open RationalPartialFractions

/-- A common radius, computed by finite rational comparisons. -/
def radius (center : Rat) : List Pole → Rat
  | [] => 1
  | p :: ps => if poleRadius p.center center <= radius center ps then
      poleRadius p.center center else radius center ps

private theorem denominator_tail (p : Pole) (ps : List Pole) (x : Rat)
    (hx : Polynomial.eval (denominator (p :: ps)) x ≠ 0) :
    x ≠ p.center ∧ Polynomial.eval (denominator ps) x ≠ 0 := by
  rw [denominator_cons_eval] at hx
  constructor
  · intro he
    rw [he, Rat.sub_self, Rat.pow_succ, Rat.mul_zero, Rat.zero_mul] at hx
    exact hx rfl
  · intro he
    rw [he, Rat.mul_zero] at hx
    exact hx rfl

theorem radius_pos (center : Rat) (poles : List Pole)
    (hc : Polynomial.eval (denominator poles) center ≠ 0) : 0 < radius center poles := by
  induction poles with
  | nil => exact (by decide : (0 : Rat) < 1)
  | cons p ps ih =>
      have ht := denominator_tail p ps center hc
      have hp := poleRadius_pos ht.1
      have hs := ih ht.2
      unfold radius
      split <;> assumption

theorem radius_le (center : Rat) (poles : List Pole) (p : Pole) (hp : p ∈ poles) :
    radius center poles <= poleRadius p.center center := by
  induction poles with
  | nil => simp at hp
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with he | ht
      · subst p
        unfold radius
        split <;> grind
      · have H := ih ht
        unfold radius
        split <;> grind

/-- The computed interval contains no pole of the original denominator. -/
theorem denominator_near (center r : Rat) (poles : List Pole)
    (hc : Polynomial.eval (denominator poles) center ≠ 0)
    (hr : ∀ p ∈ poles, r <= poleRadius p.center center)
    (x : Rat) (hx : inDomainInterval (center-r) (center+r) x) :
    Polynomial.eval (denominator poles) x ≠ 0 := by
  induction poles with
  | nil => simp only [denominator, Polynomial.eval, List.foldr, Rat.mul_zero, Rat.add_zero]; decide +kernel
  | cons p ps ih =>
      have ht := denominator_tail p ps center hc
      have hp := poleRadius_pos ht.1
      have ha := chart_apart p.center center r x (hr p (by simp)) hx
      have hxn : x-p.center ≠ 0 := by
        intro hz
        rw [hz, show qabs (0 : Rat) = 0 by decide +kernel] at ha
        grind
      have hrest := ih ht.2 (fun q hq => hr q (by simp [hq]))
      rw [denominator_cons_eval]
      have hpown : ∀ n : Nat, (x-p.center)^n ≠ 0 := by
        intro n
        induction n with
        | zero => rw [Rat.pow_zero]; decide +kernel
        | succ n ih => rw [Rat.pow_succ]; exact fun hz => (Rat.mul_eq_zero.mp hz).elim ih hxn
      exact fun hz => (Rat.mul_eq_zero.mp hz).elim (hpown _) hrest

def LinearChart (center r : Rat) : Term → Prop
  | .linear _ a _ => center ≠ a ∧ r <= poleRadius a center
  | .quadratic _ _ _ _ _ => False

private theorem removePole_charts (p q : List Rat) (a center r : Rat)
    (hc : center ≠ a) (hr : r <= poleRadius a center) (n : Nat) :
    ∀ t ∈ (removePole p q a n).terms, LinearChart center r t := by
  induction n generalizing p with
  | zero => simp [removePole]
  | succ n ih =>
      intro t ht
      change t ∈ Term.linear (coefficient p q a) a n ::
        (removePole (nextNumerator p q a) q a n).terms at ht
      rcases List.mem_cons.mp ht with he | hm
      · subst t; exact ⟨hc, hr⟩
      · exact ih _ t hm

theorem normalForm_charts (poles : List Pole) (p : List Rat) (center r : Rat)
    (hc : Polynomial.eval (denominator poles) center ≠ 0)
    (hr : ∀ q ∈ poles, r <= poleRadius q.center center) :
    ∀ t ∈ (normalForm poles p).terms, LinearChart center r t := by
  induction poles generalizing p with
  | nil => simp [normalForm]
  | cons q qs ih =>
      have ht := denominator_tail q qs center hc
      intro t hm
      change t ∈ (removePole p (denominator qs) q.center (q.order+1)).terms ++
        (normalForm qs (removePole p (denominator qs) q.center (q.order+1)).remainder).terms at hm
      rcases List.mem_append.mp hm with hb | hs
      · exact removePole_charts p _ q.center center r ht.1 (hr q (by simp)) _ t hb
      · exact ih _ ht.2 (fun q hq => hr q (by simp [hq])) t hs

def terms (center r : Rat) : (ts : List Term) →
    (∀ t ∈ ts, LinearChart center r t) →
    PrimitiveOn (fun x => sumTerms x ts) (center-r) (center+r)
  | [], _ => polynomial [] _ _
  | .linear c a n :: ts, hcharts =>
      (linear c a center r (hcharts (.linear c a n) (by simp)).1 (hcharts (.linear c a n) (by simp)).2 n).add
        (terms center r ts (fun t hm => hcharts t (by simp [hm])))
  | .quadratic A B a b n :: _, hcharts => False.elim (hcharts (.quadratic A B a b n) (by simp))

/-- End-to-end primitive construction for every admissible rationally split
denominator and every rational center in its domain. The radius is positive,
the evaluator is elementary, and the derivative is the original quotient. -/
def splitPrimitive (poles : List Pole) (p : List Rat) (hpoles : Admissible poles)
    (center : Rat) (hc : Polynomial.eval (denominator poles) center ≠ 0) :
    PrimitiveOn (fun x => Polynomial.eval p x / Polynomial.eval (denominator poles) x)
      (center-radius center poles) (center+radius center poles) := by
  let nf := normalForm poles p
  let r := radius center poles
  have hcharts := normalForm_charts poles p center r hc (radius_le center poles)
  let P := (polynomial nf.polynomial (center-r) (center+r)).add
    (terms center r nf.terms hcharts)
  exact P.congr (by
    intro x hx
    exact normalForm_identity poles p hpoles x
      (denominator_near center r poles hc (radius_le center poles) x hx))

/-- The same analytic theorem for a rational function with a checked rational
linear factorization, including any nonzero leading coefficient. -/
def ofFactorization (f : RatFun) (poles : List Pole) (leading : Rat)
    (_hleading : leading ≠ 0) (hpoles : Admissible poles)
    (hfactor : ∀ x, f.denominator x = leading * Polynomial.eval (denominator poles) x)
    (center : Rat) (hc : f.denominator center ≠ 0) :
    PrimitiveOn (fun x => f.numerator x / f.denominator x) (center-radius center poles) (center+radius center poles) := by
  have hsplit : Polynomial.eval (denominator poles) center ≠ 0 := by
    intro hz
    rw [hfactor, hz, Rat.mul_zero] at hc
    exact hc rfl
  let P := splitPrimitive poles (RationalExpressionNormalization.scale leading⁻¹ f.num)
    hpoles center hsplit
  exact P.congr (by
    intro x hx
    rw [RationalExpressionNormalization.eval_scale]
    change leading⁻¹ * Polynomial.eval f.num x / Polynomial.eval (denominator poles) x =
      f.numerator x / f.denominator x
    rw [hfactor]
    simp only [RatFun.numerator, Rat.div_def, Rat.inv_mul_rev]
    grind)

end RationalPrimitiveAssembly
end ComputableAnalysis
