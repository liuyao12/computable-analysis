import ComputableAnalysis.BinomialIntegral
import ComputableAnalysis.ReflectedPolynomialIntegral

/-! Compact reciprocal-power integrals at arbitrary represented exponents.
The independent integrand uses binomial coefficients at `1-x`; reflection is
justified by finite polynomial integrals before any improper limit is used. -/
namespace ComputableAnalysis.PowerIntegral
open FormalPowerSeries ZetaReal RealParameterSample Integral FinitePolynomial
open BinomialPower BinomialPower.Global

/-- Exponent parameter for the independent series representing `x^(-p)`. -/
def parameter (p : Real) : Real :=
  Real.ofRaw (RealRaw.sub (RealRaw.ofRat 2) p.preferred)
    (RealRaw.sub_valid (RealRaw.ofRat_valid 2) p.valid)

/-- Independent reciprocal-power evaluation on `0 < x ≤ 1`. -/
def value (p : Real) (x : Rat) : RealRaw := canonicalValue (parameter p) (1-x)

theorem value_valid (p : Real) {x : Rat} (hx : 0 < x) (hx1 : x ≤ 1) : (value p x).Valid :=
  canonicalValue_valid (parameter p) (by grind) (by grind)

def function (p : Real) (a b : Rat) (ha : 0 < a) (hb : b ≤ 1) : FunctionOnInterval :=
  onInterval (value p) a b (fun x hx => value_valid p (by grind) (Rat.le_trans hx.2 hb))

def compact (p : Real) (a b : Rat) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) : RealRaw :=
  canonicalIntegral (parameter p) (1-b) (1-a) (by grind) (by grind) (by grind)

/-- Actual compact integral witnesses on every positive rational segment in
`(0,1]`, without restricting the represented exponent to rational numbers. -/
theorem compact_hasIntegral (p : Real) {a b : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasIntegral (function p a b ha hb) (compact p a b ha hab hb) := by
  let s := parameter p
  let A := chart s (1-a) (by grind) (by grind)
  have hp := chart_bounds s (1-a) (by grind) (by grind)
  have hv := A.integral_valid hp (show 0 ≤ 1-b by grind) (show 1-b ≤ 1-a by grind) (Rat.le_refl)
  apply hasIntegral_of_uniform_approximation
    (g := fun n x => RealRaw.ofRat (taylorDerivativePrefix (coefficient (A.parameter s n)) (A.cutoff n) (1-x)))
    (hg := fun _ _ _ => RealRaw.ofRat_valid _)
    (J := fun n => RealRaw.ofRat (A.integralPolynomial s (1-b) (1-a) n))
    (e := fun n => 2*((1 : Rat)/2)^n) hab hv
  · intro n
    exact (reflected_polynomial_hasIntegral (coefficient (A.parameter s n)) (A.cutoff n)
      (Rat.le_of_lt ha) hab hb).exactRat_onInterval
  · exact GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 2)
  · intro n x hx
    have hx0 : 0 ≤ 1-x := by grind
    have hxA : 1-x ≤ A.radius := by change 1-x ≤ 1-a; grind
    have hraw := A.value_valid hp hx0 hxA
    have heq := canonicalValue_agrees A hp hx0 hxA
    have hnear := GeometricSequence.raw_within hraw n
    have h := hnear.congr_left (canonicalValue_valid s hx0 (by grind)) hraw heq
    change Within (value p x) (RealRaw.ofRat (powerPolynomial (A.parameter s n) (A.cutoff n) (1-x))) _ at h
    unfold powerPolynomial at h
    rw [polynomial_prefix] at h
    exact h
  · intro n
    exact GeometricSequence.raw_within hv n

/-- The endpoint computation corresponding to `x^(1-p)`. -/
def endpoint (p : Real) (x : Rat) : RealRaw := canonicalValue (shiftParameter (parameter p)) (1-x)

theorem endpoint_valid (p : Real) {x : Rat} (hx : 0 < x) (hx1 : x ≤ 1) : (endpoint p x).Valid :=
  canonicalValue_valid _ (by grind) (by grind)

theorem parameter_factor (p : Real) :
    (RealRaw.sub (RealRaw.ofRat 1) p.preferred).Equiv
      (RealRaw.sub (parameter p).preferred (RealRaw.ofRat 1)) := by
  intro n
  have ho := RealRaw.interval_order_of_valid _ p.valid n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change (1-(p.preferred.compute n).hi) ≤ (2-(p.preferred.compute n).lo)-1 ∧
    ((2-(p.preferred.compute n).hi)-1) ≤ 1-(p.preferred.compute n).lo
  constructor <;> grind only

/-- Exact normalized compact formula for arbitrary valid represented `p`.
It stays meaningful at `p=1`; no equality test at the threshold is performed. -/
theorem compact_closedForm (p : Real) {a b : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    (RealRaw.mul (RealRaw.sub (RealRaw.ofRat 1) p.preferred) (compact p a b ha hab hb)).Equiv
      (RealRaw.sub (endpoint p b) (endpoint p a)) := by
  have hI := compact_hasIntegral p ha hab hb
  have hL := RealRaw.sub_valid (RealRaw.ofRat_valid 1) p.valid
  have hR := RealRaw.sub_valid (parameter p).valid (RealRaw.ofRat_valid 1)
  have he := RealRaw.mul_equiv hL hR hI.valid hI.valid (parameter_factor p) (RealRaw.equiv_refl _ hI.valid)
  exact RealRaw.equiv_trans (RealRaw.mul_valid hL hI.valid) (RealRaw.mul_valid hR hI.valid)
    (RealRaw.sub_valid (endpoint_valid p (by grind) hb) (endpoint_valid p ha (by grind)))
    he (canonicalIntegral_closedForm (parameter p) (a := 1-b) (b := 1-a) (by grind) (by grind) (by grind))

theorem supplied_closedForm (p : Real) {a b : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) {I : RealRaw}
    (hI : HasIntegral (function p a b ha hb) I) :
    (RealRaw.mul (RealRaw.sub (RealRaw.ofRat 1) p.preferred) I).Equiv
      (RealRaw.sub (endpoint p b) (endpoint p a)) := by
  have hc := compact_hasIntegral p ha hab hb
  have hP := RealRaw.sub_valid (RealRaw.ofRat_valid 1) p.valid
  have he := RealRaw.mul_equiv hP hP hI.valid hc.valid (RealRaw.equiv_refl _ hP) (hI.unique hc)
  exact RealRaw.equiv_trans (RealRaw.mul_valid hP hI.valid) (RealRaw.mul_valid hP hc.valid)
    (RealRaw.sub_valid (endpoint_valid p (by grind) hb) (endpoint_valid p ha (by grind)))
    he (compact_closedForm p ha hab hb)

theorem value_equiv {p q : Real} (heq : p.Equiv q) {x : Rat}
    (hx : 0 < x) (hx1 : x ≤ 1) : (value p x).Equiv (value q x) := by
  have hs := RealRaw.sub_equiv (RealRaw.ofRat_valid 2) (RealRaw.ofRat_valid 2) p.valid q.valid
    (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 2)) heq
  exact canonicalValue_equiv (p := parameter p) (q := parameter q) hs (by grind) (by grind)

theorem compact_equiv {p q : Real} (heq : p.Equiv q) {a b : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    (compact p a b ha hab hb).Equiv (compact q a b ha hab hb) := by
  have hs := RealRaw.sub_equiv (RealRaw.ofRat_valid 2) (RealRaw.ofRat_valid 2) p.valid q.valid
    (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 2)) heq
  exact canonicalIntegral_equiv (p := parameter p) (q := parameter q) hs (by grind) (by grind) (by grind)

end ComputableAnalysis.PowerIntegral
