import ComputableAnalysis.GlobalBinomialChart
import ComputableAnalysis.GeometricSequence
import ComputableAnalysis.PolynomialIntegralWitness
import ComputableAnalysis.PolynomialIntegralComparison
import ComputableAnalysis.BinomialParameter

/-! Compact binomial integral computations on every interval separated from
base zero, with arbitrary represented-real exponents. Rational polynomial
integrals and uniform finite estimates supply the semantic witnesses. -/
namespace ComputableAnalysis.BinomialPower.Global
open FormalPowerSeries ZetaReal RealParameterSample Integral FinitePolynomial

def Chart.BoundsParameter (A : Chart) (p : Real) : Prop :=
  ∀ s, (p.compute 0).lo ≤ s → s ≤ (p.compute 0).hi → qabs (2-s) ≤ (A.order : Rat)

def Chart.observation (A : Chart) (p : Real) (n : Nat) : Nat := stage p (n+A.sampleShift)
def Chart.parameter (A : Chart) (p : Real) (n : Nat) : Rat := sample p (n+A.sampleShift)

theorem Chart.parameter_bound (A : Chart) {p : Real} (hp : A.BoundsParameter p) (n : Nat) :
    qabs (2-A.parameter p n) ≤ (A.order : Rat) :=
  hp _ (sample_initial p _).1 (sample_initial p _).2

def Chart.polynomial (A : Chart) (p : Real) (x : Rat) (n : Nat) : Rat :=
  powerPolynomial (A.parameter p n) (A.cutoff n) x

def Chart.integralPolynomial (A : Chart) (p : Real) (a b : Rat) (n : Nat) : Rat :=
  integratedTaylorPrefix (coefficient (A.parameter p n)) (A.cutoff n) b-
    integratedTaylorPrefix (coefficient (A.parameter p n)) (A.cutoff n) a

def Chart.value (A : Chart) (p : Real) (x : Rat) : RealRaw := GeometricSequence.raw (A.polynomial p x) 2

def Chart.integral (A : Chart) (p : Real) (a b : Rat) : RealRaw :=
  GeometricSequence.raw (A.integralPolynomial p a b) 2

theorem Chart.polynomial_external (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {x : Rat} (hx0 : 0 ≤ x) (hx : x ≤ A.radius) {n K : Nat} (hK : A.cutoff n ≤ K) {s : Rat}
    (hs : (p.compute (A.observation p n)).lo ≤ s ∧ s ≤ (p.compute (A.observation p n)).hi) :
    qabs (powerPolynomial s K x-A.polynomial p x n) ≤ 2*((1 : Rat)/2)^n := by
  have hn := p.valid.2.1 0 (A.observation p n) (Nat.zero_le _)
  have hsC : qabs (2-s) ≤ (A.order : Rat) := hp s (Rat.le_trans hn.1 hs.1) (Rat.le_trans hs.2 hn.2.2)
  have he := A.polynomial_parameter hsC (A.parameter_bound hp n) hx0 hx K
  have hd := point_sample p (n := n+A.sampleShift) hs
  have hm := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt A.parameterLip_pos)
  have hsmall := A.parameter_error n
  have ht := A.polynomial_tail (A.parameter_bound hp n) hx0 hx hK
  have htri := qabs_add_le
    (powerPolynomial s K x-powerPolynomial (A.parameter p n) K x)
    (powerPolynomial (A.parameter p n) K x-powerPolynomial (A.parameter p n) (A.cutoff n) x)
  change qabs (s-A.parameter p n) ≤ _ at hd
  change A.parameterLip*qabs (s-A.parameter p n) ≤ _ at hm
  rw [show (powerPolynomial s K x-powerPolynomial (A.parameter p n) K x)+
    (powerPolynomial (A.parameter p n) K x-powerPolynomial (A.parameter p n) (A.cutoff n) x) =
    powerPolynomial s K x-A.polynomial p x n by unfold polynomial; grind only] at htri
  grind only

theorem Chart.integralPolynomial_external (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius)
    {n K : Nat} (hK : A.cutoff n ≤ K) {s : Rat}
    (hs : (p.compute (A.observation p n)).lo ≤ s ∧ s ≤ (p.compute (A.observation p n)).hi) :
    qabs ((integratedTaylorPrefix (coefficient s) K b-integratedTaylorPrefix (coefficient s) K a)-
      A.integralPolynomial p a b n) ≤ 2*((1 : Rat)/2)^n := by
  have h := polynomial_integral_bound (coefficient s) (coefficient (A.parameter p n)) K (A.cutoff n)
    ha hab (by have := A.belowOne; grind) (by
      intro x hax hxb
      exact A.polynomial_external hp (Rat.le_trans ha hax) (Rat.le_trans hxb hb) hK hs)
  have hmul := Rat.mul_le_mul_of_nonneg_right (show b-a ≤ 1 by have := A.belowOne; grind)
    (show 0 ≤ 2*((1 : Rat)/2)^n by have := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := n); grind)
  exact Rat.le_trans h (by simpa only [Rat.one_mul] using hmul)

theorem Chart.value_valid (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {x : Rat} (hx0 : 0 ≤ x) (hx : x ≤ A.radius) : (A.value p x).Valid := by
  apply GeometricSequence.raw_valid (by decide : (0 : Rat) ≤ 2)
  intro n K hnK
  exact A.polynomial_external hp hx0 hx (A.cutoff_mono hnK)
    (sample_mem p (show n+A.sampleShift ≤ K+A.sampleShift by omega))

theorem Chart.integral_valid (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius) : (A.integral p a b).Valid := by
  apply GeometricSequence.raw_valid (by decide : (0 : Rat) ≤ 2)
  intro n K hnK
  exact A.integralPolynomial_external hp ha hab hb (A.cutoff_mono hnK)
    (sample_mem p (show n+A.sampleShift ≤ K+A.sampleShift by omega))

theorem Chart.value_contains (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {x : Rat} (hx0 : 0 ≤ x) (hx : x ≤ A.radius) {n K : Nat} (hK : A.cutoff n ≤ K) {s : Rat}
    (hs : (p.compute (A.observation p n)).lo ≤ s ∧ s ≤ (p.compute (A.observation p n)).hi) :
    ((A.value p x).compute n).lo ≤ powerPolynomial s K x ∧
      powerPolynomial s K x ≤ ((A.value p x).compute n).hi := by
  apply GeometricSequence.raw_contains
  intro j hj
  have hn := p.valid.2.1 _ _ (stage_mono p (show j+A.sampleShift ≤ n+A.sampleShift by omega))
  exact A.polynomial_external hp hx0 hx (Nat.le_trans (A.cutoff_mono hj) hK)
    ⟨Rat.le_trans hn.1 hs.1,Rat.le_trans hs.2 hn.2.2⟩

theorem Chart.integral_contains (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius)
    {n K : Nat} (hK : A.cutoff n ≤ K) {s : Rat}
    (hs : (p.compute (A.observation p n)).lo ≤ s ∧ s ≤ (p.compute (A.observation p n)).hi) :
    ((A.integral p a b).compute n).lo ≤
      integratedTaylorPrefix (coefficient s) K b-integratedTaylorPrefix (coefficient s) K a ∧
      integratedTaylorPrefix (coefficient s) K b-integratedTaylorPrefix (coefficient s) K a ≤
        ((A.integral p a b).compute n).hi := by
  apply GeometricSequence.raw_contains
  intro j hj
  have hn := p.valid.2.1 _ _ (stage_mono p (show j+A.sampleShift ≤ n+A.sampleShift by omega))
  exact A.integralPolynomial_external hp ha hab hb (Nat.le_trans (A.cutoff_mono hj) hK)
    ⟨Rat.le_trans hn.1 hs.1,Rat.le_trans hs.2 hn.2.2⟩

def Chart.function (A : Chart) (p : Real) (hp : A.BoundsParameter p)
    (a b : Rat) (ha : 0 ≤ a) (hb : b ≤ A.radius) : FunctionOnInterval :=
  onInterval (A.value p) a b (fun _ hx => A.value_valid hp (Rat.le_trans ha hx.1) (Rat.le_trans hx.2 hb))

/-- A constructed compact integral for every represented-real exponent on any
rational segment within the positive-base chart. -/
theorem Chart.hasIntegral (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius) :
    HasIntegral (A.function p hp a b ha hb) (A.integral p a b) := by
  apply hasIntegral_of_uniform_approximation
    (g := fun n x => RealRaw.ofRat (A.polynomial p x n)) (hg := fun _ _ _ => RealRaw.ofRat_valid _)
    (J := fun n => RealRaw.ofRat (A.integralPolynomial p a b n))
    (e := fun n => 2*((1 : Rat)/2)^n) hab (A.integral_valid hp ha hab hb)
  · intro n
    exact polynomial_hasIntegral (coefficient (A.parameter p n)) (A.cutoff n) ha hab (by have := A.belowOne; grind)
  · exact GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 2)
  · intro n x hx
    exact GeometricSequence.raw_within (A.value_valid hp (Rat.le_trans ha hx.1) (Rat.le_trans hx.2 hb)) n
  · intro n
    exact GeometricSequence.raw_within (A.integral_valid hp ha hab hb) n

/-- Displayed stage bounds, valid even when the input name has a slow rate. -/
theorem Chart.integral_stage_bounds (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius) (n : Nat) :
    A.integralPolynomial p a b n-2*((1 : Rat)/2)^n ≤ ((A.integral p a b).compute n).lo ∧
    ((A.integral p a b).compute n).hi ≤ A.integralPolynomial p a b n+2*((1 : Rat)/2)^n ∧
    0 ≤ ((A.integral p a b).compute n).width ∧
    ((A.integral p a b).compute n).width ≤ 4*((1 : Rat)/2)^n := by
  have h := GeometricSequence.raw_enclosure (A.integralPolynomial p a b) 2 n
  have hw := GeometricSequence.raw_width (A.integral_valid hp ha hab hb) n
  exact ⟨h.1,h.2,hw.1,by simpa only [Chart.integral,show (2 : Rat)*2=4 by decide +kernel] using hw.2⟩

end ComputableAnalysis.BinomialPower.Global
