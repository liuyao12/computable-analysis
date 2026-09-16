import ComputableAnalysis.PowerSeries

/-!
# The finite arithmetic at both ends of a cosine-moment irrationality argument

No integral, real-number program, pi, or trigonometric function occurs in these
statements. The missing analytic client must prove the stated integer bounds;
these conditional arithmetic lemmas do not themselves prove irrationality of pi.
-/
namespace ComputableAnalysis.CartwrightArithmetic

/-- Consecutive values of P₀ = P₁ = 1 and
Pₙ₊₂(z) = (2n+3)Pₙ₊₁(z) - z Pₙ(z). -/
def polynomialPair (z : Rat) : Nat → Rat × Rat
  | 0 => (1, 1)
  | n+1 => let p := polynomialPair z n
           (p.2, (2*(n : Rat)+3)*p.2-z*p.1)

def polynomialValue (z : Rat) (n : Nat) : Rat := (polynomialPair z n).1

/-- Clearing denominators can be done by an integer recurrence alone. -/
def integerPair (a b : Int) : Nat → Int × Int
  | 0 => (1, b)
  | n+1 => let p := integerPair a b n
           (p.2, (2*(n : Int)+3)*b*p.2-a*b*p.1)

def integerValue (a b : Int) (n : Nat) : Int := (integerPair a b n).1

/-- Exact rational denominator clearing, with both consecutive terms tracked. -/
theorem denominator_pair (a b : Int) (hb : (b : Rat) ≠ 0) (n : Nat) :
    ((integerPair a b n).1 : Rat) = (b : Rat)^n*(polynomialPair ((a : Rat)/(b : Rat)) n).1 ∧
    ((integerPair a b n).2 : Rat) = (b : Rat)^(n+1)*(polynomialPair ((a : Rat)/(b : Rat)) n).2 := by
  induction n with
  | zero => simp [integerPair, polynomialPair]
  | succ n ih =>
    simp only [integerPair, polynomialPair]
    constructor
    · exact ih.2
    · simp only [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_add]
      simp only [Rat.intCast_ofNat, Rat.intCast_natCast]
      rw [ih.1, ih.2]
      have hc := Rat.mul_inv_cancel (b : Rat) hb
      simp only [Rat.pow_succ, Rat.div_def]
      grind

/-- The integer emitted by the recurrence is precisely bⁿPₙ(a/b). -/
theorem denominator_cleared (a b : Int) (hb : (b : Rat) ≠ 0) (n : Nat) :
    (integerValue a b n : Rat) = (b : Rat)^n*polynomialValue ((a : Rat)/(b : Rat)) n :=
  (denominator_pair a b hb n).1

/-- Bound a block of k factors of a factorial from below. -/
theorem factorial_tail_lower (m k : Nat) : m^k * factorial m ≤ factorial (m+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      m^(k+1)*factorial m = m*(m^k*factorial m) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ m*factorial (m+k) := Nat.mul_le_mul_left m ih
      _ ≤ (m+k+1)*factorial (m+k) := Nat.mul_le_mul_right _ (by omega)
      _ = factorial (m+(k+1)) := by rw [show m+(k+1)=(m+k)+1 by omega, factorial]

/-- A finite witness replaces any appeal to factorial asymptotics. -/
def witnessIndex (a : Nat) : Nat := 2*(a*a)

theorem factorial_dominates (a : Nat) (ha : 0 < a) :
    2*a^(witnessIndex a) < 2^(witnessIndex a)*factorial (witnessIndex a) := by
  let m := a*a
  have hm : 0 < m := Nat.mul_pos ha ha
  have htail := factorial_tail_lower m m
  have hfact : 1 ≤ factorial m := by have h := FormalPowerSeries.factorial_ne_zero m; omega
  have hp : m^m ≤ factorial (m+m) := by
    have hmul := Nat.mul_le_mul_left (m^m) hfact
    simp only [Nat.mul_one] at hmul
    exact Nat.le_trans hmul htail
  have he : a^(witnessIndex a) = m^m := by
    change a^(2*m) = (a*a)^m
    rw [Nat.pow_mul, Nat.pow_two]
  have hn : witnessIndex a = m+m := by dsimp [witnessIndex, m]; omega
  have h2 : 2 < 2^(witnessIndex a) := by
    have hh : 2 ≤ witnessIndex a := by dsimp [witnessIndex]; dsimp [m] at hm; omega
    have hpow := Nat.pow_le_pow_right (n:=2) (by omega) hh
    change 2^2 ≤ 2^(witnessIndex a) at hpow
    omega
  have pos : 0 < a^(witnessIndex a) := Nat.pow_pos ha
  calc
    2*a^(witnessIndex a) < 2^(witnessIndex a)*a^(witnessIndex a) :=
      Nat.mul_lt_mul_of_pos_right h2 pos
    _ ≤ 2^(witnessIndex a)*factorial (witnessIndex a) := by
      apply Nat.mul_le_mul_left
      rw [he, hn]
      exact hp

/-- The arithmetic consumer of the analytic estimate.
The client supplies a positive integer and a denominator-cleared upper bound;
this theorem knows nothing about the origin of that bound. -/
theorem integer_obstruction (a : Nat) (ha : 0 < a) (k : Int) (hk : 0 < k)
    (bound : k * ((2^(witnessIndex a)*factorial (witnessIndex a) : Nat) : Int) ≤
      ((2*a^(witnessIndex a) : Nat) : Int)) : False := by
  have h := factorial_dominates a ha
  have hc : ((2*a^(witnessIndex a) : Nat) : Int) <
      ((2^(witnessIndex a)*factorial (witnessIndex a) : Nat) : Int) := by exact_mod_cast h
  have hz : (0 : Int) ≤ ((2^(witnessIndex a)*factorial (witnessIndex a) : Nat) : Int) := by omega
  have hlow := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ k by omega) hz
  simp only [Int.one_mul] at hlow
  omega

/-- The complete final contradiction for any integer sequence with the required bounds.
This is conditional on those bounds; their proof is the separate calculus task. -/
theorem no_positive_small_sequence (a : Nat) (ha : 0 < a) (K : Nat → Int)
    (positive : ∀ n, 0 < K n)
    (small : ∀ n, K n * ((2^n*factorial n : Nat) : Int) ≤ ((2*a^n : Nat) : Int)) : False :=
  integer_obstruction a ha (K (witnessIndex a)) (positive _) (small _)

end ComputableAnalysis.CartwrightArithmetic
