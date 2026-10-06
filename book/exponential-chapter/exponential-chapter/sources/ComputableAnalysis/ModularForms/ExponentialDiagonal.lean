import ComputableAnalysis.ModularForms.ComplexBinomial
import ComputableAnalysis.FiniteExponentialProduct

/-! Exact finite factorial Cauchy diagonals on represented complex values.
No convergence or infinite product identity is assumed here. -/
namespace ComputableAnalysis.ModularForms.ExponentialDiagonal
open RiemannHilbert ComplexRaw

def rationalValue (r : Rat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.scaleRat r 1

theorem rationalValue_mul (r s : Rat) :
    rationalValue r * rationalValue s = rationalValue (r*s) := by
  unfold rationalValue
  rw [ComplexRawQuotient.scaleRat_mul_scaleRat]
  congr 1
  grind

theorem rationalValue_nat (n : Nat) :
    rationalValue (n : Rat) = (n : ScalarAlgebra.Value) := by
  exact (ScalarAlgebra.natural_scale n).symm

def coefficient (n : Nat) : ScalarAlgebra.Value :=
  rationalValue (FormalPowerSeries.expCoeff n)

theorem coefficient_product (n k : Nat) (hk : k ≤ n) :
    coefficient k * coefficient (n-k) =
      coefficient n * (FiniteCounting.combination n k : ScalarAlgebra.Value) := by
  unfold coefficient
  rw [rationalValue_mul,
    FiniteExponentialProduct.expCoeff_mul_expCoeff_eq_expCoeff_mul_combination n k hk,
    ← rationalValue_mul, rationalValue_nat]

def term (n k : Nat) (x y : ScalarAlgebra.Value) : ScalarAlgebra.Value :=
  coefficient k * x^k * (coefficient (n-k) * y^(n-k))

theorem term_binomial (n k : Nat) (hk : k ≤ n) (x y : ScalarAlgebra.Value) :
    term n k x y = coefficient n * ComplexBinomial.binomialTerm n k y x := by
  unfold term ComplexBinomial.binomialTerm
  have h := coefficient_product n k hk
  grind

def diagonalPrefix (n : Nat) (x y : ScalarAlgebra.Value) : Nat → ScalarAlgebra.Value
  | 0 => 0
  | k+1 => diagonalPrefix n x y k + term n k x y

theorem diagonalPrefix_binomial (n count : Nat) (hc : count ≤ n+1)
    (x y : ScalarAlgebra.Value) :
    diagonalPrefix n x y count = coefficient n * ComplexBinomial.binomialSum n y x count := by
  induction count with
  | zero =>
    simp only [diagonalPrefix, ComplexBinomial.binomialSum]
    grind
  | succ k ih =>
    rw [diagonalPrefix, ComplexBinomial.binomialSum, ih (by omega), term_binomial n k (by omega)]
    grind

/-- Every complete finite Cauchy diagonal has the factorial coefficient
of the sum of its two arbitrary represented complex inputs. -/
theorem complete (n : Nat) (x y : ScalarAlgebra.Value) :
    diagonalPrefix n x y (n+1) = coefficient n * (x+y)^n := by
  rw [diagonalPrefix_binomial n (n+1) (Nat.le_refl _), ComplexBinomial.binomialSum_eq_pow,
    ComplexRawQuotient.add_comm y x]

theorem rationalValue_raw (r : Rat) :
    ComplexRawQuotient.ofQComplex ⟨r,0⟩ = rationalValue r := by
  change ComplexRawQuotient.ofRaw (ofQComplex ⟨r,0⟩) _ =
    ComplexRawQuotient.ofRaw (scaleRat r (ofQComplex QComplex.one)) _
  apply ComplexRawQuotient.ofRaw_eq_ofRaw
  intro k
  apply (compareAt_overlap_iff _ _ k k).mpr
  simp only [ofQComplex, scaleRat, QBox.scaleRat, QComplex.one]
  split <;> simp [QBox.Overlaps, QComplex.le_def, Rat.mul_one, Rat.mul_zero]

def rawTerm (n k : Nat) (x y : ComplexRaw) : ComplexRaw :=
  mul (scaleRat (FormalPowerSeries.expCoeff k) (LocalODE.power x k))
    (scaleRat (FormalPowerSeries.expCoeff (n-k)) (LocalODE.power y (n-k)))

theorem rawTerm_valid (n k : Nat) (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) :
    (rawTerm n k x y).Valid :=
  mul_valid (scaleRat_valid (LocalODE.power_valid x hx k))
    (scaleRat_valid (LocalODE.power_valid y hy (n-k)))

def rawPrefix (n : Nat) (x y : ComplexRaw) : Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (rawPrefix n x y k) (rawTerm n k x y)

theorem rawPrefix_valid (n count : Nat) (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) :
    (rawPrefix n x y count).Valid := by
  induction count with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact add_valid ih (rawTerm_valid n k x y hx hy)

theorem power_class (x : ComplexRaw) (hx : x.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (LocalODE.power x n) (LocalODE.power_valid x hx n) =
      (ComplexRawQuotient.ofRaw x hx)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ComplexRawQuotient.ofRaw (LocalODE.power x n) (LocalODE.power_valid x hx n) *
      ComplexRawQuotient.ofRaw x hx = _
    rw [ih]
    rfl

theorem rawTerm_class (n k : Nat) (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) :
    ComplexRawQuotient.ofRaw (rawTerm n k x y) (rawTerm_valid n k x y hx hy) =
      term n k (ComplexRawQuotient.ofRaw x hx) (ComplexRawQuotient.ofRaw y hy) := by
  change ComplexRawQuotient.scaleRat _ (ComplexRawQuotient.ofRaw (LocalODE.power x k) (LocalODE.power_valid x hx k)) *
    ComplexRawQuotient.scaleRat _ (ComplexRawQuotient.ofRaw (LocalODE.power y (n-k)) (LocalODE.power_valid y hy (n-k))) = _
  rw [power_class, power_class]
  unfold term coefficient rationalValue
  have hs (r : Rat) (v : ScalarAlgebra.Value) :
      ComplexRawQuotient.scaleRat r 1 * v = ComplexRawQuotient.scaleRat r v := by
    rw [← ComplexRawQuotient.scaleRat_mul]
    congr 1
    grind
  rw [hs, hs]

theorem rawPrefix_class (n count : Nat) (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) :
    ComplexRawQuotient.ofRaw (rawPrefix n x y count) (rawPrefix_valid n count x y hx hy) =
      diagonalPrefix n (ComplexRawQuotient.ofRaw x hx) (ComplexRawQuotient.ofRaw y hy) count := by
  induction count with
  | zero => rfl
  | succ k ih =>
    change ComplexRawQuotient.ofRaw (rawPrefix n x y k) (rawPrefix_valid n k x y hx hy) +
      ComplexRawQuotient.ofRaw (rawTerm n k x y) (rawTerm_valid n k x y hx hy) = _
    rw [ih, rawTerm_class]
    rfl

/-- Exact equality of the executable finite diagonal for arbitrary valid raw
inputs. This is independent of the choice of their names. -/
theorem raw_complete (n : Nat) (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) :
    (rawPrefix n x y (n+1)).Equiv
      (scaleRat (FormalPowerSeries.expCoeff n) (LocalODE.power (add x y) n)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := rawPrefix_valid n (n+1) x y hx hy)
    (hright := scaleRat_valid (LocalODE.power_valid _ (add_valid hx hy) n))
  rw [rawPrefix_class n (n+1) x y hx hy, complete]
  change coefficient n * (ComplexRawQuotient.ofRaw x hx + ComplexRawQuotient.ofRaw y hy)^n =
    ComplexRawQuotient.scaleRat _ (ComplexRawQuotient.ofRaw (LocalODE.power (add x y) n) (LocalODE.power_valid _ (add_valid hx hy) n))
  rw [power_class (add x y) (add_valid hx hy) n]
  unfold coefficient rationalValue
  rw [← ComplexRawQuotient.scaleRat_mul]
  congr 1
  rw [ComplexRawQuotient.ofRaw_add x y hx hy]
  grind

end ComputableAnalysis.ModularForms.ExponentialDiagonal
