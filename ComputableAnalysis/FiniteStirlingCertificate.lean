import ComputableAnalysis.ExpProofs
import ComputableAnalysis.Pi

/-!
# A finite Stirling-ratio certificate

This is deliberately a bounded numerical certificate, not Stirling's
asymptotic formula.  It uses the existing finite compound-interest enclosure
for `e`, the existing finite Leibniz enclosure for `pi`, and an explicit
rational square-root bracket for the single test index `n = 10`.
-/

namespace ComputableAnalysis

/-- The finite rational Stirling-shaped ratio used by the certificate. -/
def finiteStirlingRatio (n : Nat) (e root : Rat) : Rat :=
  factorialRat n / (root * (((n : Rat) / e) ^ n))

/-- The existing finite exponential enclosure consumed by this certificate. -/
def finiteStirlingEInterval : QInterval := eCompoundInterest.compute 100

/-- The existing finite pi enclosure consumed by the square-root check. -/
def finiteStirlingPiInterval : QInterval := piLeibniz.compute 100

/-- A rational midpoint selected from the finite `e` enclosure. -/
def finiteStirlingEApprox : Rat :=
  (finiteStirlingEInterval.lo + finiteStirlingEInterval.hi) / 2

/-- A rational square-root representative for `sqrt (20 * pi)` at `n = 10`. -/
def finiteStirlingRootApprox : Rat := 793 / 100

/-! The ratio is a genuine finite rational expression whenever its two
    positive scale inputs are positive.  This is the denominator gate needed
    before transporting interval bounds through the Stirling-shaped formula. -/
theorem finiteStirlingRatio_pos {n : Nat} {e root : Rat}
    (he : 0 < e) (hroot : 0 < root) :
    0 < finiteStirlingRatio n e root := by
  unfold finiteStirlingRatio
  have hfact : 0 < factorialRat n := RationalMajorant.factorialRat_pos n
  have hdiv : ∀ {x y : Rat}, 0 < x → 0 < y → 0 < x / y := by
    intro x y hx hy
    rw [Rat.div_def]
    exact Rat.mul_pos hx ((Rat.inv_pos).2 hy)
  cases n with
  | zero =>
      simpa [factorialRat, factorial] using hdiv hfact hroot
  | succ n =>
      have hn : 0 < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.succ_pos n)
      have hbase : 0 < ((n + 1 : Nat) : Rat) / e := hdiv hn he
      have hpow : 0 < (((n + 1 : Nat) : Rat) / e) ^ (n + 1) :=
        Rat.pow_pos hbase
      have hden : 0 < root * (((n + 1 : Nat) : Rat) / e) ^ (n + 1) :=
        Rat.mul_pos hroot hpow
      exact hdiv hfact hden

theorem finiteStirlingEInterval_ordered :
    finiteStirlingEInterval.lo <= finiteStirlingEInterval.hi := by
  have h := ExpProofs.eCompoundInterest_ordered 100
  unfold finiteStirlingEInterval at h ⊢
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem finiteStirlingPiInterval_ordered :
    finiteStirlingPiInterval.lo <= finiteStirlingPiInterval.hi := by
  native_decide

theorem finiteStirlingEApprox_mem_interval :
    finiteStirlingEInterval.lo <= finiteStirlingEApprox ∧
      finiteStirlingEApprox <= finiteStirlingEInterval.hi := by
  native_decide

/- The square bracket is checked against the complete finite pi box: every
   pi value in that box makes the radicand `20*pi` lie between the two
   rational squares. -/
theorem finiteStirlingRootApprox_squared_bounds :
    (finiteStirlingRootApprox : Rat) ^ 2 <=
        20 * finiteStirlingPiInterval.hi ∧
      20 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApprox + 1 / 100) ^ 2 := by
  native_decide

/-! The actual finite ratio enclosure.  The deliberately modest bounds make
    the certificate robustly rational while still locating the ratio near one. -/
theorem finiteStirlingRatioAtTen_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox ∧
      finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox <=
        2 := by
  native_decide

theorem finiteStirlingRatioAtTen_positive :
    0 < finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox := by
  native_decide

/-! The broad enclosure above is useful as a denominator gate.  This tighter
    enclosure records the actual numerical content of the finite computation:
    the selected rational inputs place the Stirling-shaped ratio within one
    percent of one, without invoking an asymptotic limit. -/
theorem finiteStirlingRatioAtTen_unit_enclosure :
    (1 : Rat) <=
        finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox ∧
      finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox <=
        101 / 100 := by
  native_decide

end ComputableAnalysis
