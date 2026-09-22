import ComputableAnalysis.AlgebraicODE.Frobenius
import ComputableAnalysis.GeometricPowerSeries

/-! Effective convergence of the Frobenius factor. The root-gap hypothesis
includes the larger rational indicial root and repeated roots. The evaluator
represents the factor `Σ cₙ xⁿ`; it does not construct a branch of `x^r` or
assert analytic differentiation of the resulting interval function. -/
namespace ComputableAnalysis.AlgebraicODE.Fuchs.Frobenius
open FormalPowerSeries

theorem polynomial_absSum_nonneg (p : List Rat) : 0 ≤ ratListAbsSum p := by
  induction p with
  | nil => exact Rat.le_refl
  | cons a p ih =>
      have := qabs_nonneg a
      simp only [ratListAbsSum]
      grind

theorem polynomial_coeff_bound (p : List Rat) (n : Nat) :
    qabs (ofPolynomial p n) ≤ ratListAbsSum p := by
  induction p generalizing n with
  | nil => simp [ofPolynomial, ratListAbsSum, qabs]
  | cons a p ih =>
      cases n with
      | zero =>
          have := polynomial_absSum_nonneg p
          simp [ofPolynomial, ratListAbsSum]
          grind
      | succ n =>
          have := ih n
          have := qabs_nonneg a
          simpa only [ofPolynomial, List.getElem?_cons_succ, ratListAbsSum] using
            Rat.le_trans (ih n) (show ratListAbsSum p ≤ qabs a + ratListAbsSum p by grind)

/-- When `r` is a root, this is `r - r₂`, the gap to the other indicial root. -/
def Equation.rootGap (E : Equation) (r : Rat) : Rat :=
  2 * r - 1 + ofPolynomial E.p 0

theorem Equation.indicial_shift (E : Equation) {r : Rat} (hr : E.indicial r = 0)
    (n : Nat) :
    E.indicial (r + (n : Rat)) = (n : Rat) * ((n : Rat) + E.rootGap r) := by
  unfold Equation.indicial Equation.rootGap at *
  grind

theorem Equation.indicial_lower_bound (E : Equation) {r : Rat}
    (hr : E.indicial r = 0) (hg : 0 ≤ E.rootGap r) (n : Nat) :
    (n : Rat) * (n : Rat) ≤ E.indicial (r + (n : Rat)) := by
  rw [E.indicial_shift hr]
  have hn : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have := Rat.mul_nonneg hn hg
  grind

theorem Equation.nonresonant_of_rootGap (E : Equation) {r : Rat}
    (hr : E.indicial r = 0) (hg : 0 ≤ E.rootGap r) : E.Nonresonant r := by
  intro n
  have hn : (0 : Rat) < ((n+1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have := Rat.mul_pos hn hn
  have := E.indicial_lower_bound hr hg (n+1)
  grind

/-- A deliberately coarse, executable majorant; it needs no root search. -/
def Equation.growthBound (E : Equation) (r : Rat) : Rat :=
  1 + (qabs r + 1) * ratListAbsSum E.p + ratListAbsSum E.q

theorem Equation.growthBound_ge_one (E : Equation) (r : Rat) :
    1 ≤ E.growthBound r := by
  have hp := polynomial_absSum_nonneg E.p
  have hq := polynomial_absSum_nonneg E.q
  have hr := qabs_nonneg r
  have := Rat.mul_nonneg (show 0 ≤ qabs r + 1 by grind) hp
  unfold Equation.growthBound
  grind

theorem Equation.kernel_bound (E : Equation) (r : Rat) {k n : Nat}
    (hk : k < n) :
    qabs ((r + (k : Rat)) * ofPolynomial E.p (n-k) + ofPolynomial E.q (n-k))
      ≤ E.growthBound r * (n : Rat) := by
  have hk0 : (0 : Rat) ≤ (k : Rat) := Rat.natCast_nonneg
  have hkn : (k : Rat) < (n : Rat) := by exact_mod_cast hk
  have hn : (1 : Rat) ≤ (n : Rat) := by exact_mod_cast (show 1 ≤ n by omega)
  have hp := polynomial_coeff_bound E.p (n-k)
  have hq := polynomial_coeff_bound E.q (n-k)
  have hp0 := polynomial_absSum_nonneg E.p
  have hq0 := polynomial_absSum_nonneg E.q
  have hr0 := qabs_nonneg r
  have habs := qabs_add_le r (k : Rat)
  rw [qabs_eq_self_of_nonneg hk0] at habs
  have hscale := Rat.mul_le_mul_of_nonneg_left hn hr0
  have hr : qabs (r + (k : Rat)) ≤ (qabs r + 1) * (n : Rat) := by grind
  have hprod1 := Rat.mul_le_mul_of_nonneg_left hp (qabs_nonneg (r + (k : Rat)))
  have hprod2 := Rat.mul_le_mul_of_nonneg_right hr hp0
  have hqscale := Rat.mul_le_mul_of_nonneg_left hn hq0
  have hadd := qabs_add_le ((r + (k : Rat)) * ofPolynomial E.p (n-k))
    (ofPolynomial E.q (n-k))
  rw [qabs_mul] at hadd
  unfold Equation.growthBound
  grind

/-- Geometric coefficient growth follows from the derived recurrence.
No coefficient bound or convergence provider is assumed. -/
theorem Equation.coeff_growth (E : Equation) (r c0 : Rat)
    (hr : E.indicial r = 0) (hg : 0 ≤ E.rootGap r) (n : Nat) :
    qabs (E.coeff r c0 n) ≤ qabs c0 * E.growthBound r ^ n := by
  let R := E.growthBound r
  let c := E.coeff r c0
  have hR : 1 ≤ R := E.growthBound_ge_one r
  have hM : 0 ≤ qabs c0 := qabs_nonneg c0
  have hc := E.coeff_isSolution r c0 hr (E.nonresonant_of_rootGap hr hg)
  change qabs (c n) ≤ qabs c0 * R ^ n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simp [c]
      | succ n =>
          have hpower : 0 ≤ qabs c0 * R ^ n :=
            Rat.mul_nonneg hM (Rat.pow_nonneg (by grind))
          have hterm (k : Nat) (hk : k < n+1) :
              qabs (((r + (k : Rat)) * ofPolynomial E.p (n+1-k) +
                ofPolynomial E.q (n+1-k)) * c k) ≤
                R * ((n+1 : Nat) : Rat) * (qabs c0 * R ^ n) := by
            have hi := ih k hk
            have hp := Rat.mul_le_mul_of_nonneg_left
              (pow_mono_exponent hR (show k ≤ n by omega)) hM
            have hkern := E.kernel_bound r hk
            have hleft := Rat.mul_le_mul_of_nonneg_right hkern (qabs_nonneg (c k))
            have hfac : 0 ≤ R * ((n+1 : Nat) : Rat) :=
              Rat.mul_nonneg (by grind) Rat.natCast_nonneg
            have hright := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hi hp) hfac
            rw [qabs_mul]
            change qabs _ * qabs (c k) ≤ _
            change qabs _ ≤ R * _ at hkern
            grind
          have hsum := sumBelow_abs_le hterm
          have hres := hc (n+1)
          rw [E.residual_split] at hres
          have heq : E.indicial (r + ((n+1 : Nat) : Rat)) * c (n+1) =
              -E.lower r c (n+1) := by change _ + E.lower r c _ = 0 at hres; grind
          have hden := E.indicial_lower_bound hr hg (n+1)
          have hn : (0 : Rat) < ((n+1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
          have hnn := Rat.mul_pos hn hn
          have hd0 : 0 ≤ E.indicial (r + ((n+1 : Nat) : Rat)) := by grind
          have habs := congrArg qabs heq
          rw [qabs_mul, qabs_neg, qabs_eq_self_of_nonneg hd0] at habs
          have hmul := Rat.mul_le_mul_of_nonneg_right hden (qabs_nonneg (c (n+1)))
          change qabs (E.lower r c (n+1)) ≤ _ at hsum
          rw [Rat.pow_succ]
          apply Rat.le_of_mul_le_mul_right (c := ((n+1 : Nat) : Rat) * ((n+1 : Nat) : Rat))
          · grind
          · exact hnn

/-- A literal rational interval algorithm for the Frobenius factor. -/
def Equation.factorRaw (E : Equation) (r c0 x : Rat) : RealRaw :=
  geometricRaw (E.coeff r c0) (qabs c0) x

theorem Equation.factorRaw_valid (E : Equation) (r c0 x : Rat)
    (hr : E.indicial r = 0) (hg : 0 ≤ E.rootGap r)
    (hx : E.growthBound r * qabs x ≤ 1 / 2) : (E.factorRaw r c0 x).Valid :=
  geometricRaw_valid (qabs_nonneg c0) (Rat.le_trans (by decide) (E.growthBound_ge_one r))
    (E.coeff_growth r c0 hr hg) hx

theorem Equation.factorRaw_precision (E : Equation) (r c0 x : Rat) (eps : QPos) :
    ((E.factorRaw r c0 x).compute
      (RationalMajorant.halfDecayShift (4 * qabs c0) eps)).width ≤ eps.val :=
  geometricRaw_precision _ (qabs_nonneg c0) x eps

theorem Equation.factorRaw_contains_prefix (E : Equation) (r c0 x : Rat)
    (hr : E.indicial r = 0) (hg : 0 ≤ E.rootGap r)
    (hx : E.growthBound r * qabs x ≤ 1 / 2) {n m : Nat} (hnm : n ≤ m) :
    ((E.factorRaw r c0 x).compute n).lo ≤
      sumBelow (fun k => E.coeff r c0 k * x ^ k) m ∧
    sumBelow (fun k => E.coeff r c0 k * x ^ k) m ≤
      ((E.factorRaw r c0 x).compute n).hi :=
  geometricRaw_contains_prefix (qabs_nonneg c0)
    (Rat.le_trans (by decide) (E.growthBound_ge_one r)) (E.coeff_growth r c0 hr hg) hx hnm

end ComputableAnalysis.AlgebraicODE.Fuchs.Frobenius
