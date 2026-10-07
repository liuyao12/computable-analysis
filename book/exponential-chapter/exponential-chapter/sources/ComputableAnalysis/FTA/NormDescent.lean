import ComputableAnalysis.FTA.Descent
import ComputableAnalysis.FTA.Coercivity

/-! A finite uniform strict-decrease estimate for complex polynomial local
expansions. All parameters and error margins are rational. -/
namespace ComputableAnalysis.PolynomialNormDescent
open QComplex PolynomialCoercivity

def step (δ C A R : Rat) : Rat :=
  PolynomialDescent.step (-2*δ) [2*C*R+(A+R)^2]

private theorem pow_pos {t : Rat} (ht : 0 < t) (k : Nat) : 0 < t^k := by
  induction k with
  | zero => rw [Rat.pow_zero]; decide +kernel
  | succ k ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih ht

private theorem pow_le_one {t : Rat} (ht : 0 ≤ t) (ht1 : t ≤ 1) (k : Nat) : t^k ≤ 1 := by
  induction k with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
      rw [Rat.pow_succ]
      have hm := Rat.mul_le_mul_of_nonneg_right ih ht
      grind

private theorem pow_le_self {t : Rat} (ht : 0 ≤ t) (ht1 : t ≤ 1) {k : Nat} (hk : 0 < k) : t^k ≤ t := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [hn, Rat.pow_succ]
  have hm := Rat.mul_le_mul_of_nonneg_right (pow_le_one ht ht1 n) ht
  grind

private theorem conj_norm (c : QComplex) : normBound (conj c) = normBound c := by
  simp only [normBound, conj, qabs_neg]

private theorem real_product_upper (c r : QComplex) {C R : Rat}
    (hc : normBound c ≤ C) (hr : normBound r ≤ R) (hC : 0 ≤ C) :
    (mul (conj c) r).re ≤ C*R := by
  have hn := normBound_mul_le (conj c) r
  rw [conj_norm] at hn
  have h1 := Rat.mul_le_mul_of_nonneg_right hc (normBound_nonneg r)
  have h2 := Rat.mul_le_mul_of_nonneg_left hr hC
  have hre := self_le_qabs (mul (conj c) r).re
  have him := qabs_nonneg (mul (conj c) r).im
  unfold normBound at *
  grind

/-- Any positive step whose tail budget fits has the explicit norm decrease. -/
theorem decrease_of_budget (c a r : QComplex) (δ C A R t : Rat) (k : Nat)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 0 ≤ R) (hk : 0 < k)
    (hc : normBound c ≤ C) (ha : normBound a ≤ A) (hr : normBound r ≤ R)
    (hdir : (mul (conj c) a).re ≤ -δ) (htpos : 0 < t) (ht1 : t < 1)
    (hbudget : t*(2*C*R+(A+R)^2) ≤ δ) :
    normSq (add c (scaleRat (t^k) (add a (scaleRat t r)))) ≤ normSq c-t^k*δ := by
  have hspos := pow_pos htpos k
  have hsle := pow_le_self (Rat.le_of_lt htpos) (Rat.le_of_lt ht1) hk
  have hcross := real_product_upper c r hc hr hC
  let b := add a (scaleRat t r)
  have hb : normBound b ≤ A+R := by
    have hn := normBound_add_le a (scaleRat t r)
    rw [normBound_scaleRat, qabs_eq_self_of_nonneg (Rat.le_of_lt htpos)] at hn
    have h1 := Rat.mul_le_mul_of_nonneg_left hr (Rat.le_of_lt htpos)
    have h2 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ht1) hR
    change normBound (add a (scaleRat t r)) ≤ A+R
    grind
  have hbSq : normSq b ≤ (A+R)^2 := by
    have h := normSq_le_normBound_square b
    have h1 := Rat.mul_le_mul_of_nonneg_left hb (normBound_nonneg b)
    have h2 := Rat.mul_le_mul_of_nonneg_right hb (show 0 ≤ A+R by grind)
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind
  have hlinear : (mul (conj c) b).re ≤ -δ+t*(C*R) := by
    have heq : (mul (conj c) b).re = (mul (conj c) a).re+t*(mul (conj c) r).re := by
      simp only [b, conj, mul, add, scaleRat]
      grind
    have hm := Rat.mul_le_mul_of_nonneg_left hcross (Rat.le_of_lt htpos)
    rw [heq]
    grind
  have hlin := Rat.mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 2*t^k by grind)
  have hquad := Rat.mul_le_mul_of_nonneg_left hbSq (Rat.le_of_lt (Rat.mul_pos hspos hspos))
  have hsquare : 0 ≤ (A+R)^2 := Rat.pow_nonneg (show 0 ≤ A+R by grind)
  have hsprod := Rat.mul_le_mul_of_nonneg_left hsle
    (Rat.mul_nonneg (Rat.le_of_lt hspos) hsquare)
  have hbudget' := Rat.mul_le_mul_of_nonneg_left hbudget (Rat.le_of_lt hspos)
  have hid : normSq (add c (scaleRat (t^k) b)) =
      normSq c+2*t^k*(mul (conj c) b).re+t^k*t^k*normSq b := by
    simp only [normSq, add, scaleRat, mul, conj]
    grind
  change normSq (add c (scaleRat (t^k) b)) ≤ normSq c-t^k*δ
  rw [hid]
  grind


/-- A uniform step strictly reduces squared modulus when the first varying
coefficient points inward. The decrease has an explicit positive margin. -/
theorem strict_decrease (c a r : QComplex) (δ C A R : Rat) (k : Nat)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 0 ≤ R) (hk : 0 < k)
    (hc : normBound c ≤ C) (ha : normBound a ≤ A) (hr : normBound r ≤ R)
    (hdir : (mul (conj c) a).re ≤ -δ) :
    let t := step δ C A R
    0 < t ∧ t < 1 ∧
      normSq (add c (scaleRat (t^k) (add a (scaleRat t r)))) ≤ normSq c - t^k*δ := by
  let K := 2*C*R+(A+R)^2
  let t := step δ C A R
  have hK : 0 ≤ K := by
    have hCR := Rat.mul_nonneg hC hR
    have hs := Rat.pow_nonneg (show 0 ≤ A+R by grind) (n := 2)
    dsimp [K]
    grind
  have ht := PolynomialDescent.step_spec (-2*δ) [K] (by grind)
  have htpos : 0 < t := ht.1
  have ht1 : t < 1 := ht.2.1
  have hbudget : t*K ≤ δ := by
    have hb := ht.2.2
    change -2*δ+t*(K+t*0) ≤ (-2*δ)/2 at hb
    have hh : (-2*δ)/2 = -δ := by
      rw [Rat.div_def]
      have : (2 : Rat)*(2 : Rat)⁻¹=1 := by decide +kernel
      grind
    rw [hh] at hb
    grind
  exact ⟨htpos, ht1, decrease_of_budget c a r δ C A R t k
    hδ hC hA hR hk hc ha hr hdir htpos ht1 hbudget⟩

/-- Shrinking the computed step preserves the quantitative descent. -/
theorem decrease_at_smaller_step (c a r : QComplex) (δ C A R t : Rat) (k : Nat)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 0 ≤ R) (hk : 0 < k)
    (hc : normBound c ≤ C) (ha : normBound a ≤ A) (hr : normBound r ≤ R)
    (hdir : (mul (conj c) a).re ≤ -δ) (htpos : 0 < t)
    (htle : t ≤ step δ C A R) :
    t < 1 ∧ normSq (add c (scaleRat (t^k) (add a (scaleRat t r)))) ≤ normSq c-t^k*δ := by
  let K := 2*C*R+(A+R)^2
  have hK : 0 ≤ K := by
    have hCR := Rat.mul_nonneg hC hR
    have hs := Rat.pow_nonneg (show 0 ≤ A+R by grind) (n := 2)
    dsimp [K]
    grind
  have hs := PolynomialDescent.step_spec (-2*δ) [K] (by grind)
  have hbudget : step δ C A R * K ≤ δ := by
    have hb := hs.2.2
    change -2*δ + step δ C A R*(K+step δ C A R*0) ≤ (-2*δ)/2 at hb
    simp only [Rat.div_def] at hb
    grind
  have hb := Rat.mul_le_mul_of_nonneg_right htle hK
  have ht1 : t < 1 := by
    have h : step δ C A R < 1 := hs.2.1
    grind
  exact ⟨ht1, decrease_of_budget c a r δ C A R t k
    hδ hC hA hR hk hc ha hr hdir htpos ht1 (Rat.le_trans hb hbudget)⟩

end ComputableAnalysis.PolynomialNormDescent
