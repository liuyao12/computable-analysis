import ComputableAnalysis.Basic

/-!
# Finite dyadic AM--GM certificates

This module contains only finite rational data.  A certificate is a complete
binary tree of nonnegative rational leaves; a tree of depth `k` has exactly
`2^k` leaves.  The main theorem is the corresponding finite dyadic
AM--GM inequality.
-/

namespace ComputableAnalysis

/-- A complete binary tree of nonnegative rational leaves. -/
inductive DyadicAMGM : Nat → Type
  | leaf (q : Rat) (hq : 0 ≤ q) : DyadicAMGM 0
  | branch {k : Nat} (left right : DyadicAMGM k) : DyadicAMGM (k + 1)

namespace DyadicAMGM

/-- The finite sum of the leaves. -/
def sum : {k : Nat} → DyadicAMGM k → Rat
  | _, leaf q _ => q
  | _, branch left right => sum left + sum right

/-- The finite product of the leaves. -/
def product : {k : Nat} → DyadicAMGM k → Rat
  | _, leaf q _ => q
  | _, branch left right => product left * product right

theorem sum_nonneg : {k : Nat} → (t : DyadicAMGM k) → 0 ≤ sum t
  | _, leaf q hq => hq
  | _, branch left right => Rat.add_nonneg (sum_nonneg left) (sum_nonneg right)

theorem product_nonneg : {k : Nat} → (t : DyadicAMGM k) → 0 ≤ product t
  | _, leaf q hq => hq
  | _, branch left right => Rat.mul_nonneg (product_nonneg left) (product_nonneg right)

private theorem rat_pow_le_pow {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Rat.pow_succ, Rat.pow_succ]
      calc
        x ^ n * x ≤ y ^ n * x :=
          Rat.mul_le_mul_of_nonneg_right (rat_pow_le_pow hx hxy n) hx
        _ ≤ y ^ n * y := Rat.mul_le_mul_of_nonneg_left hxy (Rat.pow_nonneg (Rat.le_trans hx hxy))

private theorem rat_mul_pow (x y : Rat) :
    ∀ n : Nat, (x * y) ^ n = x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Rat.pow_succ, rat_mul_pow x y n, Rat.pow_succ, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem dyadic_average_split {k : Nat} (s₁ s₂ : Rat) :
    (s₁ / ((2 ^ k : Nat) : Rat) + s₂ / ((2 ^ k : Nat) : Rat)) / 2 =
      (s₁ + s₂) / ((2 ^ (k + 1) : Nat) : Rat) := by
  rw [Nat.pow_succ, Rat.natCast_mul]
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The finite dyadic AM--GM bound for a complete binary certificate. -/
theorem product_le_average_pow :
    {k : Nat} → (t : DyadicAMGM k) →
      product t ≤ (sum t / ((2 ^ k : Nat) : Rat)) ^ (2 ^ k)
  | _, leaf q hq => by
      have hone : (1 : Rat)⁻¹ = 1 := by native_decide
      simp [sum, product, Rat.div_def, hone]
  | k + 1, branch left right => by
      let n : Nat := 2 ^ k
      let x : Rat := sum left / (n : Rat)
      let y : Rat := sum right / (n : Rat)
      have hn : 0 < (n : Rat) := by
        dsimp [n]
        exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega))
      have hx : 0 ≤ x := by
        dsimp [x]
        rw [Rat.div_def]
        exact Rat.mul_nonneg (sum_nonneg left) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
      have hy : 0 ≤ y := by
        dsimp [y]
        rw [Rat.div_def]
        exact Rat.mul_nonneg (sum_nonneg right) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
      have hleft := product_le_average_pow left
      have hright := product_le_average_pow right
      dsimp [sum, product]
      change product left * product right ≤ _
      have hprod : product left * product right ≤ x ^ n * y ^ n := by
        apply Rat.le_trans
          (Rat.mul_le_mul_of_nonneg_right hleft (product_nonneg right))
        exact Rat.mul_le_mul_of_nonneg_left hright (Rat.pow_nonneg hx)
      have hxy : x * y ≤ ((x + y) / 2) ^ 2 :=
        am_gm_rational_half (a := x) (b := y)
      have hxy0 : 0 ≤ x * y := Rat.mul_nonneg hx hy
      have hpow : (x * y) ^ n ≤ (((x + y) / 2) ^ 2) ^ n :=
        rat_pow_le_pow hxy0 hxy n
      have hfinal : x ^ n * y ^ n ≤ ((x + y) / 2) ^ (2 * n) := by
        calc
          x ^ n * y ^ n = (x * y) ^ n := by symm; exact rat_mul_pow x y n
          _ ≤ (((x + y) / 2) ^ 2) ^ n := hpow
          _ = ((x + y) / 2) ^ (2 * n) := by
            induction n with
            | zero => simp
            | succ n ih =>
                rw [Rat.pow_succ, ih, Nat.mul_succ]
                rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Rat.pow_succ,
                  show 2 = 1 + 1 by omega, Rat.pow_succ]
                grind [Rat.mul_assoc, Rat.mul_comm]
      have haverage : (x + y) / 2 =
          (sum left + sum right) / ((2 ^ (k + 1) : Nat) : Rat) := by
        dsimp [x, y, n]
        exact dyadic_average_split _ _
      have hbound := Rat.le_trans hprod hfinal
      rw [haverage] at hbound
      simpa [n, Nat.pow_succ, Nat.mul_comm, Rat.mul_assoc] using hbound

/- The denominator-cleared form is often the more convenient finite
   certificate: it compares the product and the raw leaf sum without first
   constructing the average. -/
theorem product_mul_card_pow_le_sum_pow :
    {k : Nat} → (t : DyadicAMGM k) →
      (((2 ^ k : Nat) : Rat) ^ (2 ^ k)) * product t ≤ (sum t) ^ (2 ^ k) := by
  intro k t
  let d : Rat := (2 ^ k : Nat)
  let n : Nat := 2 ^ k
  have hd : 0 ≤ d := by
    dsimp [d]
    exact Rat.natCast_nonneg
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.pow_pos (by omega : 0 < (2 : Nat))
  have h := product_le_average_pow t
  have hmul : d ^ n * product t ≤ d ^ n * (sum t / d) ^ n :=
    Rat.mul_le_mul_of_nonneg_left h (Rat.pow_nonneg hd)
  have hne : d ≠ 0 := by
    intro hzero
    rw [hzero] at hdpos
    exact Rat.lt_irrefl hdpos
  have hcancel : d ^ n * (sum t / d) ^ n = (sum t) ^ n := by
    have hinv : ∀ m : Nat, d ^ m * (d⁻¹) ^ m = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Rat.pow_succ, Rat.pow_succ]
          have hone := Rat.mul_inv_cancel d hne
          grind [Rat.mul_assoc, Rat.mul_comm]
    rw [Rat.div_def, rat_mul_pow]
    calc
      d ^ n * (sum t ^ n * (d⁻¹) ^ n) =
          sum t ^ n * (d ^ n * (d⁻¹) ^ n) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
      _ = sum t ^ n := by rw [hinv n, Rat.mul_one]
  dsimp [d, n] at hmul hcancel ⊢
  rw [hcancel] at hmul
  simpa using hmul

end DyadicAMGM

end ComputableAnalysis
