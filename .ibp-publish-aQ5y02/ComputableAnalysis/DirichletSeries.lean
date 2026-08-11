import ComputableAnalysis.FTC

/-!
# Dirichlet series

Computable Dirichlet-series style algorithms: zeta values, Dirichlet
L-functions, and the Dirichlet beta value behind Leibniz pi.
-/

namespace ComputableAnalysis

namespace DirichletSeries

def zetaTwoTerm (k : Nat) : Rat :=
  let m : Rat := ((k + 1 : Nat) : Rat)
  1 / (m * m)

/-- The finite partial sum `sum_{k=1}^n 1/k^2`. -/
def zetaTwoPartial : Nat -> Rat
  | 0 => 0
  | n + 1 => zetaTwoPartial n + zetaTwoTerm n

theorem zetaTwoTerm_nonneg (k : Nat) : 0 <= zetaTwoTerm k := by
  unfold zetaTwoTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  exact Rat.le_of_lt (by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 (Rat.mul_pos hmpos hmpos))

theorem zetaTwoPartial_le_succ (n : Nat) :
    zetaTwoPartial n <= zetaTwoPartial (n + 1) := by
  change zetaTwoPartial n <= zetaTwoPartial n + zetaTwoTerm n
  grind [zetaTwoTerm_nonneg n]

theorem zetaTwoPartial_le_of_le {n m : Nat} :
    n <= m -> zetaTwoPartial n <= zetaTwoPartial m := by
  intro h
  induction h with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (zetaTwoPartial_le_succ _)

/-- A finite tail after the first `n` terms:
`sum_{j=0}^{count-1} 1/(n+j+1)^2`. -/
def zetaTwoFiniteTail (n : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 => zetaTwoFiniteTail n count + zetaTwoTerm (n + count)

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

/-- One term of the zeta tail is bounded by the corresponding telescoping
difference:

`1/(m+1)^2 <= 1/m - 1/(m+1)`.
-/
theorem zetaTwoTerm_le_telescopeStep (m : Nat) (hm : 0 < m) :
    zetaTwoTerm m <=
      1 / (m : Rat) - 1 / ((m + 1 : Nat) : Rat) := by
  unfold zetaTwoTerm
  let M : Rat := (m : Rat)
  let S : Rat := ((m + 1 : Nat) : Rat)
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hSpos : 0 < S := by
    dsimp [S]
    exact (Rat.natCast_pos).2 (Nat.succ_pos m)
  have hMne : M ≠0 := Rat.ne_of_gt hMpos
  have hSne : S ≠0 := Rat.ne_of_gt hSpos
  have hSSne : S * S ≠0 := by
    exact Rat.ne_of_gt (Rat.mul_pos hSpos hSpos)
  have hMleS : M <= S := by
    dsimp [M, S]
    exact_mod_cast (Nat.le_succ m)
  apply Rat.le_of_mul_le_mul_right (c := (S * S) * M)
  · calc
      (1 / (S * S)) * ((S * S) * M) = M := by
        rw [Rat.div_def]
        have hcancel : (S * S) * (S * S)⁻¹= 1 :=
          Rat.mul_inv_cancel (S * S) hSSne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= S := hMleS
      _ = (1 / M - 1 / S) * ((S * S) * M) := by
        rw [Rat.div_def, Rat.div_def]
        have hMcancel : M * M⁻¹= 1 := Rat.mul_inv_cancel M hMne
        have hScancel : S * S⁻¹= 1 := Rat.mul_inv_cancel S hSne
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
  · exact Rat.mul_pos (Rat.mul_pos hSpos hSpos) hMpos

def telescopingTailBound (n : Nat) (count : Nat) : Rat :=
  1 / (n : Rat) - 1 / ((n + count : Nat) : Rat)

private theorem telescopingTailBound_step (n : Nat) (count : Nat) :
    telescopingTailBound n count +
      (1 / ((n + count : Nat) : Rat) -
        1 / (((n + count) + 1 : Nat) : Rat)) =
      telescopingTailBound n (count + 1) := by
  unfold telescopingTailBound
  have hnat : n + (count + 1) = (n + count) + 1 := by omega
  rw [hnat]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Finite telescoping proof of the zeta(2) tail estimate:

`sum_{j=0}^{count-1} 1/(n+j+1)^2 <= 1/n - 1/(n+count)`.
-/
theorem zetaTwoFiniteTail_le_telescoping
    (n : Nat) (hn : 0 < n) (count : Nat) :
    zetaTwoFiniteTail n count <= telescopingTailBound n count := by
  induction count with
  | zero =>
      unfold zetaTwoFiniteTail telescopingTailBound
      grind [Rat.sub_eq_add_neg]
  | succ count ih =>
      unfold zetaTwoFiniteTail
      have hstep :
          zetaTwoTerm (n + count) <=
            1 / ((n + count : Nat) : Rat) -
              1 / (((n + count) + 1 : Nat) : Rat) :=
        zetaTwoTerm_le_telescopeStep (n + count) (Nat.add_pos_left hn count)
      calc
        zetaTwoFiniteTail n count + zetaTwoTerm (n + count)
            <= telescopingTailBound n count +
                (1 / ((n + count : Nat) : Rat) -
                  1 / (((n + count) + 1 : Nat) : Rat)) :=
              rat_add_le_add ih hstep
        _ = telescopingTailBound n (count + 1) :=
              telescopingTailBound_step n count

/-- The finite tail estimate in the coarser form used by the interval
algorithm. -/
theorem zetaTwoFiniteTail_le_tailBound (n : Nat) (hn : 0 < n) (count : Nat) :
    zetaTwoFiniteTail n count <= 1 / (n : Rat) := by
  have htel := zetaTwoFiniteTail_le_telescoping n hn count
  have hdenpos : 0 < ((n + count : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.add_pos_left hn count)
  have hnonneg : 0 <= 1 / ((n + count : Nat) : Rat) :=
    Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 hdenpos)
  exact Rat.le_trans htel (by
    unfold telescopingTailBound
    grind [Rat.sub_eq_add_neg])

/-- The endpoint padding used by the Basel-series interval algorithm.

This is part of the raw algorithm's definition.  The finite telescoping
lemmas above explain why this is the traditional tail padding, but validity
of the raw real only uses the interval order, nesting, and width shrinking
proved below. -/
def zetaTwoTailBound (n : Nat) : Rat :=
  if n = 0 then 2 else 1 / (n : Rat)

def zetaTwoUpper (n : Nat) : Rat :=
  zetaTwoPartial n + zetaTwoTailBound n

theorem zetaTwoUpper_succ_le (n : Nat) (hn : 0 < n) :
    zetaTwoUpper (n + 1) <= zetaTwoUpper n := by
  unfold zetaTwoUpper zetaTwoTailBound
  rw [if_neg (Nat.succ_ne_zero n)]
  rw [if_neg (Nat.ne_of_gt hn)]
  change zetaTwoPartial n + zetaTwoTerm n +
      1 / ((n + 1 : Nat) : Rat) <=
    zetaTwoPartial n + 1 / (n : Rat)
  have hstep := zetaTwoTerm_le_telescopeStep n hn
  have hwithPartial :
      zetaTwoPartial n + zetaTwoTerm n <=
        zetaTwoPartial n +
          (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) :=
    rat_add_le_add (by exact Rat.le_refl) hstep
  calc
    zetaTwoPartial n + zetaTwoTerm n +
        1 / ((n + 1 : Nat) : Rat)
        <= zetaTwoPartial n +
            (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) +
              1 / ((n + 1 : Nat) : Rat) :=
          rat_add_le_add hwithPartial (by exact Rat.le_refl)
    _ = zetaTwoPartial n + 1 / (n : Rat) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem zetaTwoUpper_le_of_le {n m : Nat}
    (hn : 0 < n) (h : n <= m) :
    zetaTwoUpper m <= zetaTwoUpper n := by
  induction h with
  | refl => exact Rat.le_refl
  | step h ih =>
      have hmpos : 0 < _ := Nat.lt_of_lt_of_le hn h
      exact Rat.le_trans (zetaTwoUpper_succ_le _ hmpos) ih

/-- Computable interval for `zeta(2)` at stage `n`.

The lower endpoint is the first `n` terms.  The upper endpoint adds the
elementary rational tail bound `1/n`.
-/
def zetaTwoInterval (n : Nat) : QInterval :=
  let s := zetaTwoPartial n
  { lo := s, hi := s + zetaTwoTailBound n }

theorem zetaTwoInterval_width (n : Nat) :
    (zetaTwoInterval n).width = zetaTwoTailBound n := by
  unfold zetaTwoInterval QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem zetaTwoInterval_width_nonneg (n : Nat) :
    0 <= (zetaTwoInterval n).width := by
  rw [zetaTwoInterval_width]
  unfold zetaTwoTailBound
  by_cases hn0 : n = 0
  · simp [hn0]
    native_decide
  · simp [hn0]
    exact Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn0)))

theorem zetaTwoInterval_ordered (n : Nat) :
    (zetaTwoInterval n).lo <= (zetaTwoInterval n).hi := by
  have h := zetaTwoInterval_width_nonneg n
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem zetaTwoInterval_nested (n m : Nat) (hnm : n <= m) :
    (zetaTwoInterval n).lo <= (zetaTwoInterval m).lo /\
      (zetaTwoInterval m).lo <= (zetaTwoInterval m).hi /\
      (zetaTwoInterval m).hi <= (zetaTwoInterval n).hi := by
  constructor
  · change zetaTwoPartial n <= zetaTwoPartial m
    exact zetaTwoPartial_le_of_le hnm
  · constructor
    · exact zetaTwoInterval_ordered m
    · change zetaTwoUpper m <= zetaTwoUpper n
      by_cases hn0 : n = 0
      · by_cases hm0 : m = 0
        · simp [hn0, hm0, zetaTwoUpper, zetaTwoTailBound]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          calc
            zetaTwoUpper m <= zetaTwoUpper 1 :=
              zetaTwoUpper_le_of_le (by omega : 0 < (1 : Nat)) hmpos
            _ = zetaTwoUpper n := by
              rw [hn0]
              native_decide
      · exact zetaTwoUpper_le_of_le (Nat.pos_of_ne_zero hn0) hnm

private theorem one_div_nat_le_one_div_nat_of_le
    {a b : Nat} (ha : 0 < a) (hab : a <= b) :
    1 / (b : Rat) <= 1 / (a : Rat) := by
  let A : Rat := (a : Rat)
  let B : Rat := (b : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 ha
  have hBpos : 0 < B := by
    dsimp [B]
    exact (Rat.natCast_pos).2 (Nat.lt_of_lt_of_le ha hab)
  have hAne : A ≠0 := Rat.ne_of_gt hApos
  have hBne : B ≠0 := Rat.ne_of_gt hBpos
  have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
  have hAleB : A <= B := by
    dsimp [A, B]
    exact_mod_cast hab
  apply Rat.le_of_mul_le_mul_right (c := A * B)
  · calc
      (1 / B) * (A * B) = A := by
        rw [Rat.div_def]
        have hcancel : B * B⁻¹= 1 := Rat.mul_inv_cancel B hBne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= B := hAleB
      _ = (1 / A) * (A * B) := by
        rw [Rat.div_def]
        have hcancel : A * A⁻¹= 1 := Rat.mul_inv_cancel A hAne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hABpos

theorem zetaTwoWidthsShrinkToZero :
    RealRaw.WidthsShrinkToZero zetaTwoInterval := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  exact ⟨N, by
    intro n hn
    rw [zetaTwoInterval_width]
    unfold zetaTwoTailBound
    rw [if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le hNpos hn))]
    have hsmallN : 1 / (N : Rat) <= eps.val := by
      dsimp [N]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    exact Rat.le_trans
      (one_div_nat_le_one_div_nat_of_le (a := N) (b := n) hNpos hn)
      hsmallN⟩
theorem zetaTwoRaw_validCompute :
    RealRaw.ValidCompute zetaTwoInterval := by
  constructor
  · exact zetaTwoInterval_width_nonneg
  · constructor
    · exact zetaTwoInterval_nested
    · exact zetaTwoWidthsShrinkToZero

/-- Raw zeta(2) algorithm. -/
def zetaTwoRaw : RealRaw where
  compute := zetaTwoInterval
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [zetaTwoInterval_width]
      unfold zetaTwoTailBound
      rw [if_neg (by omega : n ≠ 0)]
      rw [Rat.pow_one]
      exact Rat.le_refl)

/-!
## Integer-exponent zeta values

For every natural exponent `p >= 2`, the same interval trick works:

`sum_{k=1}^n 1/k^p <= zeta(p) <= sum_{k=1}^n 1/k^p + 1/n`.

The padding is intentionally coarse but very robust.  Since
`1/k^p <= 1/k^2` for `p >= 2`, the Basel telescoping estimate certifies
nesting for the whole integer-exponent family.
-/

def zetaNatTerm (p : Nat) (k : Nat) : Rat :=
  let m : Rat := ((k + 1 : Nat) : Rat)
  1 / (m ^ p)

def zetaNatPartial (p : Nat) : Nat -> Rat
  | 0 => 0
  | n + 1 => zetaNatPartial p n + zetaNatTerm p n

def zetaNatTailBound (n : Nat) : Rat :=
  if n = 0 then 2 else 1 / (n : Rat)

def zetaNatUpper (p : Nat) (n : Nat) : Rat :=
  zetaNatPartial p n + zetaNatTailBound n

def zetaNatInterval (p : Nat) (n : Nat) : QInterval :=
  { lo := zetaNatPartial p n, hi := zetaNatUpper p n }

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem one_le_pow_of_one_le {q : Rat}
    (hq : 1 <= q) (n : Nat) :
    1 <= q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ]
      have hq_nonneg : 0 <= q := by grind
      have hpow_nonneg : 0 <= q ^ n := Rat.pow_nonneg hq_nonneg
      have hleft : q ^ n * 1 <= q ^ n * q :=
        Rat.mul_le_mul_of_nonneg_left hq hpow_nonneg
      have hone : 1 <= q ^ n * 1 := by simpa using ih
      exact Rat.le_trans hone hleft

private theorem rat_pow_two_le_pow_of_two_le {q : Rat}
    (hq : 1 <= q) {p : Nat} (hp : 2 <= p) :
    q ^ 2 <= q ^ p := by
  have hrewrite : p = 2 + (p - 2) := by omega
  rw [hrewrite, rat_pow_add]
  have hq_nonneg : 0 <= q := by grind
  have hq2_nonneg : 0 <= q ^ 2 := Rat.pow_nonneg hq_nonneg
  have htail : 1 <= q ^ (p - 2) := one_le_pow_of_one_le hq _
  calc
    q ^ 2 = q ^ 2 * 1 := by rw [Rat.mul_one]
    _ <= q ^ 2 * q ^ (p - 2) :=
      Rat.mul_le_mul_of_nonneg_left htail hq2_nonneg

private theorem one_div_le_one_div_of_pos_of_le
    {a b : Rat} (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠0 := Rat.ne_of_gt ha
  have hbne : b ≠0 := Rat.ne_of_gt hb
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹= 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹= 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

theorem zetaNatTerm_nonneg (p k : Nat) :
    0 <= zetaNatTerm p k := by
  unfold zetaNatTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  exact Rat.le_of_lt (by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 (Rat.pow_pos hmpos))

theorem zetaNatTerm_le_zetaTwoTerm
    (p k : Nat) (hp : 2 <= p) :
    zetaNatTerm p k <= zetaTwoTerm k := by
  unfold zetaNatTerm zetaTwoTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  have hmone : 1 <= m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hpow : m ^ 2 <= m ^ p := rat_pow_two_le_pow_of_two_le hmone hp
  have hm2 : m ^ 2 = m * m := by
    rw [show (2 : Nat) = 1 + 1 by omega]
    rw [Rat.pow_succ]
    simp [Rat.pow_succ, Rat.mul_comm]
  change 1 / (m ^ p) <= 1 / (m * m)
  rw [←hm2]
  exact one_div_le_one_div_of_pos_of_le
    (Rat.pow_pos hmpos) hpow

theorem zetaNatPartial_le_succ (p n : Nat) :
    zetaNatPartial p n <= zetaNatPartial p (n + 1) := by
  change zetaNatPartial p n <=
    zetaNatPartial p n + zetaNatTerm p n
  grind [zetaNatTerm_nonneg p n]

theorem zetaNatPartial_le_of_le (p : Nat) {n m : Nat} :
    n <= m -> zetaNatPartial p n <= zetaNatPartial p m := by
  intro h
  induction h with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (zetaNatPartial_le_succ p _)

theorem zetaNatUpper_succ_le
    (p n : Nat) (hp : 2 <= p) (hn : 0 < n) :
    zetaNatUpper p (n + 1) <= zetaNatUpper p n := by
  unfold zetaNatUpper zetaNatTailBound
  rw [if_neg (Nat.succ_ne_zero n)]
  rw [if_neg (Nat.ne_of_gt hn)]
  change zetaNatPartial p n + zetaNatTerm p n +
      1 / ((n + 1 : Nat) : Rat) <=
    zetaNatPartial p n + 1 / (n : Rat)
  have hstepTwo := zetaTwoTerm_le_telescopeStep n hn
  have hterm : zetaNatTerm p n <=
      1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat) :=
    Rat.le_trans (zetaNatTerm_le_zetaTwoTerm p n hp) hstepTwo
  have hwithPartial :
      zetaNatPartial p n + zetaNatTerm p n <=
        zetaNatPartial p n +
          (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) :=
    rat_add_le_add (by exact Rat.le_refl) hterm
  calc
    zetaNatPartial p n + zetaNatTerm p n +
        1 / ((n + 1 : Nat) : Rat)
        <= zetaNatPartial p n +
            (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) +
              1 / ((n + 1 : Nat) : Rat) :=
          rat_add_le_add hwithPartial (by exact Rat.le_refl)
    _ = zetaNatPartial p n + 1 / (n : Rat) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem zetaNatUpper_le_of_le
    (p : Nat) (hp : 2 <= p) {n m : Nat}
    (hn : 0 < n) (h : n <= m) :
    zetaNatUpper p m <= zetaNatUpper p n := by
  induction h with
  | refl => exact Rat.le_refl
  | step h ih =>
      have hmpos : 0 < _ := Nat.lt_of_lt_of_le hn h
      exact Rat.le_trans (zetaNatUpper_succ_le p _ hp hmpos) ih

theorem zetaNatInterval_width (p : Nat) (n : Nat) :
    (zetaNatInterval p n).width = zetaNatTailBound n := by
  unfold zetaNatInterval zetaNatUpper QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem zetaNatInterval_width_nonneg (p : Nat) (n : Nat) :
    0 <= (zetaNatInterval p n).width := by
  rw [zetaNatInterval_width]
  unfold zetaNatTailBound
  by_cases hn0 : n = 0
  · simp [hn0]
    native_decide
  · simp [hn0]
    exact Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn0)))

theorem zetaNatInterval_ordered (p : Nat) (n : Nat) :
    (zetaNatInterval p n).lo <= (zetaNatInterval p n).hi := by
  have h := zetaNatInterval_width_nonneg p n
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem zetaNatInterval_nested
    (p : Nat) (hp : 2 <= p)
    (n m : Nat) (hnm : n <= m) :
    (zetaNatInterval p n).lo <= (zetaNatInterval p m).lo /\
      (zetaNatInterval p m).lo <= (zetaNatInterval p m).hi /\
      (zetaNatInterval p m).hi <= (zetaNatInterval p n).hi := by
  constructor
  · exact zetaNatPartial_le_of_le p hnm
  · constructor
    · exact zetaNatInterval_ordered p m
    · by_cases hn0 : n = 0
      · by_cases hm0 : m = 0
        · simp [hn0, hm0, zetaNatInterval, zetaNatUpper, zetaNatTailBound]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          change zetaNatUpper p m <= zetaNatUpper p n
          calc
            zetaNatUpper p m <= zetaNatUpper p 1 :=
              zetaNatUpper_le_of_le p hp (by omega : 0 < (1 : Nat)) hmpos
            _ = zetaNatUpper p n := by
              rw [hn0]
              unfold zetaNatUpper zetaNatTailBound zetaNatPartial zetaNatTerm
              simp
              change (0 : Rat) + 1 / (1 : Rat) ^ p + 1 / 1 = 0 + 2
              have hpow : (1 : Rat) ^ p = 1 := by
                clear hp
                induction p with
                | zero => simp
                | succ p ih =>
                    rw [Rat.pow_succ, ih]
                    native_decide
              rw [hpow]
              native_decide
      · exact zetaNatUpper_le_of_le p hp (Nat.pos_of_ne_zero hn0) hnm

theorem zetaNatWidthsShrinkToZero (p : Nat) :
    RealRaw.WidthsShrinkToZero (zetaNatInterval p) := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  exact ⟨N, by
    intro n hn
    rw [zetaNatInterval_width]
    unfold zetaNatTailBound
    rw [if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le hNpos hn))]
    have hsmallN : 1 / (N : Rat) <= eps.val := by
      dsimp [N]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    exact Rat.le_trans
      (one_div_nat_le_one_div_nat_of_le (a := N) (b := n) hNpos hn)
      hsmallN⟩
theorem zetaNatRaw_validCompute (p : Nat) (hp : 2 <= p) :
    RealRaw.ValidCompute (zetaNatInterval p) := by
  constructor
  · exact zetaNatInterval_width_nonneg p
  · constructor
    · exact zetaNatInterval_nested p hp
    · exact zetaNatWidthsShrinkToZero p

def zetaNatRaw (p : Nat) : RealRaw where
  compute := zetaNatInterval p
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [zetaNatInterval_width]
      unfold zetaNatTailBound
      rw [if_neg (by omega : n ≠ 0)]
      rw [Rat.pow_one]
      exact Rat.le_refl)

def zetaNat (p : Nat) (hp : 2 <= p) : Real :=
  Real.ofRaw (zetaNatRaw p) (zetaNatRaw_validCompute p hp)


/-- Constructive data for a Dirichlet character: a conductor and a computable
complex-valued function on natural numbers.

The character laws are kept as predicates below, so we can first build and
compute with explicit characters, then prove the laws as needed. -/
structure DirichletCharacter where
  conductor : Nat
  value : Nat -> QComplex

namespace DirichletCharacter

def IsPeriodic (chi : DirichletCharacter) : Prop :=
  forall n : Nat, chi.value (n + chi.conductor) = chi.value n

def VanishesOffUnits (chi : DirichletCharacter) : Prop :=
  forall n : Nat, Nat.gcd n chi.conductor ≠ 1 -> chi.value n = QComplex.zero

def IsMultiplicative (chi : DirichletCharacter) : Prop :=
  forall m n : Nat, chi.value (m * n) = QComplex.mul (chi.value m) (chi.value n)

def IsGenuine (chi : DirichletCharacter) : Prop :=
  chi.IsPeriodic /\ chi.VanishesOffUnits /\ chi.IsMultiplicative

end DirichletCharacter

/-- One term `chi(k) / k^s`, with the conventional indexing `k >= 1`. -/
def dirichletLTerm (chi : DirichletCharacter) (s k : Nat) : QComplex :=
  QComplex.scaleRat (1 / ((k : Rat) ^ s)) (chi.value k)

/-- The finite partial sum `sum_{k=1}^n chi(k) / k^s`. -/
def dirichletLPartial (chi : DirichletCharacter) (s n : Nat) : QComplex :=
  (List.range n).foldl
    (fun acc k => QComplex.add acc (dirichletLTerm chi s (k + 1)))
    QComplex.zero

def chi4Value (n : Nat) : QComplex :=
  QComplex.ofRat
    (if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1)

/-- The primitive character of conductor 4. -/
def chi4 : DirichletCharacter where
  conductor := 4
  value := chi4Value

/-- The real-valued function behind `chi4`, useful for the alternating
one-dimensional computation. -/
def characterModFour (n : Nat) : Rat :=
  (chi4.value n).re

/-- Finite odd-denominator partial sums for `L(1, chi)`, for real-valued
characters. -/
def dirichletLOddPartialAtOne (chi : Nat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun acc k => acc + chi (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)) 0

def dirichletLChi4OddPartialAtOne (n : Nat) : Rat :=
  dirichletLOddPartialAtOne characterModFour n

/-- The Dirichlet L-value `L(1, chi4)` as a raw real. -/
def dirichletLChi4AtOne : RealRaw where
  compute := fun n =>
    let state : Prod Rat Rat := (List.range n).foldl
      (fun state (i : Nat) =>
        let term1 : Rat := 1 / (4 * i + 3)
        let term2 : Rat := 1 / (4 * i + 5)
        let lo := state.1 - term1
        let hi := lo + term2
        (hi, lo))
      (1, 0)
    { lo := state.2, hi := state.1 }

/-- Conventional alias: the Dirichlet beta function is `L(s, chi4)`. -/
def dirichletBetaAtOne : RealRaw :=
  dirichletLChi4AtOne

end DirichletSeries

end ComputableAnalysis
