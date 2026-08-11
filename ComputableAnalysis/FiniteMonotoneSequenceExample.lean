import ComputableAnalysis.Basic

/-!
# A finite monotone-sequence certificate

The benchmark's ascending/descending-sequence item is represented here by
the constructive order core: a local successor bound propagates to every
finite pair of indices.  No limit or completeness principle is used.
-/

namespace ComputableAnalysis

theorem monotone_of_succ_le {f : Nat → Rat}
    (hstep : ∀ n, f n ≤ f (n + 1)) :
    ∀ ⦃a b : Nat⦄, a ≤ b → f a ≤ f b := by
  intro a b hab
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact Rat.le_refl
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact Rat.le_refl
      · have hab' : a ≤ b := by omega
        exact Rat.le_trans (ih hab') (hstep b)

theorem antitone_of_succ_ge {f : Nat → Rat}
    (hstep : ∀ n, f (n + 1) ≤ f n) :
    ∀ ⦃a b : Nat⦄, a ≤ b → f b ≤ f a := by
  intro a b hab
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact Rat.le_refl
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact Rat.le_refl
      · have hab' : a ≤ b := by omega
        exact Rat.le_trans (hstep b) (ih hab')

def ascendingNaturalSequence (n : Nat) : Rat := n

theorem ascendingNaturalSequence_succ_le (n : Nat) :
    ascendingNaturalSequence n ≤ ascendingNaturalSequence (n + 1) := by
  simp only [ascendingNaturalSequence]
  exact (Rat.natCast_le_natCast).2 (Nat.le_succ n)

theorem ascendingNaturalSequence_monotone :
    ∀ ⦃a b : Nat⦄, a ≤ b →
      ascendingNaturalSequence a ≤ ascendingNaturalSequence b := by
  apply monotone_of_succ_le
  exact ascendingNaturalSequence_succ_le

theorem ascendingNaturalSequence_stage64 :
    ascendingNaturalSequence 64 = 64 := by
  native_decide

theorem ascendingNaturalSequence_stage128 :
    ascendingNaturalSequence 128 = 128 := by
  native_decide

/-!
The following bounded sequence illustrates the project's potential-infinity
replacement for a classical monotone-convergence statement.  Every stage is a
rational computation, and the remaining error is represented by the explicit
dyadic tail rather than by an asserted real limit.
-/

def dyadicApproach (n : Nat) : Rat := 1 - (1 / 2 : Rat) ^ n

theorem dyadicApproach_succ_le (n : Nat) :
    dyadicApproach n ≤ dyadicApproach (n + 1) := by
  unfold dyadicApproach
  rw [Rat.pow_succ]
  have hpow : (0 : Rat) ≤ (1 / 2 : Rat) ^ n :=
    Rat.pow_nonneg (by native_decide)
  have hhalf : (1 / 2 : Rat) ≤ 1 := by native_decide
  have hmul := Rat.mul_le_mul_of_nonneg_left hhalf hpow
  grind

theorem dyadicApproach_le_one (n : Nat) : dyadicApproach n ≤ 1 := by
  unfold dyadicApproach
  have hpow : (0 : Rat) ≤ (1 / 2 : Rat) ^ n :=
    Rat.pow_nonneg (by native_decide)
  grind [Rat.sub_eq_add_neg]

theorem dyadicApproach_error (n : Nat) :
    1 - dyadicApproach n = (1 / 2 : Rat) ^ n := by
  unfold dyadicApproach
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem dyadicPower_le_one_div_succ (n : Nat) :
    (1 / 2 : Rat) ^ n <= 1 / ((n + 1 : Nat) : Rat) := by
  have hpow : ((n + 1 : Nat) : Rat) * (1 / 2 : Rat) ^ n <= 1 := by
    induction n with
    | zero => native_decide
    | succ n ih =>
        rw [Rat.pow_succ]
        change ((n + 2 : Nat) : Rat) *
          ((1 / 2 : Rat) ^ n * (1 / 2 : Rat)) <= 1
        have hnonneg : 0 <= (1 / 2 : Rat) ^ n :=
          Rat.pow_nonneg (by native_decide)
        have hstep : (n + 2 : Rat) <= 2 * (n + 1 : Rat) := by
          exact_mod_cast (by omega : n + 2 <= 2 * (n + 1))
        have hscaled := Rat.mul_le_mul_of_nonneg_right hstep hnonneg
        have hscaled' :
            ((n : Rat) + 2) / 2 * (1 / 2 : Rat) ^ n <=
              ((n : Rat) + 1) * (1 / 2 : Rat) ^ n := by
          apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
          · calc
              (((n : Rat) + 2) / 2 * (1 / 2 : Rat) ^ n) * 2 =
                  ((n : Rat) + 2) * (1 / 2 : Rat) ^ n := by
                    rw [Rat.div_def]
                    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
              _ <= (2 * ((n : Rat) + 1)) * (1 / 2 : Rat) ^ n := hscaled
              _ = (((n : Rat) + 1) * (1 / 2 : Rat) ^ n) * 2 := by
                    grind [Rat.mul_assoc, Rat.mul_comm]
          · native_decide
        have hrewrite :
            (n + 2 : Rat) * ((1 / 2 : Rat) ^ n * (1 / 2 : Rat)) =
              ((n + 2 : Rat) / 2) * (1 / 2 : Rat) ^ n := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
        rw [show ((n + 2 : Nat) : Rat) = (n : Rat) + 2 by
          exact_mod_cast (by omega : n + 2 = n + 2), hrewrite]
        calc
          ((n + 2 : Rat) / 2) * (1 / 2 : Rat) ^ n <=
              (n + 1 : Rat) * (1 / 2 : Rat) ^ n := by
                simpa only [show (n + 2 : Rat) = (n : Rat) + 2 by rfl,
                  show (n + 1 : Rat) = (n : Rat) + 1 by rfl] using hscaled'
          _ <= 1 := by
            simpa only [show ((n + 1 : Nat) : Rat) = (n : Rat) + 1 by
              exact_mod_cast (by omega : n + 1 = n + 1)] using ih
  apply Rat.le_of_mul_le_mul_right
    (c := ((n + 1 : Nat) : Rat))
  · rw [Rat.div_def]
    have hne : ((n + 1 : Nat) : Rat) ≠ 0 := by
      exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact (Rat.natCast_pos).2 (Nat.succ_pos n)

theorem dyadicApproach_error_shrinks :
    ShrinksToZero (fun n => 1 - dyadicApproach n) := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  change 1 - dyadicApproach n <= eps.val
  rw [dyadicApproach_error]
  have hdenpos : 0 < ((eps.val.den + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (by omega)
  have hnpos : 0 < ((n + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hindex : ((eps.val.den + 1 : Nat) : Rat) <=
      ((n + 1 : Nat) : Rat) := by
    exact_mod_cast (by omega : eps.val.den + 1 <= n + 1)
  have hinv : 1 / ((n + 1 : Nat) : Rat) <=
      1 / ((eps.val.den + 1 : Nat) : Rat) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((n + 1 : Nat) : Rat) * ((eps.val.den + 1 : Nat) : Rat))
    · rw [Rat.div_def, Rat.div_def]
      have hneN : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hnpos
      have hneD : ((eps.val.den + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt hdenpos
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos hnpos hdenpos
  exact Rat.le_trans (dyadicPower_le_one_div_succ n)
    (Rat.le_trans hinv (one_div_den_succ_le_of_pos eps.property))

theorem dyadicApproach_stage8_certificate :
    dyadicApproach 8 = 255 / 256 /\
      1 - dyadicApproach 8 = 1 / 256 /\
      dyadicApproach 8 ≤ 1 := by
  native_decide

theorem dyadicApproach_stage16_certificate :
    dyadicApproach 16 = 65535 / 65536 /\
      1 - dyadicApproach 16 = 1 / 65536 /\
      dyadicApproach 16 ≤ 1 := by
  native_decide

theorem dyadicApproach_stage32_certificate :
    dyadicApproach 32 = 4294967295 / 4294967296 /\
      1 - dyadicApproach 32 = 1 / 4294967296 /\
      dyadicApproach 32 ≤ 1 := by
  native_decide

theorem dyadicApproach_stage64_certificate :
    dyadicApproach 64 = 18446744073709551615 / 18446744073709551616 /\
      1 - dyadicApproach 64 = 1 / 18446744073709551616 /\
      dyadicApproach 64 ≤ 1 := by
  native_decide

theorem dyadicApproach_stage128_certificate :
    dyadicApproach 128 =
        340282366920938463463374607431768211455 /
          340282366920938463463374607431768211456 /\
      1 - dyadicApproach 128 =
        1 / 340282366920938463463374607431768211456 /\
      dyadicApproach 128 ≤ 1 := by
  native_decide

end ComputableAnalysis
