import ComputableAnalysis.Basic

/-!
# A finite prime-reciprocal extension certificate

The prime-reciprocal benchmark is represented by a finite accumulator and a
constructive extension theorem: every finite list of certified primes can be
extended by a new certified prime, and its reciprocal strictly increases the
accumulator.  This is the project's potential-infinity core, not a completed
infinite-series divergence theorem.
-/

namespace ComputableAnalysis

def primeReciprocalSum : List Nat → Rat
  | [] => 0
  | p :: ps => 1 / (p : Rat) + primeReciprocalSum ps

theorem primeReciprocalSum_append (xs ys : List Nat) :
    primeReciprocalSum (xs ++ ys) =
      primeReciprocalSum xs + primeReciprocalSum ys := by
  induction xs with
  | nil => simp [primeReciprocalSum, Rat.zero_add]
  | cons p xs ih =>
      simp only [List.cons_append, primeReciprocalSum, ih]
      exact (Rat.add_assoc _ _ _).symm

theorem primeReciprocalSum_cons_gt {p : Nat} {xs : List Nat}
    (hp : 2 ≤ p) :
    primeReciprocalSum xs < primeReciprocalSum (p :: xs) := by
  have hpos : 0 < 1 / (p : Rat) := one_div_nat_pos (by omega)
  change primeReciprocalSum xs <
    1 / (p : Rat) + primeReciprocalSum xs
  rw [Rat.lt_iff_sub_pos]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem primeReciprocalSum_four_primes :
    primeReciprocalSum [2, 3, 5, 7] = 247 / 210 := by
  native_decide

theorem primeReciprocalSum_five_primes :
    primeReciprocalSum [2, 3, 5, 7, 11] = 2927 / 2310 := by
  native_decide

theorem primeReciprocalSum_six_primes :
    primeReciprocalSum [2, 3, 5, 7, 11, 13] = 40361 / 30030 := by
  native_decide

theorem primeReciprocalSum_eight_primes :
    primeReciprocalSum [2, 3, 5, 7, 11, 13, 17, 19] =
      14117683 / 9699690 := by
  native_decide

theorem primeReciprocalSum_ten_primes :
    primeReciprocalSum [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] =
      9920878441 / 6469693230 := by
  native_decide

theorem primeReciprocalSum_twelve_primes_gt_three_halves :
    (3 : Rat) / 2 <
      primeReciprocalSum [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] := by
  native_decide

theorem primeReciprocalSum_five_gt_four :
    primeReciprocalSum [2, 3, 5, 7] <
      primeReciprocalSum [11, 2, 3, 5, 7] := by
  apply primeReciprocalSum_cons_gt
  omega

theorem primeReciprocalSum_six_gt_five :
    primeReciprocalSum [2, 3, 5, 7, 11] <
      primeReciprocalSum [13, 2, 3, 5, 7, 11] := by
  apply primeReciprocalSum_cons_gt
  omega

theorem primeReciprocalSum_eight_gt_six :
    primeReciprocalSum [2, 3, 5, 7, 11, 13] <
      primeReciprocalSum [19, 17, 2, 3, 5, 7, 11, 13] := by
  have h17 : primeReciprocalSum [2, 3, 5, 7, 11, 13] <
      primeReciprocalSum [17, 2, 3, 5, 7, 11, 13] := by
    apply primeReciprocalSum_cons_gt
    omega
  have h19 : primeReciprocalSum [17, 2, 3, 5, 7, 11, 13] <
      primeReciprocalSum [19, 17, 2, 3, 5, 7, 11, 13] := by
    apply primeReciprocalSum_cons_gt
    omega
  grind

theorem primeReciprocalSum_ten_gt_eight :
    primeReciprocalSum [2, 3, 5, 7, 11, 13, 17, 19] <
      primeReciprocalSum [29, 23, 2, 3, 5, 7, 11, 13, 17, 19] := by
  have h23 : primeReciprocalSum [2, 3, 5, 7, 11, 13, 17, 19] <
      primeReciprocalSum [23, 2, 3, 5, 7, 11, 13, 17, 19] := by
    apply primeReciprocalSum_cons_gt
    omega
  have h29 : primeReciprocalSum [23, 2, 3, 5, 7, 11, 13, 17, 19] <
      primeReciprocalSum [29, 23, 2, 3, 5, 7, 11, 13, 17, 19] := by
    apply primeReciprocalSum_cons_gt
    omega
  grind

theorem exists_prime_reciprocal_extension (xs : List Nat)
    (hprime : ∀ p, p ∈ xs → BasicPrime p) :
    ∃ p, BasicPrime p ∧ p ∉ xs ∧
      primeReciprocalSum xs < primeReciprocalSum (p :: xs) := by
  rcases exists_basicPrime_not_mem_of_all_basicPrime xs hprime with
    ⟨p, hp, hpnot⟩
  exact ⟨p, hp, hpnot, primeReciprocalSum_cons_gt hp.1⟩

end ComputableAnalysis
