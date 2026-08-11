import ComputableAnalysis.Basic

/-!
# A finite prime-factorization witness

The number `360 = 2^3 * 3^2 * 5` is supplied with a prime-labelled factor
list.  This is a worked certificate-level instance of item 80; the general
classical theorem is represented by the finite recursive certificate API.
-/

namespace ComputableAnalysis

def primeFactorizationCertificate360 : PrimeFactorCertificate 360 where
  factors := [2, 2, 2, 3, 3, 5]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_five
  product_eq := by
    native_decide

theorem primeFactorizationCertificate360_factors :
    primeFactorizationCertificate360.factors = [2, 2, 2, 3, 3, 5] := by
  rfl

theorem primeFactorizationCertificate360_product :
    primeFactorizationCertificate360.factors.foldl (fun acc p => acc * p) 1 =
      360 := by
  exact primeFactorizationCertificate360.product_eq

theorem primeFactorizationCertificate360_factor_dvd :
    2 ∣ 360 /\ 3 ∣ 360 /\ 5 ∣ 360 := by
  native_decide

def primeFactorizationCertificate360_alternative : PrimeFactorCertificate 360 where
  factors := [5, 3, 3, 2, 2, 2]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    · exact basicPrime_five
    · exact basicPrime_three
    · exact basicPrime_two
  product_eq := by
    native_decide

theorem primeFactorizationCertificate360_alternative_factors :
    primeFactorizationCertificate360_alternative.factors = [5, 3, 3, 2, 2, 2] := by
  rfl

theorem primeFactorizationCertificate360_factor_order_unique :
    primeFactorizationCertificate360.factors.Perm
      primeFactorizationCertificate360_alternative.factors := by
  exact PrimeFactorCertificate.factor_perm
    primeFactorizationCertificate360
    primeFactorizationCertificate360_alternative

def primeFactorizationCertificate720 : PrimeFactorCertificate 720 where
  factors := [2, 2, 2, 2, 3, 3, 5]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_five
  product_eq := by
    native_decide

theorem primeFactorizationCertificate720_product :
    primeFactorizationCertificate720.factors.foldl (fun acc p => acc * p) 1 =
      720 := by
  exact primeFactorizationCertificate720.product_eq

theorem primeFactorizationCertificate720_factor_dvd :
    2 ∣ 720 /\ 3 ∣ 720 /\ 5 ∣ 720 := by
  native_decide

def primeFactorizationCertificate600 : PrimeFactorCertificate 600 where
  factors := [2, 2, 2, 3, 5, 5]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_five
  product_eq := by
    native_decide

theorem primeFactorizationCertificate600_product :
    primeFactorizationCertificate600.factors.foldl (fun acc p => acc * p) 1 =
      600 := by
  exact primeFactorizationCertificate600.product_eq

theorem primeFactorizationCertificate600_factor_dvd :
    2 ∣ 600 /\ 3 ∣ 600 /\ 5 ∣ 600 := by
  native_decide

def primeFactorizationCertificate126 : PrimeFactorCertificate 126 where
  factors := [2, 3, 3, 7]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)
  product_eq := by
    native_decide

theorem primeFactorizationCertificate126_product :
    primeFactorizationCertificate126.factors.foldl (fun acc p => acc * p) 1 =
      126 := by
  exact primeFactorizationCertificate126.product_eq

theorem primeFactorizationCertificate126_factor_dvd :
    2 ∣ 126 /\ 3 ∣ 126 /\ 7 ∣ 126 := by
  native_decide

def primeFactorizationCertificate27720 : PrimeFactorCertificate 27720 where
  factors := [2, 2, 2, 3, 3, 5, 7, 11]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_five
    · exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)
    · exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)
  product_eq := by
    native_decide

theorem primeFactorizationCertificate27720_product :
    primeFactorizationCertificate27720.factors.foldl (fun acc p => acc * p) 1 =
      27720 := by
  exact primeFactorizationCertificate27720.product_eq

theorem primeFactorizationCertificate27720_factor_dvd :
    2 ∣ 27720 /\ 3 ∣ 27720 /\ 5 ∣ 27720 /\ 7 ∣ 27720 /\ 11 ∣ 27720 := by
  native_decide

end ComputableAnalysis
