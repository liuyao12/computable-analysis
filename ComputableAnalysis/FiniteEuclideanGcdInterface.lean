import ComputableAnalysis.Basic

/-!
# Reusable finite Euclidean-gcd interface

The gcd benchmark is an executable remainder loop.  This certificate keeps
the terminating output and a Bézout witness together, so divisibility and
coprimality are consequences of one finite computation.
-/

namespace ComputableAnalysis

structure FiniteEuclideanGcdCertificate where
  leftInput : Nat
  rightInput : Nat
  gcdValue : Nat
  leftCoeff : Int
  rightCoeff : Int
  gcd_eq : gcdValue = euclideanGcd leftInput rightInput
  bezout : leftCoeff * (leftInput : Int) + rightCoeff * (rightInput : Int) = gcdValue

theorem FiniteEuclideanGcdCertificate.divides_left
    (certificate : FiniteEuclideanGcdCertificate) :
    certificate.gcdValue ∣ certificate.leftInput := by
  rw [certificate.gcd_eq, euclideanGcd_eq_gcd]
  exact Nat.gcd_dvd_left _ _

theorem FiniteEuclideanGcdCertificate.divides_right
    (certificate : FiniteEuclideanGcdCertificate) :
    certificate.gcdValue ∣ certificate.rightInput := by
  rw [certificate.gcd_eq, euclideanGcd_eq_gcd]
  exact Nat.gcd_dvd_right _ _

theorem FiniteEuclideanGcdCertificate.is_coprime_of_value_one
    (certificate : FiniteEuclideanGcdCertificate)
    (hvalue : certificate.gcdValue = 1) :
    Nat.Coprime certificate.leftInput certificate.rightInput := by
  apply euclideanGcd_eq_one_iff_coprime.mp
  rw [← certificate.gcd_eq, hvalue]

def finiteEuclideanGcdCertificate
    (leftInput rightInput : Nat) (leftCoeff rightCoeff : Int)
    (bezout : leftCoeff * (leftInput : Int) + rightCoeff * (rightInput : Int) =
      euclideanGcd leftInput rightInput) :
    FiniteEuclideanGcdCertificate where
  leftInput := leftInput
  rightInput := rightInput
  gcdValue := euclideanGcd leftInput rightInput
  leftCoeff := leftCoeff
  rightCoeff := rightCoeff
  gcd_eq := rfl
  bezout := bezout

end ComputableAnalysis
