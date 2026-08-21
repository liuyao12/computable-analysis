import ComputableAnalysis.FiniteStirlingCertificate

/-!
# Reusable finite Stirling-ratio interface

This packages the project-native part of Stirling's formula: a finite rational
ratio together with explicit positivity and enclosure certificates.  It makes
no asymptotic claim.
-/

namespace ComputableAnalysis

structure FiniteStirlingRatioCertificate where
  index : Nat
  eApprox : Rat
  rootApprox : Rat
  ratioValue : Rat
  e_pos : 0 < eApprox
  root_pos : 0 < rootApprox
  ratio_eq : ratioValue = finiteStirlingRatio index eApprox rootApprox
  lowerBound : Rat
  upperBound : Rat
  lower_le : (lowerBound : Rat) ≤ (ratioValue : Rat)
  le_upper : (ratioValue : Rat) ≤ (upperBound : Rat)

theorem FiniteStirlingRatioCertificate.mem_interval
    (certificate : FiniteStirlingRatioCertificate) :
    certificate.lowerBound ≤ certificate.ratioValue ∧
      certificate.ratioValue ≤ certificate.upperBound := by
  exact ⟨certificate.lower_le, certificate.le_upper⟩

theorem FiniteStirlingRatioCertificate.positive
    (certificate : FiniteStirlingRatioCertificate)
    (hlower : 0 < certificate.lowerBound) :
    0 < certificate.ratioValue := by
  have h := certificate.lower_le
  grind

theorem FiniteStirlingRatioCertificate.abs_error_le
    (certificate : FiniteStirlingRatioCertificate)
    (htarget : Rat) (hlower : htarget ≤ certificate.ratioValue)
    (hupper : certificate.ratioValue ≤ htarget + 1 / 100) :
    qabs (certificate.ratioValue - htarget) ≤ 1 / 100 := by
  have hnonneg : 0 ≤ certificate.ratioValue - htarget := by
    grind
  rw [qabs_eq_self_of_nonneg hnonneg]
  grind

theorem FiniteStirlingRatioCertificate.abs_error_le_of_tolerance
    (certificate : FiniteStirlingRatioCertificate)
    (htarget delta : Rat)
    (hlower : htarget ≤ certificate.ratioValue)
    (hupper : certificate.ratioValue ≤ htarget + delta) :
    qabs (certificate.ratioValue - htarget) ≤ delta := by
  have hnonneg : 0 ≤ certificate.ratioValue - htarget := by
    grind
  rw [qabs_eq_self_of_nonneg hnonneg]
  grind

/-! The ratio has an exact finite stage law.  This is the recurrence used by
any stagewise Stirling computation; no asymptotic limit is involved. -/
theorem finiteStirlingRatio_succ_numerator
    (n : Nat) (e root : Rat) :
    finiteStirlingRatio (n + 1) e root =
      (((n + 1 : Nat) : Rat) * factorialRat n) /
        (root * ((((n + 1 : Nat) : Rat) / e) ^ (n + 1))) := by
  unfold finiteStirlingRatio
  rw [FormalPowerSeries.factorialRat_succ]

def finiteStirlingTenCertificate : FiniteStirlingRatioCertificate where
  index := 10
  eApprox := finiteStirlingEApprox
  rootApprox := finiteStirlingRootApprox
  ratioValue := finiteStirlingRatio 10 finiteStirlingEApprox finiteStirlingRootApprox
  e_pos := by native_decide
  root_pos := by native_decide
  ratio_eq := rfl
  lowerBound := 1
  upperBound := 101 / 100
  lower_le := finiteStirlingRatioAtTen_unit_enclosure.1
  le_upper := finiteStirlingRatioAtTen_unit_enclosure.2

theorem finiteStirlingTenCertificate_unit_error :
    qabs (finiteStirlingTenCertificate.ratioValue - 1) ≤ 1 / 100 := by
  exact finiteStirlingTenCertificate.abs_error_le 1
    finiteStirlingTenCertificate.lower_le
    (by
      have h := finiteStirlingTenCertificate.le_upper
      calc
        finiteStirlingTenCertificate.ratioValue ≤ finiteStirlingTenCertificate.upperBound := h
        _ = 1 + 1 / 100 := by native_decide)

end ComputableAnalysis
