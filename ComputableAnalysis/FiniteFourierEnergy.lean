import ComputableAnalysis.FiniteFourierCertificate

/-!
# Finite Fourier energy certificates

This is the project's small constructive boundary for `L2`-style arguments.
It records rational coefficient energy and a supplied tail budget; it does not
construct measurable functions or a completed Hilbert space.
-/

namespace ComputableAnalysis

def qcomplexEnergy : List QComplex -> Rat
  | [] => 0
  | z :: zs => QComplex.normSq z + qcomplexEnergy zs

theorem qcomplexEnergy_append (xs ys : List QComplex) :
    qcomplexEnergy (xs ++ ys) = qcomplexEnergy xs + qcomplexEnergy ys := by
  induction xs with
  | nil => simp [qcomplexEnergy, Rat.zero_add]
  | cons z xs ih =>
      simp only [List.cons_append, qcomplexEnergy, ih]
      grind [Rat.add_assoc]

theorem qcomplexEnergy_nonneg (xs : List QComplex) :
    0 <= qcomplexEnergy xs := by
  induction xs with
  | nil => native_decide
  | cons z xs ih =>
      apply Rat.add_nonneg
      · cases z
        simp only [QComplex.normSq]
        exact Rat.add_nonneg
          (rat_square_nonneg_basic _) (rat_square_nonneg_basic _)
      · exact ih

structure FiniteFourierEnergyTailCertificate where
  coefficients : List QComplex
  totalEnergy : Rat
  tailBudget : Rat
  tailBudget_nonneg : 0 <= tailBudget
  total_minus_prefix_nonneg :
    0 <= totalEnergy - qcomplexEnergy coefficients
  total_minus_prefix_le_budget :
    totalEnergy - qcomplexEnergy coefficients <= tailBudget

def FiniteFourierEnergyTailCertificate.energyInterval
  (certificate : FiniteFourierEnergyTailCertificate) : QInterval :=
  { lo := qcomplexEnergy certificate.coefficients
    hi := qcomplexEnergy certificate.coefficients + certificate.tailBudget }

theorem FiniteFourierEnergyTailCertificate.energyInterval_ordered
    (certificate : FiniteFourierEnergyTailCertificate) :
    (certificate.energyInterval).lo <= (certificate.energyInterval).hi := by
  unfold FiniteFourierEnergyTailCertificate.energyInterval
  apply (Rat.le_iff_sub_nonneg _ _).2
  change 0 <= qcomplexEnergy certificate.coefficients + certificate.tailBudget -
    qcomplexEnergy certificate.coefficients
  rw [Rat.add_comm (qcomplexEnergy certificate.coefficients) certificate.tailBudget]
  rw [Rat.add_sub_cancel]
  exact certificate.tailBudget_nonneg

theorem FiniteFourierEnergyTailCertificate.energyInterval_contains_total
    (certificate : FiniteFourierEnergyTailCertificate) :
    (certificate.energyInterval).ContainsInterval
      { lo := certificate.totalEnergy, hi := certificate.totalEnergy } := by
  unfold FiniteFourierEnergyTailCertificate.energyInterval
    QInterval.ContainsInterval
  constructor
  · exact (Rat.le_iff_sub_nonneg _ _).2
      certificate.total_minus_prefix_nonneg
  · have htail : 0 <= certificate.tailBudget -
        (certificate.totalEnergy - qcomplexEnergy certificate.coefficients) :=
      (Rat.le_iff_sub_nonneg
        (certificate.totalEnergy - qcomplexEnergy certificate.coefficients)
        certificate.tailBudget).1
        certificate.total_minus_prefix_le_budget
    apply (Rat.le_iff_sub_nonneg _ _).2
    change 0 <= qcomplexEnergy certificate.coefficients + certificate.tailBudget -
      certificate.totalEnergy
    simp only [Rat.sub_eq_add_neg] at htail ⊢
    rw [Rat.neg_add] at htail
    simpa [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm] using htail

end ComputableAnalysis
