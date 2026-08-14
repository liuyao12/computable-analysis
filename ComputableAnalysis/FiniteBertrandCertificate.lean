import ComputableAnalysis.Basic

/-!
# Finite Bertrand-postulate certificates

The general prime-gap theorem is outside the project's current number-theory
boundary.  These executable witnesses record two exact finite instances of
the interval claim.
-/

namespace ComputableAnalysis

theorem bertrand_stage10 :
    ∃ p, BasicPrime p ∧ 10 < p ∧ p < 20 := by
  refine ⟨11, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage20 :
    ∃ p, BasicPrime p ∧ 20 < p ∧ p < 40 := by
  refine ⟨23, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage30 :
    ∃ p, BasicPrime p ∧ 30 < p ∧ p < 60 := by
  refine ⟨31, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage40 :
    ∃ p, BasicPrime p ∧ 40 < p ∧ p < 80 := by
  refine ⟨41, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage50 :
    ∃ p, BasicPrime p ∧ 50 < p ∧ p < 100 := by
  refine ⟨53, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage60 :
    ∃ p, BasicPrime p ∧ 60 < p ∧ p < 120 := by
  refine ⟨61, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage70 :
    ∃ p, BasicPrime p ∧ 70 < p ∧ p < 140 := by
  refine ⟨71, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage80 :
    ∃ p, BasicPrime p ∧ 80 < p ∧ p < 160 := by
  refine ⟨83, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_stage100 :
    ∃ p, BasicPrime p ∧ 100 < p ∧ p < 200 := by
  refine ⟨101, ?_, by omega, by omega⟩
  exact basicPrime_of_properDivisorSearch_none (by native_decide) (by native_decide)

theorem bertrand_finite_certificate :
    (∃ p, BasicPrime p ∧ 10 < p ∧ p < 20) /\
      (∃ p, BasicPrime p ∧ 20 < p ∧ p < 40) /\
      (∃ p, BasicPrime p ∧ 30 < p ∧ p < 60) /\
      (∃ p, BasicPrime p ∧ 40 < p ∧ p < 80) /\
      (∃ p, BasicPrime p ∧ 50 < p ∧ p < 100) := by
  exact ⟨bertrand_stage10, bertrand_stage20, bertrand_stage30,
    bertrand_stage40, bertrand_stage50⟩

theorem bertrand_extended_finite_certificate :
    (∃ p, BasicPrime p ∧ 10 < p ∧ p < 20) /\
      (∃ p, BasicPrime p ∧ 20 < p ∧ p < 40) /\
      (∃ p, BasicPrime p ∧ 30 < p ∧ p < 60) /\
      (∃ p, BasicPrime p ∧ 40 < p ∧ p < 80) /\
      (∃ p, BasicPrime p ∧ 50 < p ∧ p < 100) /\
      (∃ p, BasicPrime p ∧ 60 < p ∧ p < 120) := by
  exact ⟨bertrand_stage10, bertrand_stage20, bertrand_stage30,
    bertrand_stage40, bertrand_stage50, bertrand_stage60⟩

theorem bertrand_further_finite_certificate :
    (∃ p, BasicPrime p ∧ 70 < p ∧ p < 140) /\
      (∃ p, BasicPrime p ∧ 80 < p ∧ p < 160) /\
      (∃ p, BasicPrime p ∧ 100 < p ∧ p < 200) := by
  exact ⟨bertrand_stage70, bertrand_stage80, bertrand_stage100⟩

end ComputableAnalysis
