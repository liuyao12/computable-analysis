import ComputableAnalysis.Basic

/-!
# A worked finite subset-count certificate

The recursive subset counter is evaluated at a concrete stage.  This keeps
the benchmark's counting statement in the project's finite recurrence style,
without introducing a general finite-set cardinality library.
-/

namespace ComputableAnalysis

theorem subsetCount_stage8 :
    FiniteCounting.subsetCount 8 = 256 := by
  native_decide

theorem subsetCount_stage8_pow :
    FiniteCounting.subsetCount 8 = 2 ^ 8 := by
  exact FiniteCounting.subsetCount_eq_pow 8

theorem subsetCount_stage8_certificate :
    FiniteCounting.subsetCount 8 = 2 ^ 8 ∧
      FiniteCounting.subsetCount 8 = 256 := by
  exact ⟨subsetCount_stage8_pow, subsetCount_stage8⟩

end ComputableAnalysis
