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

theorem subsetCount_stage10 :
    FiniteCounting.subsetCount 10 = 1024 := by
  native_decide

theorem subsetCount_stage10_pow :
    FiniteCounting.subsetCount 10 = 2 ^ 10 := by
  exact FiniteCounting.subsetCount_eq_pow 10

theorem subsetCount_stage10_certificate :
    FiniteCounting.subsetCount 10 = 2 ^ 10 /\
      FiniteCounting.subsetCount 10 = 1024 := by
  exact ⟨subsetCount_stage10_pow, subsetCount_stage10⟩

theorem subsetCount_stage12 :
    FiniteCounting.subsetCount 12 = 4096 := by
  native_decide

theorem subsetCount_stage12_pow :
    FiniteCounting.subsetCount 12 = 2 ^ 12 := by
  exact FiniteCounting.subsetCount_eq_pow 12

theorem subsetCount_stage12_certificate :
    FiniteCounting.subsetCount 12 = 2 ^ 12 /\
      FiniteCounting.subsetCount 12 = 4096 := by
  exact ⟨subsetCount_stage12_pow, subsetCount_stage12⟩

theorem subsetCount_stage16 :
    FiniteCounting.subsetCount 16 = 65536 := by
  native_decide

theorem subsetCount_stage16_pow :
    FiniteCounting.subsetCount 16 = 2 ^ 16 := by
  exact FiniteCounting.subsetCount_eq_pow 16

theorem subsetCount_stage16_certificate :
    FiniteCounting.subsetCount 16 = 2 ^ 16 /\
      FiniteCounting.subsetCount 16 = 65536 := by
  exact ⟨subsetCount_stage16_pow, subsetCount_stage16⟩

theorem subsetCount_stage20 :
    FiniteCounting.subsetCount 20 = 1048576 := by
  native_decide

theorem subsetCount_stage20_pow :
    FiniteCounting.subsetCount 20 = 2 ^ 20 := by
  exact FiniteCounting.subsetCount_eq_pow 20

theorem subsetCount_stage20_certificate :
    FiniteCounting.subsetCount 20 = 2 ^ 20 /\
      FiniteCounting.subsetCount 20 = 1048576 := by
  exact ⟨subsetCount_stage20_pow, subsetCount_stage20⟩

theorem subsetCount_stage32 :
    FiniteCounting.subsetCount 32 = 4294967296 := by
  native_decide

theorem subsetCount_stage32_pow :
    FiniteCounting.subsetCount 32 = 2 ^ 32 := by
  exact FiniteCounting.subsetCount_eq_pow 32

theorem subsetCount_stage32_certificate :
    FiniteCounting.subsetCount 32 = 2 ^ 32 /\
      FiniteCounting.subsetCount 32 = 4294967296 := by
  exact ⟨subsetCount_stage32_pow, subsetCount_stage32⟩

theorem subsetCount_stage64 :
    FiniteCounting.subsetCount 64 = 18446744073709551616 := by
  native_decide

theorem subsetCount_stage64_pow :
    FiniteCounting.subsetCount 64 = 2 ^ 64 := by
  exact FiniteCounting.subsetCount_eq_pow 64

theorem subsetCount_stage64_certificate :
    FiniteCounting.subsetCount 64 = 2 ^ 64 /\
      FiniteCounting.subsetCount 64 = 18446744073709551616 := by
  exact ⟨subsetCount_stage64_pow, subsetCount_stage64⟩

end ComputableAnalysis
