import ComputableAnalysis.Logarithm

namespace ComputableAnalysis

/-! A concrete finite witness for harmonic-series growth (benchmark item 34). -/

theorem harmonicSum_stage8_exact :
    Logarithm.harmonicSum 8 = 761 / 280 := by
  native_decide

theorem harmonicSum_stage8_exceeds_two :
    (2 : Rat) <= Logarithm.harmonicSum 8 := by
  rw [harmonicSum_stage8_exact]
  native_decide

theorem harmonicSum_stage8_certificate :
    Logarithm.harmonicSum 8 = 761 / 280 /\
      (2 : Rat) <= Logarithm.harmonicSum 8 := by
  exact ⟨harmonicSum_stage8_exact, harmonicSum_stage8_exceeds_two⟩

theorem harmonicSum_stage16_exact :
    Logarithm.harmonicSum 16 = 2436559 / 720720 := by
  native_decide

theorem harmonicSum_stage16_exceeds_two :
    (2 : Rat) <= Logarithm.harmonicSum 16 := by
  rw [harmonicSum_stage16_exact]
  native_decide

theorem harmonicSum_stage16_certificate :
    Logarithm.harmonicSum 16 = 2436559 / 720720 /\
      (2 : Rat) <= Logarithm.harmonicSum 16 := by
  exact ⟨harmonicSum_stage16_exact, harmonicSum_stage16_exceeds_two⟩

theorem harmonicSum_stage32_exact :
    Logarithm.harmonicSum 32 = 586061125622639 / 144403552893600 := by
  native_decide

theorem harmonicSum_stage32_exceeds_two :
    (2 : Rat) <= Logarithm.harmonicSum 32 := by
  rw [harmonicSum_stage32_exact]
  native_decide

theorem harmonicSum_stage32_certificate :
    Logarithm.harmonicSum 32 = 586061125622639 / 144403552893600 /\
      (2 : Rat) <= Logarithm.harmonicSum 32 := by
  exact ⟨harmonicSum_stage32_exact, harmonicSum_stage32_exceeds_two⟩

theorem harmonicSum_stage64_exact :
    Logarithm.harmonicSum 64 =
      623171679694215690971693339 / 131362987122535807501262400 := by
  native_decide

theorem harmonicSum_stage64_exceeds_three :
    (3 : Rat) <= Logarithm.harmonicSum 64 := by
  rw [harmonicSum_stage64_exact]
  native_decide

theorem harmonicSum_stage64_certificate :
    Logarithm.harmonicSum 64 =
        623171679694215690971693339 / 131362987122535807501262400 /\
      (3 : Rat) <= Logarithm.harmonicSum 64 := by
  exact ⟨harmonicSum_stage64_exact, harmonicSum_stage64_exceeds_three⟩

theorem harmonicSum_stage64_reaches_three :
    (3 : Rat) <= Logarithm.harmonicSum 64 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 3

theorem harmonicSum_stage256_reaches_four :
    (4 : Rat) <= Logarithm.harmonicSum 256 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 4

theorem harmonicSum_stage1024_reaches_five :
    (5 : Rat) <= Logarithm.harmonicSum 1024 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 5

theorem harmonicSum_stage4096_reaches_six :
    (6 : Rat) <= Logarithm.harmonicSum 4096 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 6

set_option maxRecDepth 10000 in
theorem harmonicSum_stage16384_reaches_seven :
    (7 : Rat) <= Logarithm.harmonicSum 16384 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 7

set_option maxRecDepth 40000 in
theorem harmonicSum_stage65536_reaches_eight :
    (8 : Rat) <= Logarithm.harmonicSum 65536 := by
  simpa using Logarithm.harmonicSum_two_pow_reaches 8

end ComputableAnalysis
