import ComputableAnalysis.RiemannHilbert.GeometricSeries
import ComputableAnalysis.RiemannHilbert.SeriesRemainder

/-! Quantitative bounds for the omitted region of finite products. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarSeries
open ComplexRaw FunctionTheory LocalODE

def missing (t u : Nat → ComplexRaw) (N : Nat) : ComplexRaw :=
  block (fun i => mul (t i) (block u (N-i) i)) 0 N

theorem missing_valid (t u : Nat → ComplexRaw)
    (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid) (N : Nat) : (missing t u N).Valid :=
  block_valid _ (fun i => mul_valid (ht i) (block_valid u hu (N-i) i)) 0 N

theorem missing_image (t u : Nat → ComplexRaw)
    (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (missing t u N) (missing_valid t u ht hu N) =
      FiniteProducts.missing (fun i => ComplexRawQuotient.ofRaw (t i) (ht i))
        (fun i => ComplexRawQuotient.ofRaw (u i) (hu i)) N := by
  change ComplexRawQuotient.ofRaw (block (fun i => mul (t i) (block u (N-i) i)) 0 N)
    (block_valid _ (fun i => mul_valid (ht i) (block_valid u hu (N-i) i)) 0 N) = _
  rw [prefix_image]
  apply FiniteProducts.prefix_congr
  intro i hi
  change ComplexRawQuotient.ofRaw (t i) (ht i) *
    ComplexRawQuotient.ofRaw (block u (N-i) i) (block_valid u hu (N-i) i) = _
  rw [block_image u hu (N-i) i]

theorem missing_bound (t u : Nat → ComplexRaw)
    (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid) (M C q : Rat)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (htB : ∀ i, Small (t i) (2*M*q^i)) (huB : ∀ i, Small (u i) (2*C*q^i)) (N : Nat) :
    Small (missing t u N) (32*M*C*(4*q)^N) := by
  have hB : 0 ≤ 16*M*C*q^N :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC) (Rat.pow_nonneg hq)
  have hs : Small (missing t u N) ((N : Rat)*(16*M*C*q^N)) := by
    apply block_uniform _ (16*M*C*q^N) hB 0 N
    intro i hi
    simp only [Nat.zero_add]
    have hp := Small.mul (ht i) (block_valid u hu (N-i) i)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (Rat.pow_nonneg hq))
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq))
      (htB i) (block_bound u C q hC hq hlocal huB (N-i) i)
    have he : q^i*q^(N-i)=q^N := by
      rw [← rational_pow_add]
      congr 1
      omega
    have he2 : 2*(2*M*q^i)*(4*C*q^(N-i))=16*M*C*q^N := by
      have hc : 2*(2*M*q^i)*(4*C*q^(N-i))=(16*M*C)*(q^i*q^(N-i)) := by grind
      rw [hc, he]
    rw [he2] at hp
    exact hp
  apply hs.mono
  have hN : N ≤ (N+2)*(N+1) := by
    calc
      N ≤ N+2 := by omega
      _ ≤ (N+2)*(N+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hindex : (N : Rat) ≤ 2*(4 : Rat)^N := by
    rw [← cast_four_pow]
    exact_mod_cast Nat.le_trans hN (quadratic_index_bound N)
  have hle := Rat.mul_le_mul_of_nonneg_right hindex hB
  rw [rational_mul_pow]
  grind

end ComputableAnalysis.RiemannHilbert.ScalarSeries
