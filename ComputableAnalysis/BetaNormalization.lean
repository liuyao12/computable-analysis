import ComputableAnalysis.BetaLaws

/-! Polynomial beta densities integrate to one. The normalizing coefficient
is a finite rational recurrence, never the reciprocal of a computed integral. -/
namespace ComputableAnalysis.BetaIntegral
open RationalSampleLimits IntervalSelections

theorem value_pos (m : Nat) : (n : Nat) → 0<value m n
  | 0 => by
    rw [value,Rat.div_def,Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (by omega))
  | n+1 => by
    rw [value,Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos ((Rat.natCast_pos).2 (by omega))
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (by omega)))) (value_pos m n)

def normalizer (m n : Nat) : Rat := 1/value m n

theorem normalizer_pos (m n : Nat) : 0<normalizer m n := by
  rw [normalizer,Rat.div_def,Rat.one_mul];exact (Rat.inv_pos).2 (value_pos m n)


/-- The rational normalizer has the standard factorial interpretation. -/
theorem normalizer_factorial (m n : Nat) :
    ((factorial m:Rat)*(factorial n:Rat))*normalizer m n=(factorial (m+n+1):Rat) := by
  have hv:=factorial_value m n
  have hc:=Rat.mul_inv_cancel (value m n) (Rat.ne_of_gt (value_pos m n))
  unfold normalizer
  simp only [Rat.div_def,Rat.one_mul]
  grind only

def NormalizationStatement (m n : Nat) : Prop :=
  (RealRaw.scaleRat (normalizer m n) (integral m n)).Equiv RealRaw.one

theorem normalization_of_laws (h : Laws) (m n : Nat) : NormalizationStatement m n := by
  have hc:=Rat.mul_inv_cancel (value m n) (Rat.ne_of_gt (value_pos m n))
  have he : normalizer m n*value m n=1 := by
    unfold normalizer;simp only [Rat.div_def,Rat.one_mul];grind only
  apply equiv_of_close (RealRaw.scaleRat_valid (integral_valid m n)) (RealRaw.ofRat_valid 1)
    (fun q=>normalizer m n*sample m n q) (fun _=>1)
    (fun q=>scale_mem (sample_mem m n q) (Rat.le_of_lt (normalizer_pos m n))) (ClockTrigonometry.rat_mem 1)
  have ht:=close_scale (normalizer m n) (evaluation_samples h m n)
  simpa only [he] using ht

end ComputableAnalysis.BetaIntegral
