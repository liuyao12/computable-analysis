import ComputableAnalysis.WallisArithmetic
import ComputableAnalysis.WallisLaws

/-! Standard factorial evaluations of both parity subsequences, for the same
independently computed cosine-power integrals. Shared finite arithmetic only
transforms the endpoint; the caller must supply the proved analytic laws. -/
namespace ComputableAnalysis.Wallis
open CartwrightMoments RationalSampleLimits IntervalSelections

def FactorialStatement (n : Nat) : Prop :=
  (RealRaw.scaleRat ((4:Rat)^n*(factorial n:Rat)*(factorial n:Rat)) (integral (2*n))).Equiv
    (RealRaw.ofRat (factorial (2*n):Rat)) ∧
  (RealRaw.scaleRat (factorial (2*n+1):Rat) (RealRaw.mul frequency (integral (2*n+1)))).Equiv
    (RealRaw.ofRat ((4:Rat)^n*(factorial n:Rat)*(factorial n:Rat)))

theorem factorials_of_laws (h : Laws) (n : Nat) : FactorialStatement n := by
  have he:=(evaluation_samples h (2*n))
  have ho:=(evaluation_samples h (2*n+1))
  have e:(2*n)%2=0:=by omega
  have o:¬(2*n+1)%2=0:=by omega
  simp [paritySample,e] at he
  simp only [paritySample,if_neg o] at ho
  have hc : 0≤(4:Rat)^n*(factorial n:Rat)*(factorial n:Rat) := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (FiniteRationalPowers.pow_nonneg (by decide) n) Rat.natCast_nonneg) Rat.natCast_nonneg
  constructor
  · apply equiv_of_close (RealRaw.scaleRat_valid (integral_valid (2*n))) (RealRaw.ofRat_valid _)
      (fun q=>((4:Rat)^n*(factorial n:Rat)*(factorial n:Rat))*integralSample (2*n) q)
      (fun _=>(factorial (2*n):Rat))
      (fun q=>scale_mem (integral_mem _ q) hc) (ClockTrigonometry.rat_mem _)
    have ht:=close_scale ((4:Rat)^n*(factorial n:Rat)*(factorial n:Rat)) he
    simpa only [coefficient_even] using ht
  · apply equiv_of_close (RealRaw.scaleRat_valid (RealRaw.mul_valid frequency_valid (integral_valid (2*n+1))))
      (RealRaw.ofRat_valid _)
      (fun q=>(factorial (2*n+1):Rat)*(frequencySample q*integralSample (2*n+1) q))
      (fun _=>(4:Rat)^n*(factorial n:Rat)*(factorial n:Rat))
      (fun q=>scale_mem (mul_mem (frequencySample_mem q) (integral_mem _ q)) Rat.natCast_nonneg)
      (ClockTrigonometry.rat_mem _)
    have ht:=close_scale (factorial (2*n+1):Rat) ho
    simpa only [coefficient_odd] using ht

end ComputableAnalysis.Wallis
