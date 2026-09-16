import ComputableAnalysis.BetaData

/-! Common finite recurrence contract, shared endpoint algebra and factorial
interpretation. The two analytic routes instantiate these laws independently. -/
namespace ComputableAnalysis.BetaIntegral
open ClosedArctanInverse RationalSampleLimits IntervalSelections

def stepResidual (m n q : Nat) : Rat :=
  ((m+n+2:Nat):Rat)*sample m (n+1) q-((n+1:Nat):Rat)*sample m n q

structure Laws : Prop where
  base : ∀ m, Close (fun q=>((m+1:Nat):Rat)*sample m 0 q) (fun _=>1)
  step : ∀ m n, Small (stepResidual m n)

theorem evaluation_samples (h : Laws) (m : Nat) : (n : Nat) →
    Close (sample m n) (fun _=>value m n)
  | 0 => by
    have hp : 0<((m+1:Nat):Rat) := (Rat.natCast_pos).2 (by omega)
    have hc:=Rat.mul_inv_cancel ((m+1:Nat):Rat) (Rat.ne_of_gt hp)
    have ht:=close_scale (1/((m+1:Nat):Rat)) (h.base m)
    have he : (fun q=>(1/((m+1:Nat):Rat))*(((m+1:Nat):Rat)*sample m 0 q))=sample m 0 := by
      funext q;simp only [Rat.div_def,Rat.one_mul];grind only
    rw [he] at ht
    simpa only [Rat.mul_one,value] using ht
  | n+1 => by
    let r : Rat:=((n+1:Nat):Rat)/((m+n+2:Nat):Rat)
    have hp : 0<((m+n+2:Nat):Rat) := (Rat.natCast_pos).2 (by omega)
    have hc:=Rat.mul_inv_cancel ((m+n+2:Nat):Rat) (Rat.ne_of_gt hp)
    have hs:=small_bounded_mul (qabs_nonneg (1/((m+n+2:Nat):Rat)))
      (bounded_const (1/((m+n+2:Nat):Rat))) (h.step m n)
    have he : (fun q=>(1/((m+n+2:Nat):Rat))*stepResidual m n q)=
        (fun q=>sample m (n+1) q-r*sample m n q) := by
      funext q;unfold stepResidual r;simp only [Rat.div_def,Rat.one_mul];grind only
    rw [he] at hs
    exact close_trans hs (close_scale r (evaluation_samples h m n))

theorem evaluation_of_laws (h : Laws) (m n : Nat) : Statement m n :=
  equiv_of_close (integral_valid m n) (RealRaw.ofRat_valid (value m n))
    (sample m n) (fun _=>value m n) (sample_mem m n) (ClockTrigonometry.rat_mem _)
    (evaluation_samples h m n)

/-- Integral evaluation in its conventional factorial form, with no division
by a computed quantity. This is a second statement in the SAME theorem family. -/
def FactorialStatement (m n : Nat) : Prop :=
  (RealRaw.scaleRat (factorial (m+n+1):Rat) (integral m n)).Equiv
    (RealRaw.ofRat ((factorial m:Rat)*(factorial n:Rat)))

theorem factorial_of_laws (h : Laws) (m n : Nat) : FactorialStatement m n := by
  have hp : 0≤(factorial (m+n+1):Rat) := Rat.natCast_nonneg
  apply equiv_of_close (RealRaw.scaleRat_valid (integral_valid m n)) (RealRaw.ofRat_valid _)
    (fun q=>(factorial (m+n+1):Rat)*sample m n q)
    (fun _=>(factorial m:Rat)*(factorial n:Rat))
    (fun q=>scale_mem (sample_mem m n q) hp) (ClockTrigonometry.rat_mem _)
  have ht:=close_scale (factorial (m+n+1):Rat) (evaluation_samples h m n)
  simpa only [factorial_value] using ht

end ComputableAnalysis.BetaIntegral
